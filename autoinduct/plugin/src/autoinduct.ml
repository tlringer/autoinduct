module CMonad = Monad

open Proofview
open EConstr
open Environ

(* --- Useful higher-order functions --- *)
module State = struct
  module Self = struct
    type 'a t = Evd.evar_map -> Evd.evar_map * 'a

    let (>>=) f1 f2 = (fun sigma -> let sigma, a = f1 sigma in f2 a sigma)

    let (>>) f1 f2 = f1 >>= fun () -> f2

    let map f x = fun sigma -> let sigma, x = x sigma in sigma, f x

    let return a = fun sigma -> sigma, a
  end

  include CMonad.Make(Self)

  let get sigma = sigma, sigma

  let set sigma = fun sigma' -> sigma, ()
end
open State.Self

(* Stateful if/else *)
let branch_state p f g a =
  State.get >>= fun sigma_f ->
  p a >>= fun b ->
  if b then f a
  else begin
    State.set sigma_f >>= fun () ->
    g a
  end

(* fold_left2 with state *)
let fold_left2_state f acc l1 l2 =
  State.List.fold_left2 (fun _ -> failwith "not same length") f acc l1 l2

(* Like fold_left2_state, but over arrays *)
let fold_left2_state_array f c args1 args2 sigma =
  fold_left2_state f c (Array.to_list args1) (Array.to_list args2) sigma

(* Stateful forall2, from https://github.com/uwplse/coq-plugin-lib *)
let forall2_state_array p args1 args2 =
  fold_left2_state_array
    (fun b a1 a2 -> branch_state (p a1) (fun _ -> return b) (fun _ -> return false) a2)
    true
    args1
    args2

(* --- Useful Coq utilities, mostly from https://github.com/uwplse/coq-plugin-lib --- *)

(*
 * Look up a definition from an environment
 *)
let lookup_definition env def sigma =
  match kind sigma def with
  | Constr.Const (c, u) ->
    begin match constant_value_in env (c, EConstr.Unsafe.to_instance u) with
      | v -> EConstr.of_constr v
      | exception NotEvaluableConst _ ->
        CErrors.user_err (Pp.str "The supplied term is not a transparent constant.")
    end
  | _ -> CErrors.user_err (Pp.str "The supplied term is not a constant.")

(* Equal but convert to constr (maybe this exists already in the Coq API) *)
let eequal trm1 trm2 sigma =
  sigma, EConstr.eq_constr sigma trm1 trm2

(* Push a local binding to an environment *)
let push_local (n, t) env =
  EConstr.push_rel Context.Rel.Declaration.(LocalAssum (n, t)) env

(* --- Implementation --- *)

(*
 * Get the recursive argument index
 *)
let rec recursive_argument env f_body sigma =
  match kind sigma f_body with
  | Constr.Fix ((rec_indexes, i), _) -> Array.get rec_indexes i
  | Constr.Lambda (n, t, b) ->
     let env_b = push_local (n, t) env in
     1 + (recursive_argument env_b b sigma)
  | Constr.Const (c, u) ->
     recursive_argument env (lookup_definition env f_body sigma) sigma
  | _ ->
     CErrors.user_err (Pp.str "The supplied function is not a fixpoint")

(*
 * Inner implementation of autoinduct tactic
 * The current version does not go under binders.
 * It's Part 1 out of 3, so requires explicit arguments
 * It also does not have the most useful error messages
 * It also requires exact equality (rather than convertibility) for the function and all of its arguments
 * It also may not stop itself if the chosen argument is not inductive (have not tested yet; it may, actually)
 *)
let find_autoinduct env f f_args concl sigma =
  let rec aux under_binders (sigma,found as acc) concl =
    if under_binders then acc
    else
      let recurse (sigma, _ as acc) =
        EConstr.fold_with_binders sigma (fun _ -> true) aux under_binders acc concl
      in
      match kind sigma concl with
      | App (g, g_args) ->
        let sigma, f_eq = eequal f g sigma in
        if f_eq then
          let sigma, args_eq = forall2_state_array eequal f_args g_args sigma in
          if args_eq then
            let f_body = lookup_definition env f sigma in
            let arg_no = recursive_argument env f_body sigma in
            let arg = g_args.(arg_no) in
            recurse (sigma, arg :: found)
          else recurse acc
        else recurse acc
      | _ -> recurse acc
  in
  aux false (sigma,[]) concl

let one_autoinduct arg =
  let dest_arg = Some true, Tactics.ElimOnConstr (fun _env sigma -> sigma, (arg, Tactypes.NoBindings)) in
  Tactics.induction_destruct true false ([dest_arg, (None, None), None], None)

let do_autoinduct env concl f f_args sigma =
  let sigma, induct_args = find_autoinduct env f f_args concl sigma in
  if CList.is_empty induct_args
  then Tacticals.tclFAIL Pp.(str "Could not find anything to induct over.")
  else
    tclBIND (Proofview.Unsafe.tclEVARS sigma) begin fun () ->
      Tacticals.tclFIRST (List.map one_autoinduct induct_args)
    end

(*
 * Implementation of autoinduct tactic, top level
 *)
let autoinduct f f_args =
  Goal.enter begin fun gl ->
    let env = Goal.env gl in
    let sigma = Goal.sigma gl in
    let concl = Goal.concl gl in
    do_autoinduct env concl f f_args sigma 
  end

