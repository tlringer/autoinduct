The `autoinduct` tactic
-----------------------

Steps:
1. `autoinduct on (f a b).` should run `induction` on the recursive argument of `f`, in this case either `a` or `b`.
   1. `f` unfolds to a `fix`, like `Nat.plus` does
   2. `f` unfolds to `fun ... => fix`, like `List.map does`
   3. `f` reduces (many steps) to the above
1. `autoinduct on f.` as above but the arguments on which `induction` is run are not given. The tactic has to inspect the goal and run `induction` on an actual term.
