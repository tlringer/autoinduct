# The `autoinduct` tactic

Steps:
1. `autoinduct on (f a b).` should run `induction` on the recursive argument of `f`, in this case either `a` or `b`.
   1. `f` unfolds to a `fix`, like `Nat.plus` does
   1. `f` unfolds to `fun ... => fix`, like `List.map does`
   1. `f` reduces (many steps) to the above
1. `autoinduct on f.` as above but the arguments on which `induction` is run are not given. The tactic has to inspect the goal and run `induction` on an actual term.

The tactic should be callable  from the `"Classic"` proof mode, AKA ltac1.

# Solutions

## Elpi

The [elpi/](elpi/) directory contains the code of a typical elpi tactic, and the file
[Tactic.v](elpi/theories/Tactic.v) the actual implementation of `autoinduct`.

<details>

<summary>expand</summary>

details specific to the Elpi code

</details>
