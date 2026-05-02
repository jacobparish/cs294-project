module

import Mathlib.Computability.Primrec.Basic

@[expose] public section

/--
Convert a decidable predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [DecidablePred p] : α → ℕ :=
  fun a => (decide (p a)).toNat

end
