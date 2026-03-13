import Mathlib.Computability.Halting
import Mathlib.Computability.TuringDegree

open Nat.Partrec

/-- The halting problem -/
def halts_on_zero : Code → Prop := fun c => (c.eval 0).Dom
