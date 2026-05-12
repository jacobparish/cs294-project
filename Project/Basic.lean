module

public import Mathlib.Data.PFun

@[expose] public section

/--
Convert a decidable predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [DecidablePred p] : α → ℕ :=
  fun a => (decide (p a)).toNat

/--
Convert a decidable relation `α → β → Prop` into an indicator function `α → β → ℕ`.
-/
def ofRel {α β} (r : α → β → Prop) [DecidableRel r] : α → β → ℕ :=
  fun a b => (decide (r a b)).toNat

namespace PFun

@[simp]
lemma dom_restrict {α β} (f : α →. β) {p} (hp : p ⊆ f.Dom) : (PFun.restrict f hp).Dom = p := rfl

@[simp]
lemma dom_res {α β} (f : α → β) (s : Set α) : (PFun.res f s).Dom = s := rfl

end PFun

end
