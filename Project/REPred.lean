module

public import Mathlib.Computability.Halting

namespace REPred

/--
A predicate `p : α → Prop` is RE iff `p` is empty or `p` is the range of a total computable function.
-/
theorem re_iff_range_of_computable {α} [Primcodable α] (p : α → Prop) : REPred p ↔ (∀ a, ¬ p a) ∨ ∃ f : ℕ → α, Computable f ∧ Set.range f = p := by
  constructor
  · intro hp
    sorry
  · rintro (hp | ⟨f, hf, rfl⟩)
    · sorry
    sorry

end REPred
