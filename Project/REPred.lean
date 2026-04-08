module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode

namespace REPred

/--
The range of a partial recursive function `ℕ →. ℕ` is RE.
-/
theorem Nat.re_range_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : REPred fun b => ∃ a, b ∈ f a := by
  rw [Nat.Partrec.Code.exists_code] at hf
  obtain ⟨c, hc⟩ := hf
  -- The partial recursive function whose domain equals the range of `f` is the function `g` which, given input `n`, searches for a pair `(k, m)` such that `c.evaln k m = some n`.
  let g (n : ℕ) := (Nat.rfind <| Nat.unpaired fun k m => decide (c.evaln k m = .some n)).map fun _ => ()
  have hg : Partrec g := by
    refine Partrec.map ?_ (Computable.const ())
    refine Partrec.rfind (?_ : Primrec _).to_comp.partrec
    obtain ⟨_, h⟩ := Primrec.eq (α := Option ℕ)
    convert h.comp (Primrec.pair ?_ ?_)
    · refine (?_ : Primrec fun x : ℕ => Nat.Partrec.Code.evaln (Nat.unpair x).1 c (Nat.unpair x).2).comp Primrec.snd
      exact Nat.Partrec.Code.primrec_evaln.comp <| Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd
    · exact Primrec.option_some.comp Primrec.fst
  unfold REPred
  convert hg with b
  ext u
  simp only [Part.mem_assert_iff, Part.mem_some_iff, ← hc, Nat.Partrec.Code.evaln_complete,
    exists_prop, and_true, Part.coe_some, Part.mem_map_iff, ← Part.dom_iff_mem, Nat.rfind_dom,
    Nat.unpaired, Bool.true_eq, decide_eq_true_eq, Part.some_dom, implies_true, g]
  exact ⟨fun ⟨a, b, h⟩ => ⟨Nat.pair b a, by simpa⟩, fun ⟨n, hn⟩ => ⟨n.unpair.2, n.unpair.1, hn⟩⟩

/--
The range of a partial recursive function between `Primcodable` types is RE.
-/
theorem re_range_partrec {α β} [Primcodable α] [Primcodable β] {f : α →. β} (hf : Partrec f) : REPred fun b => ∃ a, b ∈ f a := by
  sorry

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
