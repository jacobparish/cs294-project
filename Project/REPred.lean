module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode

namespace REPred

open Nat.Partrec

/--
If `p` is a nonempty RE predicate, then `p` is the range of a primitive recursive function.
-/
theorem Nat.range_primrec_of_re {p : ℕ → Prop} (hp : REPred p) {n₀ : ℕ} (hn₀ : p n₀) : ∃ f : ℕ → ℕ, Nat.Primrec f ∧ Set.range f = p := by
  simp only [REPred, Partrec, Encodable.decode, Part.coe_some, Encodable.encode, Part.bind_some,
    Code.exists_code] at hp
  obtain ⟨c, hc⟩ := hp
  -- The primitive recursive function whose range equals the domain of `f` is the function `g` defined as follows. On input `(k, m)`, `g` checks if `c.evaln k m` is defined. If it is, it outputs `m`, and if it is not, it outputs `n₀`.
  use Nat.unpaired fun k m => if (c.evaln k m).isSome then m else n₀
  constructor
  · refine Primrec.nat_iff.mp <| Primrec.ite ?_ ?_ ?_
    · simp only [PrimrecPred, Bool.decide_eq_true, exists_const]
      exact Primrec.option_isSome.comp <|
        Code.primrec_evaln.comp <|
          .pair (.pair .fst (.const c)) .snd
    · exact Primrec.nat_iff.mpr Nat.Primrec.right
    · exact Primrec.const n₀
  · sorry

/--
The range of a partial recursive function `ℕ →. ℕ` is RE.
-/
theorem Nat.re_range_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : REPred fun b => ∃ a, b ∈ f a := by
  rw [Code.exists_code] at hf
  obtain ⟨c, hc⟩ := hf
  -- The partial recursive function whose domain equals the range of `f` is the function `g` which, given input `n`, searches for a pair `(k, m)` such that `c.evaln k m = some n`.
  have hg : Partrec fun n => (Nat.rfind <| Nat.unpaired fun k m => decide (c.evaln k m = .some n)).map fun _ => () := by
    refine Partrec.map ?_ (Computable.const ())
    refine Partrec.rfind (?_ : Primrec _).to_comp.partrec
    obtain ⟨_, h⟩ := Primrec.eq (α := Option ℕ)
    convert h.comp (Primrec.pair ?_ ?_)
    · refine (?_ : Primrec fun x : ℕ => Code.evaln x.unpair.1 c x.unpair.2).comp .snd
      exact Code.primrec_evaln.comp <| .pair (.pair .fst (.const c)) .snd
    · exact Primrec.option_some.comp .fst
  unfold REPred
  convert hg with b
  ext u
  have hp (p : ℕ → ℕ → Prop) : (∃ x y, p y x) ↔ ∃ n : ℕ, p n.unpair.1 n.unpair.2 :=
    ⟨fun ⟨a, b, h⟩ => ⟨Nat.pair b a, by simpa⟩, fun ⟨n, hn⟩ => ⟨n.unpair.2, n.unpair.1, hn⟩⟩
  simp [← hc, Code.evaln_complete, ← Part.dom_iff_mem, hp, -Nat.mem_rfind]

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
