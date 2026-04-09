module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.PartrecCode

namespace REPred

open Nat.Partrec

/--
If `p : ℕ → Prop` is a nonempty RE predicate, then `p` is the range of a primitive recursive function `ℕ → ℕ`.
-/
theorem Nat.range_primrec_of_re {p : ℕ → Prop} (hp : REPred p) {n₀ : ℕ} (hn₀ : p n₀) : ∃ f : ℕ → ℕ, Nat.Primrec f ∧ (· ∈ Set.range f) = p := by
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
  · ext m
    constructor
    · rintro ⟨n, rfl⟩
      simp only [Nat.unpaired]
      rcases h : c.evaln n.unpair.1 n.unpair.2 with - | y
      · simpa
      apply Code.evaln_sound at h
      simp [hc] at h
      tauto
    · intro (hm : p m)
      have h := congr_fun hc m
      simp only [Part.assert_pos hm, Part.map_some, Part.eq_some_iff] at h
      obtain ⟨k, hk⟩ := Code.evaln_complete.mp h
      use Nat.pair k m
      simp [Option.mem_def.mp hk]

/--
If `p : α → Prop` is a nonempty RE predicate, then `p` is the range of a primitive recursive function `ℕ → α`.
-/
theorem range_primrec_of_re {α} [Primcodable α] {p : α → Prop} (hp : REPred p) {a₀ : α} (ha₀ : p a₀) : ∃ f : ℕ → α, Primrec f ∧ (· ∈ Set.range f) = p := by
  sorry

/--
If `p : α → Prop` is a nonempty RE predicate, then `p` is the range of a computable function `ℕ → α`.
-/
theorem range_computable_of_re {α} [Primcodable α] {p : α → Prop} (hp : REPred p) {a₀ : α} (ha₀ : p a₀) : ∃ f : ℕ → α, Computable f ∧ (· ∈ Set.range f) = p := by
  obtain ⟨f, hf, rfl⟩ := range_primrec_of_re hp ha₀
  exact ⟨f, hf.to_comp, rfl⟩

/--
If `p : α → Prop` is a (possibly empty) RE predicate, then `p` is the range of a partial recursive function `ℕ →. α`.
-/
theorem range_partrec_of_re {α} [Primcodable α] {p : α → Prop} (hp : REPred p) : ∃ f : ℕ →. α, Partrec f ∧ (· ∈ PFun.ran f) = p := by
  by_cases! h : ∃ a, p a
  · obtain ⟨a₀, ha₀⟩ := h
    obtain ⟨f, hf, rfl⟩ := range_computable_of_re hp ha₀
    refine ⟨f, hf.partrec, ?_⟩
    simp [PFun.ran]
    grind
  · use fun _ => Part.none, Partrec.none
    funext a
    simp [PFun.ran, h]

/--
The range of a partial recursive function `ℕ →. ℕ` is RE.
-/
theorem Nat.re_range_partrec {f : ℕ →. ℕ} (hf : Nat.Partrec f) : REPred (· ∈ PFun.ran f) := by
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
  simp [← hc, PFun.ran, Code.evaln_complete, ← Part.dom_iff_mem, hp, -Nat.mem_rfind]

/--
The range of a partial recursive function `ℕ →. α` is RE.
-/
theorem re_range_partrec {α β} [Primcodable α] [Primcodable β] {f : α →. β} (hf : Partrec f) : REPred (· ∈ PFun.ran f) := by
  sorry

/--
The range of a computable function `ℕ → α` is RE.
-/
theorem re_range_computable {α β} [Primcodable α] [Primcodable β] {f : α → β} (hf : Computable f) : REPred (· ∈ Set.range f) := by
  convert re_range_partrec hf.partrec with b
  simp [Set.range, PFun.ran]
  grind

/--
The range of a primitive recursive function `ℕ → α` is RE.
-/
theorem re_range_primrec {α β} [Primcodable α] [Primcodable β] {f : α → β} (hf : Primrec f) : REPred (· ∈ Set.range f) :=
  re_range_computable hf.to_comp

/--
A predicate `p : α → Prop` is RE iff `p` is empty or `p` is the range of a primitive recursive function.
-/
theorem re_iff_range_primrec {α} [Primcodable α] (p : α → Prop) : REPred p ↔ (∀ a, ¬ p a) ∨ ∃ f : ℕ → α, Primrec f ∧ (· ∈ Set.range f) = p := by
  constructor
  · simp only [Set.mem_range, or_iff_not_imp_left, not_forall, not_not, forall_exists_index]
    exact range_primrec_of_re
  · rintro (hp | ⟨f, hf, rfl⟩)
    · simp [REPred, Part.assert_neg (hp _), Partrec.none]
    · exact re_range_primrec hf

/--
A predicate `p : α → Prop` is RE iff `p` is empty or `p` is the range of a total computable function.
-/
theorem re_iff_range_computable {α} [Primcodable α] (p : α → Prop) : REPred p ↔ (∀ a, ¬ p a) ∨ ∃ f : ℕ → α, Computable f ∧ (· ∈ Set.range f) = p := by
  constructor
  · simp only [Set.mem_range, or_iff_not_imp_left, not_forall, not_not, forall_exists_index]
    exact range_computable_of_re
  · rintro (hp | ⟨f, hf, rfl⟩)
    · simp [REPred, Part.assert_neg (hp _), Partrec.none]
    · exact re_range_computable hf

/--
A predicate `p : α → Prop` is RE iff `p` is the range of a partial recursive function.
-/
theorem re_iff_range_partrec {α} [Primcodable α] (p : α → Prop) : REPred p ↔ ∃ f : ℕ →. α, Partrec f ∧ (· ∈ PFun.ran f) = p := by
  constructor
  · exact range_partrec_of_re
  · rintro ⟨f, hf, rfl⟩
    exact re_range_partrec hf

end REPred
