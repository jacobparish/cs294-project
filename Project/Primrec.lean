module

public import Mathlib.Computability.Primrec.List
public import Project.List

/-!
### Helper primrec lemmas

The lemmas in this file are standard facts that are not (yet) in Mathlib:
primitive recursiveness of `List.takeI`, `List.product`, and `List.find?`.
-/

@[expose] public section

namespace Primrec

lemma list_takeI {α : Type*} [Inhabited α] [Primcodable α] :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.takeI n) := by
  -- Use the equivalent formulation: `l.takeI n = (List.range n).map (fun i => l.getI i)`.
  have h : Primrec (fun (p : List α × ℕ) => (List.range p.2).map (fun i => p.1.getI i)) := by
    apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    exact Primrec.list_getI.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  refine h.to₂.of_eq fun l n => ?_
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.takeI_length]
  · intro i _ hi
    rw [List.getElem_map, List.getElem_range]
    rw [List.takeI_length] at hi
    rw [← List.getI_eq_getElem _ (by rw [List.takeI_length]; exact hi)]
    exact (List.getI_takeI l n i hi).symm

lemma list_product {α β : Type*} [Primcodable α] [Primcodable β] :
    Primrec₂ (List.product : List α → List β → List (α × β)) := by
  -- `List.product l₁ l₂ = l₁.flatMap (fun a => l₂.map (Prod.mk a))`.
  refine Primrec.list_flatMap .fst ?_
  refine Primrec.list_map (.comp .snd .fst) ?_
  exact Primrec.pair (.comp .snd .fst) .snd

lemma list_find? {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).find? (p a)) := by
  -- Use the equivalence `l.find? p = l[l.findIdx p]?`.
  have h_idx : Primrec (fun a => (f a).findIdx (p a)) := Primrec.list_findIdx hf hp
  have h_get : Primrec (fun a => (f a)[(f a).findIdx (p a)]?) :=
    Primrec.list_getElem?.comp hf h_idx
  refine h_get.of_eq fun a => ?_
  -- Show: (f a)[(f a).findIdx (p a)]? = (f a).find? (p a)
  generalize (f a) = l
  generalize (p a) = q
  clear hf hp h_idx h_get f p
  induction l with
  | nil => rfl
  | cons b t IH =>
    by_cases hb : q b
    · simp [List.findIdx_cons, hb]
    · simp [List.findIdx_cons, hb]
      exact IH

end Primrec
