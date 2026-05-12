module

public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.List.Lemmas

@[expose] public section

namespace List

variable {α β : Type*}

/--
Given a function `f : ℕ → α`, extract the first `k` values into a list.
-/
def ofFnNat (f : ℕ → α) (k : ℕ) : List α := map f (range k)

@[simp]
lemma ofFnNat_eq_iff {f g : ℕ → α} {k : ℕ} : ofFnNat f k = ofFnNat g k ↔ ∀ i < k, f i = g i := by
  simp [ofFnNat]

@[simp]
lemma length_ofFnNat (f : ℕ → α) (k : ℕ) : length (ofFnNat f k) = k := by
  simp [ofFnNat]

@[simp]
lemma getElem_ofFnNat {f : ℕ → α} {k i : ℕ} (h : i < (ofFnNat f k).length) : (ofFnNat f k)[i] = f i := by
  simp [ofFnNat]

@[simp]
lemma getElem?_ofFnNat (f : ℕ → α) (k i : ℕ) : (ofFnNat f k)[i]? = if i < k then some (f i) else none := by
  by_cases h : i < k <;> simp [ofFnNat, h]

@[simp]
lemma take_ofFnNat (f : ℕ → α) {k₁ k₂} (h : k₁ ≤ k₂) : take k₁ (ofFnNat f k₂) = ofFnNat f k₁ := by
  simpa [ext_get_iff]

@[simp]
lemma ofFnNat_prefix_iff (f₁ f₂ : ℕ → α) {k₁ k₂} : ofFnNat f₁ k₁ <+: ofFnNat f₂ k₂ ↔ k₁ ≤ k₂ ∧ ∀ i < k₁, f₁ i = f₂ i := by
  simp [prefix_iff_eq_take, ext_get_iff]
  grind

lemma prefix_iff_forall_getElem? {l₁ l₂ : List α}
    : l₁ <+: l₂ ↔ ∀ i : ℕ, ∀ a ∈ l₁[i]?, a ∈ l₂[i]? := by
  simp [prefix_iff_getElem?]
  grind

/--
If `i < n`, then `(l.takeI n).getI i = l.getI i`.
-/
@[simp]
lemma getI_takeI [Inhabited α] :
    ∀ (l : List α) (n i : ℕ), i < n → (l.takeI n).getI i = l.getI i
  | _, 0, _, hi => by omega
  | [], n+1, i, hi => by
    rw [List.takeI_nil, List.getI_nil]
    have hlen : i < (List.replicate (n+1) (default : α)).length := by
      rw [List.length_replicate]; exact hi
    rw [List.getI_eq_getElem _ hlen]
    simp
  | _::_, _+1, 0, _ => rfl
  | _::xs, n+1, i+1, hi => by
    show (_ :: xs.takeI n).getI (i+1) = _
    rw [List.getI_cons_succ, List.getI_cons_succ]
    exact List.getI_takeI xs n i (Nat.lt_of_succ_lt_succ hi)

@[simp]
lemma getI_append_takeI_right [Inhabited α] (l l' : List α) (n k : ℕ)
    : (l.takeI n ++ l').getI (n + k) = l'.getI k := by
  have h : ¬(n + k < n) := by omega
  simp [getI, getD, List.getElem?_append, h]

@[simp]
lemma getI_append_takeI_right_zero [Inhabited α] (l l' : List α) (n : ℕ)
    : (l.takeI n ++ l').getI n = l'.getI 0 :=
  getI_append_takeI_right l l' n 0

lemma getI_append_takeI_left [Inhabited α] (l l' : List α) {n k : ℕ} (h : k < n)
    : (l.takeI n ++ l').getI k = l.getI k := by
  rw [List.getI_append _ _ _ ?_] <;> simp [h]

/--
See also `range'_eq_cons_iff`.
-/
lemma cons_eq_range'_iff {a xs s n step} : a :: xs = range' s n step ↔ s = a ∧ 0 < n ∧ xs = range' (a + step) (n - 1) step := by
  grind [range'_eq_cons_iff]

lemma find?_product_range {a b : ℕ} {p : (ℕ × ℕ) → Bool} {i₀ j₀}
    : find? p ((range a) ×ˢ (range b)) = some (i₀, j₀)
    ↔ p (i₀, j₀) ∧ i₀ < a ∧ j₀ < b ∧ (∀ i < i₀, ∀ j < b, ¬ p (i, j)) ∧ (∀ j < j₀, ¬ p (i₀, j)) := by
  simp [SProd.sprod, product, find?_flatMap, findSome?_eq_some_iff, range_eq_range', range'_eq_append_iff, cons_eq_range'_iff]
  grind

end List

end
