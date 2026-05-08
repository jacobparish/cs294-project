module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.TakeDrop

/-!
# List Helper Lemmas.
-/

@[expose] public section

namespace List

/--
If `i < n`, then `(l.takeI n).getI i = l.getI i`.
-/
lemma getI_takeI {α : Type*} [Inhabited α] :
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

end List
