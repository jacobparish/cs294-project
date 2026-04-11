module

public import Mathlib.Computability.PartrecCode

/-!
This extends `Mathlib.Computability.PartrecCode` to add some additional lemmas about `Nat.Partrec.Code`. In particular, codes for several basic functions are defined, along with simp lemmas for their eval functions.
-/

@[expose] public section

namespace Nat.Partrec.Code
section

-- TODO: It may be better to create a type `Nat.Primrec.Code`, because then its eval function will be total and we won't have to deal with PFun.

/--
A code which evaluates to `Nat.pred`.
-/
def pred : Code := prec zero (left.comp right)

/--
A code which evaluates to `Nat.add`.
-/
protected def add : Code := prec Code.id ((succ.comp right).comp right)

/--
A code which evaluates to `Nat.sub`.
-/
protected def sub : Code := prec Code.id ((pred.comp right).comp right)

/--
A code which evaluates to the `swap` function.
-/
protected def swap : Code := pair right left

/--
Given codes `c`, `ctrue`, `cfalse`, `c.ite ctrue cfalse` evaluates to `if c.eval n > 0 then ctrue.eval n else cfalse.eval n`.
-/
protected def ite : Code → Code → Code → Code :=
  fun c ctrue cfalse =>
    (prec (cfalse.comp left) (ctrue.comp left)).comp (pair Code.id c)

/--
A code which evaluates to the `≤` relation.
-/
protected def le : Code := Code.ite Code.sub (Code.const 0) (Code.const 1)

/--
A code which evaluates to the minimum function.
-/
protected def min : Code := Code.ite Code.le left right

/--
A code which evaluates to the maximum function.
-/
protected def max : Code := Code.ite Code.le right left

/--
A code which evaluates to the equality function.
-/
protected def eq : Code := Code.min.comp <| pair Code.le (Code.le.comp Code.swap)

@[simp]
lemma eval_pred : eval Code.pred = Nat.pred := by
  funext n
  simp [Code.pred, eval]
  sorry

@[simp]
lemma eval_add : eval Code.add = Nat.unpaired Nat.add := by
  simp [Code.add, eval]
  sorry

@[simp]
lemma eval_sub : eval Code.sub = Nat.unpaired Nat.sub := by
  simp [Code.sub, eval]
  sorry

@[simp]
lemma eval_swap : eval Code.swap = Nat.unpaired (Function.swap Nat.pair) := by
  funext n
  simp [Code.swap, eval, Seq.seq]

@[simp]
lemma eval_ite {c ctrue cfalse : Code} {n} : eval (c.ite ctrue cfalse) n = (c.eval n).bind fun x => if x ≠ 0 then ctrue.eval n else cfalse.eval n := by
  simp [Code.ite, eval]
  sorry

@[simp]
lemma eval_le : eval Code.le = Nat.unpaired fun x y => (decide (x ≤ y)).toNat  := by
  funext n
  by_cases n.unpair.1 ≤ n.unpair.2 <;> simp [Code.le, Nat.sub_eq_zero_iff_le, *]

@[simp]
lemma eval_min : eval Code.min = Nat.unpaired Nat.min := by
  funext n
  simp [Code.min, eval]
  sorry

@[simp]
lemma eval_max : eval Code.max = Nat.unpaired Nat.max := by
  funext n
  simp [Code.max, eval]
  sorry

@[simp]
lemma eval_eq : eval Code.eq = Nat.unpaired fun x y => (decide (x = y)).toNat := by
  funext n
  simp [Code.eq, eval, Seq.seq]
  sorry

end

section

/--
From a list `l`, return a code whose `eval` is `fun n => n ∈ l`.
-/
def listMem : List ℕ → Code
  | .nil => Code.zero
  | .cons x xs => Code.max.comp <| pair (Code.eq.curry x) (listMem xs)

/--
`ofList l` evaluates to `fun n => l[n]?`.
-/
@[simp]
lemma eval_listMem (l : List ℕ) (n : ℕ) : eval (listMem l) n = (decide (n ∈ l)).toNat := by
  induction l with
  | nil => rfl
  | cons x xs IH =>
    simp only [listMem, eval, IH, Seq.seq]
    by_cases! h : x = n
    · simp [h, Bool.toNat_le]
    · simp [h, h.symm]

/--
`listMem` is primitive recursive.
-/
lemma primrec_listMem : Primrec listMem := by
  convert Primrec.list_rec .id (.const zero) (?_ : Primrec₂ fun _ (x, xs, IH) => Code.max.comp <| pair (Code.eq.curry x) IH) with l
  · induction l with simp [listMem, *]
  exact (primrec₂_comp.comp (.const _) .id).comp <|
    primrec₂_pair.comp (primrec₂_curry.comp (.const _) (.comp .fst .snd)) <|
      .comp .snd (.comp .snd .snd)

end
end Nat.Partrec.Code

end
