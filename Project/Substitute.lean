module

public import Project.Queries
public import Mathlib.Computability.Halting

/-!
# Oracle Substitution.

## Main Definitions

* `RecursiveIn.Code.subst`:
* `RecursiveIn.Code.substPartrec`:

## Main Results

* `RecursiveIn.Code.primrec₂_subst`:
* `RecursiveIn.Code.primrec₂_substPartrec`:
* `RecursiveIn.Code.eval_subst`:
* `RecursiveIn.Code.eval_substPartrec`:
-/

@[expose] public section

namespace RecursiveIn.Code

/--
Substitute the oracle in a code `c` for another `RecursiveIn.Code` `c'`.
-/
def subst (c : Code) (c' : Code) : Code := match c with
| zero => zero
| succ => succ
| left => left
| right => right
| oracle => c'
| pair cf cg => pair (cf.subst c') (cg.subst c')
| comp cf cg => comp (cf.subst c') (cg.subst c')
| prec cf cg => prec (cf.subst c') (cg.subst c')
| rfind' cf => rfind' (cf.subst c')

/--
Substitute the oracle in a code `c` for a `Nat.Partrec.Code` `c'`.
-/
def substPartrec (c : Code) (c' : Nat.Partrec.Code) : Nat.Partrec.Code := match c with
| zero => .zero
| succ => .succ
| left => .left
| right => .right
| oracle => c'
| pair cf cg => .pair (cf.substPartrec c') (cg.substPartrec c')
| comp cf cg => .comp (cf.substPartrec c') (cg.substPartrec c')
| prec cf cg => .prec (cf.substPartrec c') (cg.substPartrec c')
| rfind' cf => .rfind' (cf.substPartrec c')

/--
`subst` is primitive recursive.
-/
theorem primrec₂_subst : Primrec₂ subst := by
  -- TODO: will need to use `primrec_recOn`.
  sorry

/--
`substPartrec` is primitive recursive.
-/
theorem primrec₂_substPartrec : Primrec₂ substPartrec := by
  -- TODO: will need to use `primrec_recOn`.
  sorry

/--
The `eval` of `c.subst c'` with oracle `o` is equal to the `eval` of `c` with oracle `c'.eval o`.
-/
theorem eval_subst (c c' : Code) (o : ℕ →. ℕ) : (c.subst c').eval o = c.eval (c'.eval o) := by
  induction c with simp [subst, eval, *]

/--
The `eval` of `c.substPartrec c'` is equal to the `eval` of `c` with oracle `c'.eval`.
-/
theorem eval_substPartrec (c : Code) (c' : Nat.Partrec.Code) : (c.substPartrec c').eval = c.eval c'.eval := by
  induction c with simp [substPartrec, eval, Nat.Partrec.Code.eval, *]

end RecursiveIn.Code

namespace Nat.Partrec.Code

/--
A code which evaluates to the equality function.
-/
protected def eq : Code :=
  -- TODO: This definition should mimic the proof in `Computability/Primrec/Basic.lean` that equality is primitive recursive.
  sorry

/--
`Code.eq` evaluates to the equality function.
-/
@[simp]
lemma eval_eq : eval Code.eq = Nat.unpaired fun x y => (decide (x = y)).toNat := by
  sorry

/--
A code which evaluates to the maximum function.
-/
protected def max : Code :=
  -- TODO: This definition should mimic the proof in `Computability/Primrec/Basic.lean` that max is primitive recursive.
  sorry

/--
`Code.max` evaluates to the maximum function.
-/
@[simp]
lemma eval_max : eval Code.max = Nat.unpaired Nat.max := by
  sorry

/--
From a list `l`, return a code whose `eval` is `fun n => n ∈ l`.
-/
def listMem : List ℕ → Code
  | .nil => Code.zero
  | .cons x xs => Code.max.comp <| Code.pair (Code.eq.curry x) (listMem xs)

/--
`ofList l` evaluates to `fun n => l[n]?`.
-/
@[simp]
lemma eval_listMem (l : List ℕ) (n : ℕ) : eval (listMem l) n = (decide (n ∈ l)).toNat := by
  induction l generalizing n with
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
  -- TODO: This will be crucial to reasoning about the evaluation of oracles using partial information. We will need to call `c.substPartrec (listMem l)` to computably replace the oracle in code `c` with the oracle `l`.
  sorry

end Nat.Partrec.Code

end
