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
  induction c with
  | zero | succ | left | right => rfl
  | oracle => simp [subst, eval]
  | pair cf cg IHcf IHcg => sorry
  | comp cf cg IHcf IHcg => sorry
  | prec cf cg IHcf IHcg => sorry
  | rfind' cf IHcf => sorry

/--
The `eval` of `c.substPartrec c'` is equal to the `eval` of `c` with oracle `c'.eval`.
-/
theorem eval_substPartrec (c : Code) (c' : Nat.Partrec.Code) : (c.substPartrec c').eval = c.eval c'.eval := by
  induction c with
  | zero | succ | left | right => rfl
  | oracle => simp [substPartrec, eval]
  | pair cf cg IHcf IHcg => sorry
  | comp cf cg IHcf IHcg => sorry
  | prec cf cg IHcf IHcg => sorry
  | rfind' cf IHcf => sorry

end RecursiveIn.Code
