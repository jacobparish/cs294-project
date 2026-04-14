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
  -- Provide implicit function arguments explicitly to avoid slow unification
  refine (primrec_recOn (α := Code × Code) (σ := Code)
    (pr := fun _ _ _ hf hg => pair hf hg)
    (co := fun _ _ _ hf hg => comp hf hg)
    (pc := fun _ _ _ hf hg => prec hf hg)
    (rf := fun _ _ hf => rfind' hf)
    Primrec.fst
    (Primrec.const zero) (Primrec.const succ) (Primrec.const left) (Primrec.const right)
    Primrec.snd
    (primrec₂_pair.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (primrec₂_comp.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (primrec₂_prec.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (primrec_rfind'.comp (Primrec.snd.comp Primrec.snd))).of_eq ?_
  intro ⟨c₁, c₂⟩
  induction c₁ with
  | zero | succ | left | right | oracle => rfl
  | pair cf cg ihf ihg => exact congrArg₂ pair ihf ihg
  | comp cf cg ihf ihg => exact congrArg₂ comp ihf ihg
  | prec cf cg ihf ihg => exact congrArg₂ prec ihf ihg
  | rfind' cf ihf => exact congrArg rfind' ihf

/--
`substPartrec` is primitive recursive.
-/
theorem primrec₂_substPartrec : Primrec₂ substPartrec := by
  refine (primrec_recOn (α := Code × Nat.Partrec.Code) (σ := Nat.Partrec.Code)
    (pr := fun _ _ _ hf hg => Nat.Partrec.Code.pair hf hg)
    (co := fun _ _ _ hf hg => Nat.Partrec.Code.comp hf hg)
    (pc := fun _ _ _ hf hg => Nat.Partrec.Code.prec hf hg)
    (rf := fun _ _ hf => Nat.Partrec.Code.rfind' hf)
    Primrec.fst
    (Primrec.const .zero) (Primrec.const .succ) (Primrec.const .left) (Primrec.const .right)
    Primrec.snd
    (Nat.Partrec.Code.primrec₂_pair.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Nat.Partrec.Code.primrec₂_comp.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Nat.Partrec.Code.primrec₂_prec.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
    (Nat.Partrec.Code.primrec_rfind'.comp (Primrec.snd.comp Primrec.snd))).of_eq ?_
  intro ⟨c₁, c₂⟩
  induction c₁ with
  | zero | succ | left | right | oracle => rfl
  | pair cf cg ihf ihg => exact congrArg₂ Nat.Partrec.Code.pair ihf ihg
  | comp cf cg ihf ihg => exact congrArg₂ Nat.Partrec.Code.comp ihf ihg
  | prec cf cg ihf ihg => exact congrArg₂ Nat.Partrec.Code.prec ihf ihg
  | rfind' cf ihf => exact congrArg Nat.Partrec.Code.rfind' ihf

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

end
