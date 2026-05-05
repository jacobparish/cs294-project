module

public import Project.Queries
public import Project.PartrecCode
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

namespace Nat.RecursiveIn.Code

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
Substitute the oracle in a code `c` for a `Partrec.Code` `c'`.
-/
def substPartrec (c : Code) (c' : Partrec.Code) : Partrec.Code := match c with
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
    (.const zero) (.const succ) (.const left) (.const right)
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
  refine (primrec_recOn (α := Code × Partrec.Code) (σ := Partrec.Code)
    (pr := fun _ _ _ => Partrec.Code.pair)
    (co := fun _ _ _ => Partrec.Code.comp)
    (pc := fun _ _ _ => Partrec.Code.prec)
    (rf := fun _ _ => Partrec.Code.rfind')
    Primrec.fst
    (.const .zero) (.const .succ) (.const .left) (.const .right)
    Primrec.snd
    (Partrec.Code.primrec₂_pair.comp
      (.comp .fst (.comp .snd (.comp .snd .snd)))
      (.comp .snd (.comp .snd (.comp .snd .snd))))
    (Partrec.Code.primrec₂_comp.comp
      (.comp .fst (.comp .snd (.comp .snd .snd)))
      (.comp .snd (.comp .snd (.comp .snd .snd))))
    (Partrec.Code.primrec₂_prec.comp
      (.comp .fst (.comp .snd (.comp .snd .snd)))
      (.comp .snd (.comp .snd (.comp .snd .snd))))
    (Partrec.Code.primrec_rfind'.comp (.comp .snd .snd))).of_eq ?_
  intro ⟨c₁, c₂⟩
  induction c₁ with
  | zero | succ | left | right | oracle => rfl
  | pair cf cg ihf ihg => exact congrArg₂ Partrec.Code.pair ihf ihg
  | comp cf cg ihf ihg => exact congrArg₂ Partrec.Code.comp ihf ihg
  | prec cf cg ihf ihg => exact congrArg₂ Partrec.Code.prec ihf ihg
  | rfind' cf ihf => exact congrArg Partrec.Code.rfind' ihf

/--
The `eval` of `c.subst c'` with oracle `o` is equal to the `eval` of `c` with oracle `c'.eval o`.
-/
lemma eval_subst (c c' : Code) (o : ℕ →. ℕ) : (c.subst c').eval o = c.eval (c'.eval o) := by
  induction c with simp [subst, eval, *]

/--
The `eval` of `c.substPartrec c'` is equal to the `eval` of `c` with oracle `c'.eval`.
-/
lemma eval_substPartrec (c : Code) (c' : Partrec.Code) : (c.substPartrec c').eval = c.eval c'.eval := by
  induction c with simp [substPartrec, eval, Partrec.Code.eval, *]

/--
This essentially says that `(c.substPartrec c').evaln k` only uses the first `k` values of the oracle `c'`.

Note: the more obvious conclusion `(c.substPartrec c₁).evaln k = (c.substPartrec c₂).evaln k` is false, since `c₁` and `c₂` can take a different number of steps, so it could be that `c₁` halts on some query while `c₂` does not.
-/
theorem evaln_substPartrec (c : Code) {c₁ c₂ : Partrec.Code} {k : ℕ} (hres : ∀ i < k, ∀ m ∈ c₁.eval i, m ∈ c₂.eval i) {n x₁ x₂} (hx₁ : x₁ ∈ (c.substPartrec c₁).evaln k n) (hx₂ : x₂ ∈ (c.substPartrec c₂).evaln k n) : x₁ = x₂ := by
  induction k generalizing c n x₁ x₂ with
  | zero => simp [Partrec.Code.evaln] at hx₁
  | succ k IHk =>
    have hres' : ∀ i < k, ∀ m ∈ c₁.eval i, m ∈ c₂.eval i :=
      fun i hi => hres i (Nat.lt_succ_of_lt hi)
    induction c generalizing n x₁ x₂ with
    | zero | succ | left | right => simp_all [substPartrec]
    | oracle =>
      -- This is the only case where `hres` is used.
      unfold substPartrec at hx₁ hx₂
      have hn : n < k + 1 := Partrec.Code.evaln_bound hx₁
      apply Partrec.Code.evaln_sound at hx₁
      apply Partrec.Code.evaln_sound at hx₂
      exact Part.mem_unique (hres n hn x₁ hx₁) hx₂
    | pair cf cg IHcf IHcg =>
      simp [substPartrec, Partrec.Code.evaln, Option.bind_eq_some_iff, Seq.seq] at hx₁ hx₂
      obtain ⟨-, a₁, ha₁, b₁, hb₁, rfl⟩ := hx₁
      obtain ⟨-, a₂, ha₂, b₂, hb₂, rfl⟩ := hx₂
      rw [pair_eq_pair]
      exact ⟨IHcf ha₁ ha₂, IHcg hb₁ hb₂⟩
    | comp cf cg IHcf IHcg =>
      simp [substPartrec, Partrec.Code.evaln, Option.bind_eq_some_iff] at hx₁ hx₂
      obtain ⟨-, y₁, hy₁, hx₁⟩ := hx₁
      obtain ⟨-, y₂, hy₂, hx₂⟩ := hx₂
      rw [IHcg hy₁ hy₂] at hx₁
      exact IHcf hx₁ hx₂
    | prec cf cg IHcf IHcg =>
      have := n.pair_unpair
      generalize n.unpair.1 = a, n.unpair.2 = m at this
      subst this
      cases m with
      | zero =>
        simp [substPartrec, Partrec.Code.evaln, Option.bind_eq_some_iff] at hx₁ hx₂
        exact IHcf hx₁.2 hx₂.2
      | succ m =>
        simp [substPartrec, Partrec.Code.evaln, Option.bind_eq_some_iff] at hx₁ hx₂
        obtain ⟨-, y₁, hy₁, hx₁⟩ := hx₁
        obtain ⟨-, y₂, hy₂, hx₂⟩ := hx₂
        rw [← substPartrec] at hy₁ hy₂
        rw [IHk _ hres' hy₁ hy₂] at hx₁
        exact IHcg hx₁ hx₂
    | rfind' cf IHcf =>
      simp [substPartrec, Partrec.Code.evaln, Option.bind_eq_some_iff] at hx₁ hx₂
      obtain ⟨-, y₁, hy₁, hx₁⟩ := hx₁
      obtain ⟨-, y₂, hy₂, hx₂⟩ := hx₂
      rw [IHcf hy₁ hy₂] at hx₁
      cases y₂ with
      | zero => simp_all
      | succ y₂ =>
        simp at hx₁ hx₂
        rw [← substPartrec] at hx₁ hx₂
        exact IHk _ hres' hx₁ hx₂

end Nat.RecursiveIn.Code

end
