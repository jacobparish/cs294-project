module

public import Mathlib.Computability.PartrecCode
public import Project.Basic

/-!
This extends `Mathlib.Computability.PartrecCode` to add some additional lemmas about `Nat.Partrec.Code`. In particular, codes for several basic functions are defined, along with simp lemmas for their eval functions.
-/

@[expose] public section

namespace Nat.Partrec.Code
section

-- TODO: It may be better to create a type `Nat.Primrec.Code`, because then its eval function will be total and we won't have to deal with PFun.

/--
A code for the function with empty domain.
-/
protected def none : Code := rfind' succ

/--
A code which evaluates to `Nat.pred`.
-/
def pred : Code := (prec zero (left.comp right)).comp (pair zero Code.id)

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

The naive construction `(prec cfalse (ctrue.comp left)).comp (pair Code.id c)` is incorrect: `prec` always
evaluates its base case, so `cfalse` would be evaluated even when `c.eval n ≠ 0` (and likewise the result
binds through repeated calls to `ctrue` for larger values of `c.eval n`). To avoid this, we evaluate `c`
once and then dispatch on the result via `comp (pair Code.id c)`. Inside, we compute the sign
`s := sg(x) ∈ {0, 1}` (where `x = c.eval n`), then use two `prec` constructions whose bases are
`Code.const 0` (harmlessly total) so that the actual branch (`ctrue` or `cfalse`) is invoked only when
its corresponding selector value is `1`. The two branch values are then summed; the unselected branch
contributes `0`.
-/
protected def ite (c ctrue cfalse : Code) : Code :=
  -- The inner code receives input `Nat.pair n x` where `x = c.eval n`.
  let sgInner : Code := (prec (Code.const 0) (Code.const 1)).comp (pair zero right)
  let nzInner : Code := Code.sub.comp (pair (Code.const 1) sgInner)
  let trueInner : Code := (prec (Code.const 0) (ctrue.comp left)).comp (pair left sgInner)
  let falseInner : Code := (prec (Code.const 0) (cfalse.comp left)).comp (pair left nzInner)
  let inner : Code := Code.add.comp (pair trueInner falseInner)
  inner.comp (pair Code.id c)

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

/--
`none` always evaluates to `Part.none`.
-/
@[simp]
lemma eval_none : eval Code.none = fun _ => Part.none := by
  funext n
  simp [eval, Code.none, Part.eq_none_iff]

@[simp]
lemma eval_pred : eval Code.pred = Nat.pred := by
  have aux : ∀ m, eval (prec zero (left.comp right)) (Nat.pair 0 m) = Part.some (Nat.pred m) := by
    intro m
    induction m with
    | zero => rw [eval_prec_zero]; rfl
    | succ k IH =>
      rw [eval_prec_succ, IH]
      simp [eval]
  funext n
  have h0 : eval zero n = Part.some 0 := rfl
  have hpair : eval (pair zero Code.id) n = Part.some (Nat.pair 0 n) := by
    show Nat.pair <$> eval zero n <*> eval Code.id n = Part.some (Nat.pair 0 n)
    rw [h0, eval_id]
    simp [Seq.seq]
  show eval ((prec zero (left.comp right)).comp (pair zero Code.id)) n = Part.some (Nat.pred n)
  change eval (pair zero Code.id) n >>= eval (prec zero (left.comp right)) = _
  rw [hpair]
  simp [aux n]

@[simp]
lemma eval_add : eval Code.add = Nat.unpaired Nat.add := by
  suffices h : ∀ a m, eval Code.add (Nat.pair a m) = Part.some (a + m) by
    funext n
    conv_lhs => rw [← n.pair_unpair]
    rw [h]
    rfl
  intro a m
  induction m with
  | zero => simp [Code.add]
  | succ k IH =>
    rw [Code.add, eval_prec_succ, ← Code.add]
    simp [IH, eval]
    omega

@[simp]
lemma eval_sub : eval Code.sub = Nat.unpaired Nat.sub := by
  suffices h : ∀ a m, eval Code.sub (Nat.pair a m) = Part.some (a - m) by
    funext n
    conv_lhs => rw [← n.pair_unpair]
    rw [h]
    rfl
  intro a m
  induction m with
  | zero => simp [Code.sub]
  | succ k IH =>
    rw [Code.sub, eval_prec_succ, ← Code.sub]
    simp [IH, eval, eval_pred]
    omega

@[simp]
lemma eval_swap : eval Code.swap = Nat.unpaired (Function.swap Nat.pair) := by
  funext n
  simp [Code.swap, eval, Seq.seq]

@[simp]
lemma eval_ite {c ctrue cfalse : Code} {n} :
    eval (c.ite ctrue cfalse) n =
      (c.eval n).bind fun x => if x ≠ 0 then ctrue.eval n else cfalse.eval n := by
  -- Helper 1: sign function via prec.
  have h_sg : ∀ a x, eval (prec (Code.const 0) (Code.const 1)) (Nat.pair a x) =
                Part.some (if x = 0 then 0 else 1) := by
    intros a x
    induction x with
    | zero => simp
    | succ k IH => rw [eval_prec_succ, IH]; simp
  -- Helper 2: prec base 0 with `cb.comp left`, at second-arg 0 (without evaluating `cb`).
  have h_pcl0 : ∀ (cb : Code) a,
      eval (prec (Code.const 0) (cb.comp left)) (Nat.pair a 0) = Part.some 0 := fun _ _ => by simp
  -- Helper 3: prec base 0 with `cb.comp left`, at second-arg 1.
  have h_pcl1 : ∀ (cb : Code) a,
      eval (prec (Code.const 0) (cb.comp left)) (Nat.pair a 1) = eval cb a := by
    intros cb a
    rw [show (1 : ℕ) = 0 + 1 from rfl, eval_prec_succ, h_pcl0]
    simp [eval]
  -- Combined: dispatch on `if x = 0 then 0 else 1`.
  have h_pcl : ∀ (cb : Code) a x,
      eval (prec (Code.const 0) (cb.comp left)) (Nat.pair a (if x = 0 then 0 else 1)) =
        if x = 0 then Part.some 0 else eval cb a := by
    intros cb a x
    by_cases hx : x = 0
    · simp [hx, h_pcl0]
    · simp [hx, h_pcl1]
  -- Compute the sign-inner code at input `Nat.pair n x`.
  have h_sgInner : ∀ x, eval ((prec (Code.const 0) (Code.const 1)).comp (pair zero right))
      (Nat.pair n x) = Part.some (if x = 0 then 0 else 1) := by
    intro x
    show eval (pair zero right) (Nat.pair n x) >>= eval (prec (Code.const 0) (Code.const 1)) = _
    have hpr : eval (pair zero right) (Nat.pair n x) = Part.some (Nat.pair 0 x) := by
      show Nat.pair <$> eval zero (Nat.pair n x) <*> eval right (Nat.pair n x) = _
      have hz : eval zero (Nat.pair n x) = Part.some 0 := rfl
      have hr : eval right (Nat.pair n x) = Part.some x := by simp [eval]
      rw [hz, hr]; simp [Seq.seq]
    rw [hpr, Part.bind_eq_bind, Part.bind_some, h_sg]
  -- Compute the (1 − sg)-inner code at input `Nat.pair n x`.
  have h_nzInner : ∀ x, eval (Code.sub.comp (pair (Code.const 1)
      ((prec (Code.const 0) (Code.const 1)).comp (pair zero right)))) (Nat.pair n x) =
      Part.some (if x = 0 then 1 else 0) := by
    intro x
    show eval (pair _ _) (Nat.pair n x) >>= eval Code.sub = _
    have hpr : eval (pair (Code.const 1)
        ((prec (Code.const 0) (Code.const 1)).comp (pair zero right))) (Nat.pair n x) =
        Part.some (Nat.pair 1 (if x = 0 then 0 else 1)) := by
      show Nat.pair <$> eval (Code.const 1) (Nat.pair n x) <*> _ = _
      rw [eval_const, h_sgInner]
      simp [Seq.seq]
    rw [hpr, Part.bind_eq_bind, Part.bind_some, eval_sub]
    by_cases hx : x = 0 <;> simp [hx, Nat.unpaired]
  -- Compute the true-branch inner code at input `Nat.pair n x`.
  have h_tInner : ∀ x, eval ((prec (Code.const 0) (ctrue.comp left)).comp
      (pair left ((prec (Code.const 0) (Code.const 1)).comp (pair zero right))))
      (Nat.pair n x) = (if x = 0 then Part.some 0 else eval ctrue n) := by
    intro x
    show eval (pair left _) (Nat.pair n x) >>= eval (prec (Code.const 0) (ctrue.comp left)) = _
    have hpr : eval (pair left ((prec (Code.const 0) (Code.const 1)).comp (pair zero right)))
        (Nat.pair n x) = Part.some (Nat.pair n (if x = 0 then 0 else 1)) := by
      show Nat.pair <$> eval left (Nat.pair n x) <*> _ = _
      rw [h_sgInner]
      simp [eval, Seq.seq]
    rw [hpr, Part.bind_eq_bind, Part.bind_some, h_pcl]
  -- Compute the false-branch inner code at input `Nat.pair n x`.
  have h_fInner : ∀ x, eval ((prec (Code.const 0) (cfalse.comp left)).comp
      (pair left (Code.sub.comp (pair (Code.const 1)
        ((prec (Code.const 0) (Code.const 1)).comp (pair zero right))))))
      (Nat.pair n x) = (if x = 0 then eval cfalse n else Part.some 0) := by
    intro x
    show eval (pair left _) (Nat.pair n x) >>= eval (prec (Code.const 0) (cfalse.comp left)) = _
    have hpr : eval (pair left (Code.sub.comp (pair (Code.const 1)
        ((prec (Code.const 0) (Code.const 1)).comp (pair zero right))))) (Nat.pair n x) =
        Part.some (Nat.pair n (if x = 0 then 1 else 0)) := by
      show Nat.pair <$> eval left (Nat.pair n x) <*> _ = _
      rw [h_nzInner]
      simp [eval, Seq.seq]
    rw [hpr, Part.bind_eq_bind, Part.bind_some]
    by_cases hx : x = 0
    · simp [hx, h_pcl1]
    · simp [hx, h_pcl0]
  -- Now compute the whole eval:
  -- eval (c.ite ctrue cfalse) n = eval (pair Code.id c) n >>= eval inner
  show eval (pair Code.id c) n >>= eval (Code.add.comp (pair _ _)) = _
  have hpic : eval (pair Code.id c) n = (eval c n).map (Nat.pair n) := by
    show Nat.pair <$> eval Code.id n <*> eval c n = _
    rw [eval_id]
    simp [Seq.seq, Part.map_eq_map]
  rw [hpic, Part.bind_eq_bind, Part.bind_map]
  refine congrArg ((eval c n).bind) ?_
  funext x
  -- Goal: eval (Code.add.comp (pair trueInner falseInner)) (Nat.pair n x) =
  --       if x ≠ 0 then ctrue.eval n else cfalse.eval n
  show eval (pair _ _) (Nat.pair n x) >>= eval Code.add = _
  show (Nat.pair <$> eval _ (Nat.pair n x) <*> eval _ (Nat.pair n x)) >>= eval Code.add = _
  rw [h_tInner x, h_fInner x, eval_add]
  -- Goal: (Nat.pair <$> (if x = 0 then Part.some 0 else ctrue.eval n) <*>
  --        (if x = 0 then cfalse.eval n else Part.some 0)) >>= ↑(Nat.unpaired Nat.add) =
  --       if x ≠ 0 then ctrue.eval n else cfalse.eval n
  have unaddpair : ∀ a b : ℕ, (↑(Nat.unpaired Nat.add) : ℕ →. ℕ) (Nat.pair a b) = Part.some (a + b) :=
    fun a b => by show Part.some _ = _; congr 1; simp [Nat.unpaired]
  by_cases hx : x = 0
  · -- x = 0: result should be cfalse.eval n.
    simp only [hx, ↓reduceIte, ne_eq, not_true_eq_false]
    -- Compute: Nat.pair <$> Part.some 0 = Part.some (Nat.pair 0).
    have h1 : (Nat.pair <$> (Part.some 0 : Part ℕ)) = Part.some (Nat.pair 0) := rfl
    -- Use pure_seq: Part.some f <*> x = f <$> x.
    have h2 : (Part.some (Nat.pair 0) : Part (ℕ → ℕ)) <*> cfalse.eval n =
              Nat.pair 0 <$> cfalse.eval n := pure_seq _ _
    rw [h1, h2, Part.map_eq_map, Part.bind_eq_bind, Part.bind_map]
    -- Goal: (cfalse.eval n).bind (fun b => ↑(Nat.unpaired Nat.add) (Nat.pair 0 b)) = cfalse.eval n
    have h3 : (fun b => (↑(Nat.unpaired Nat.add) : ℕ →. ℕ) (Nat.pair 0 b)) = Part.some := by
      funext b; rw [unaddpair]; simp
    rw [h3]; exact Part.bind_some_right _
  · -- x ≠ 0: result should be ctrue.eval n.
    simp only [hx, ↓reduceIte, ne_eq, not_false_eq_true]
    -- Compute: Nat.pair <$> ctrue.eval n = Part.map Nat.pair (ctrue.eval n)
    rw [show (Nat.pair <$> ctrue.eval n) = Part.map Nat.pair (ctrue.eval n) from rfl]
    -- Use seq def: f <*> x = f >>= fun g => g <$> x  (for monads).
    -- In Part: (Part.map Nat.pair X) <*> Part.some 0 = X.bind (fun a => Nat.pair a <$> Part.some 0)
    --                                                  = X.bind (fun a => Part.some (Nat.pair a 0))
    have h1 : Part.map Nat.pair (ctrue.eval n) <*> (Part.some 0 : Part ℕ) =
              (ctrue.eval n).bind (fun a => Part.some (Nat.pair a 0)) := by
      show Part.map Nat.pair (ctrue.eval n) >>= (fun g => g <$> Part.some 0) = _
      rw [Part.bind_eq_bind, Part.bind_map]
      rfl
    rw [h1, Part.bind_eq_bind, Part.bind_assoc]
    -- Goal: (ctrue.eval n).bind (fun a => (Part.some (Nat.pair a 0)).bind ↑(unpaired add)) = ctrue.eval n
    have h2 : (fun a : ℕ => (Part.some (Nat.pair a 0)).bind (↑(Nat.unpaired Nat.add) : ℕ →. ℕ)) =
              Part.some := by
      funext a
      rw [Part.bind_some, unaddpair]
      simp
    rw [h2]; exact Part.bind_some_right _

@[simp]
lemma eval_le : eval Code.le = Nat.unpaired fun x y => (decide (x ≤ y)).toNat  := by
  funext n
  by_cases n.unpair.1 ≤ n.unpair.2 <;> simp [Code.le, Nat.sub_eq_zero_iff_le, *]

@[simp]
lemma eval_min : eval Code.min = Nat.unpaired Nat.min := by
  funext n
  by_cases h : n.unpair.1 ≤ n.unpair.2
  · simp [Code.min, eval, h]
  · simp [Code.min, eval, h, le_of_not_ge h]

@[simp]
lemma eval_max : eval Code.max = Nat.unpaired Nat.max := by
  funext n
  by_cases h : n.unpair.1 ≤ n.unpair.2
  · simp [Code.max, eval, h]
  · simp [Code.max, eval, h, le_of_not_ge h]

@[simp]
lemma eval_eq : eval Code.eq = Nat.unpaired fun x y => (decide (x = y)).toNat := by
  funext n
  by_cases hxy : n.unpair.1 ≤ n.unpair.2
  · by_cases hyx : n.unpair.2 ≤ n.unpair.1
    · have h : n.unpair.1 = n.unpair.2 := le_antisymm hxy hyx
      simp [Code.eq, eval, Seq.seq, h]
    · have h : n.unpair.1 ≠ n.unpair.2 := by
        intro h
        exact hyx (h ▸ le_rfl)
      simp [Code.eq, eval, Seq.seq, hyx, h]
  · have hyx : n.unpair.2 ≤ n.unpair.1 := le_of_not_ge hxy
    have h : n.unpair.1 ≠ n.unpair.2 := by
      intro h
      exact hxy (h ▸ le_rfl)
    simp [Code.eq, eval, Seq.seq, hxy, hyx, h]

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
lemma eval_listMem (l : List ℕ) : eval (listMem l) = ofPred (· ∈ l) := by
  funext n
  induction l with
  | nil => rfl
  | cons x xs IH =>
    simp only [listMem, eval, IH, Seq.seq]
    by_cases! h : x = n
    · simp [h, Bool.toNat_le, ofPred]
    · simp [h, h.symm, ofPred]

/--
`listMem` is primitive recursive.
-/
lemma primrec_listMem : Primrec listMem := by
  convert Primrec.list_rec .id (.const zero) (?_ : Primrec₂ fun _ (x, xs, IH) => Code.max.comp <| pair (Code.eq.curry x) IH) with l
  · induction l with simp [listMem, *]
  exact (primrec₂_comp.comp (.const _) .id).comp <|
    primrec₂_pair.comp (primrec₂_curry.comp (.const _) (.comp .fst .snd)) <|
      .comp .snd (.comp .snd .snd)

/--
From a list `l`, return a code whose eval is `fun n => l[n]?`.
-/
def ofList : List ℕ → Code
  | .nil => Code.none
  | .cons x xs => prec ((Code.const x).comp right) ((ofList xs).comp (left.comp right))
    |>.comp (pair zero Code.id)

/--
`ofList l` evaluates to `fun n => l[n]?`.
-/
@[simp]
lemma eval_ofList (l : List ℕ) : eval (ofList l) = (↑l[·]?) := by
  induction l with
  | nil => simp [ofList]
  | cons x xs IHxs =>
    funext n
    induction n with
    | zero =>
      simp [ofList, eval, Seq.seq, Part.bind_some_eq_map]
      rfl
    | succ n IHn =>
      simp_all [ofList, eval, Seq.seq, pure, PFun.pure]
      by_cases! h : n < xs.length + 1
      · rw [List.getElem?_eq_getElem h]
        simp
      · rw [List.getElem?_eq_none h, List.getElem?_eq_none (le_of_succ_le h)]
        simp

/--
`ofList` is primitive recursive.
-/
lemma primrec_ofList : Primrec ofList := by
  convert Primrec.list_rec .id (.const Code.none) (?_ : Primrec₂ fun _ (x, xs, IH) => prec ((Code.const x).comp right) (IH.comp (left.comp right))
    |>.comp (pair zero Code.id)) with l
  · induction l with simp [ofList, *]
  refine primrec₂_comp.comp (primrec₂_prec.comp ?_ ?_) (.const _)
  · exact primrec₂_comp.comp (primrec_const.comp (.comp .fst .snd)) (.const _)
  · exact primrec₂_comp.comp (.comp .snd (.comp .snd .snd)) (.const _)

end
end Nat.Partrec.Code

end
