import Project.Basic
import Project.OracleCode
import Project.Evaln
import Project.List
import Project.Primrec
import Project.RE
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite

namespace Primcodable

instance {α : Type*} [Primcodable α] : Primcodable (WithBot α) :=
  Primcodable.option

end Primcodable

namespace Computability.FriedbergMuchnik

/--
Notation for the pairing function `Nat.pair`.
-/
local notation "⟪" a ", " b "⟫" => Nat.pair a b

open Nat.RecursiveIn Denumerable

/--
The type carrying the data for each stage of the Friedberg-Muchnik construction. This is usually unpacked as `(p, r)`. See `extend` for the interpretation of `p` and `r`.
-/
abbrev FMStage := List (ℕ × ℕ) × List (WithBot ℕ)

/--
See `extend` for a description of the parameters.
-/
def isWitness (i k : ℕ) : FMStage → (ℕ × ℕ) → Bool
  | (p, r), (e, y) =>
  -- We need requirement `⟪i, e⟫` to not currently be satisfied (`r[⟪i, e⟫] = ⊥`), as well as a witness `x = ⟪e, y⟫` such that:
  -- (1) `x` is not already enumerated into `p[i]`,
  -- (2) the eval of the code encoded by `e` with oracle `p[≠ i]` halts in `< k` steps and outputs `x`, and
  -- (3) `r[n] < x` for every `n < ⟪i, e⟫`.
  r.getI ⟪i, e⟫ = ⊥
    ∧ (i, ⟪e, y⟫) ∉ p
    ∧ 0 ∈ (ofNat Code e).evaln k (Nat.unpaired fun i' x' => if i ≠ i' ∧ (i', x') ∈ p then 1 else 0) ⟪e, y⟫
    ∧ ∀ n < ⟪i, e⟫, r.getI n < .some ⟪e, y⟫

/--
See `extend` for a description of the parameters.
-/
def findWitness? (i k : ℕ) (s : FMStage) : Option (ℕ × ℕ) :=
  -- `List.product` is ordered so that this checks all `y`-values for `e = 0`, then all `y`-values for `e = 1`, and so on.
  (List.range k) ×ˢ (List.range k) |>.find? (isWitness i k s)

/--
The roles of the parameters are as follows:
* `p` : The finite sets enumerated so far, encoded as list of `ℕ × ℕ`, where the first coordinate is the index of the set, and the second coordinate is the element of the set. We write `p.i` for the `i`th set.
* `i` : The index of the set being extended at this stage. We try to ensure that `p.i` is not computable relative to `p.(≠ i)`.
* `k` : A bound on (1) the number of codes to check at this stage, (2) the number of witnesses to check at this stage, and (3) the number of steps to run `evaln` at this stage.
* `r` : The list of restraints. `r[⟪i, e⟫] = ⊥` (or the index is out of bounds) if requirement `⟪i, e⟫` is not currently satisfied. `r[⟪i, e⟫] = some j'` if requirement `⟪i, e⟫` has been satisfied at some earlier stage `j < k`, and has not been injured since then.
-/
def extend (i k : ℕ) (s : FMStage) :=
  match findWitness? i k s with
  -- If no strategy needs to act, then do nothing.
  | none => s
  -- If strategy `⟪i, e⟫` needs to act, then add the witness to `p.i`. Also, injure all strategies with lower priority than `⟪i, e⟫`, and set `r[⟪i, e⟫] = some k`.
  | some (e, y) => ((i, ⟪e, y⟫) :: s.1, s.2.takeI ⟪i, e⟫ ++ [WithBot.some k])

/--
`extend` is monotone in the first coordinate of `FMStage`.
-/
lemma subset_extend {i k s} : s.1 ⊆ (extend i k s).1 := by
  unfold extend
  rcases findWitness? i k s with - | ⟨e, y⟩
  · exact List.Subset.refl _
  · exact List.subset_cons_self _ _

/--
`isWitness` is primitive recursive.
-/
lemma primrec₂_isWitness : Primrec₂ (fun (a : ℕ × ℕ × FMStage) (x : ℕ × ℕ) => isWitness a.1 a.2.1 a.2.2 x) := by
  -- Set up projections.
  set I : Type := (ℕ × ℕ × FMStage) × (ℕ × ℕ)
  have hi : Primrec (fun p : I => p.1.1) := .comp .fst .fst
  have hk : Primrec (fun p : I => p.1.2.1) := .comp .fst (.comp .snd .fst)
  have hp : Primrec (fun p : I => p.1.2.2.1) :=
    .comp .fst (.comp .snd (.comp .snd .fst))
  have hr : Primrec (fun p : I => p.1.2.2.2) :=
    .comp .snd (.comp .snd (.comp .snd .fst))
  have he : Primrec (fun p : I => p.2.1) := .comp .fst .snd
  have hy : Primrec (fun p : I => p.2.2) := .comp .snd .snd
  have hie : Primrec (fun p : I => Nat.pair p.1.1 p.2.1) :=
    Primrec₂.natPair.comp hi he
  have hey : Primrec (fun p : I => Nat.pair p.2.1 p.2.2) :=
    Primrec₂.natPair.comp he hy
  simp only [isWitness, Option.mem_def, Bool.decide_and, decide_not]
  refine Primrec.and.comp ?_ (Primrec.and.comp ?_ (Primrec.and.comp ?_ ?_))
  · refine (Primrec.eq.comp ?_ (.const none)).decide
    exact Primrec.list_getI.comp hr hie
  · refine Primrec.not.comp ?_
    exact (Primrec.list_mem.comp hp (.pair hi hey)).decide
  · simp only [Code.evaln]
    refine (Primrec.eq.comp ?_ (.const _)).decide
    have hcode : Primrec fun p : I => ofNat Code p.2.1 := (Primrec.ofNat Code).comp he
    have hlist : Primrec fun p : I => List.ofFnNat (Nat.unpaired fun i' x' => if p.1.1 ≠ i' ∧ (i', x') ∈ p.1.2.2.1 then 1 else 0) p.1.2.1 := by
      refine Primrec.list_ofFnNat ?_ hk
      simp only [Primrec₂, Nat.unpaired]
      refine Primrec.ite (.and (.not ?_) ?_) (.const 1) (.const 0)
      · refine Primrec.eq.comp ?_ ?_
        · exact hi.comp .fst
        · exact .comp .fst (.comp .unpair .snd)
      · refine Primrec.list_mem.comp ?_ ?_
        · exact hp.comp .fst
        · refine .pair ?_ ?_
          · exact .comp .fst (.comp .unpair .snd)
          · exact .comp .snd (.comp .unpair .snd)
    exact Code.primrec_evalp.comp (.pair (.pair hk (.pair hcode hlist)) hey)
  · -- `∀ n < ⟪i, e⟫, r.getI i < .some ⟪e, y⟫`
    -- We prove this as a primrec relation `R i (l, k) := l.getI i < some k`
    -- and then apply `forall_mem_list` with `L = List.range ⟪i, e⟫`.
    -- decide (o < some k) for o : Option ℕ is primrec via option_casesOn.
    have h_optlt : Primrec (fun (a : WithBot ℕ × ℕ) => decide (a.1 < .some a.2)) := by
      have h₂ : Primrec₂ (fun (a : WithBot ℕ × ℕ) (n : ℕ) => decide (n < a.2)) :=
        Primrec₂.comp Primrec.nat_lt.decide Primrec.snd
          (Primrec.snd.comp Primrec.fst)
      refine (Primrec.option_casesOn Primrec.fst (Primrec.const true) h₂).of_eq
        fun ⟨o, k⟩ => ?_
      cases o
      · rfl
      · simp [WithBot.some_eq_coe]
    -- Lift to a PrimrecRel R : ℕ → (List (Withbot ℕ) × ℕ) → Prop.
    have hR_prim : PrimrecRel
        (fun (i : ℕ) (lk : List (WithBot ℕ) × ℕ) => lk.1.getI i < some lk.2) := by
      refine Primrec.primrecPred ?_
      refine (h_optlt.comp (α := ℕ × (List (Option ℕ) × ℕ))
        (Primrec.pair (Primrec.list_getI.comp (Primrec.fst.comp Primrec.snd) Primrec.fst)
          (Primrec.snd.comp Primrec.snd))).of_eq fun p => rfl
    -- ∀ n ∈ List.range n, R i lk
    have h_all : PrimrecRel (fun (L : List ℕ) (lk : List (WithBot ℕ) × ℕ) =>
        ∀ n ∈ L, lk.1.getI n < some lk.2) := hR_prim.forall_mem_list
    have hrange : Primrec (fun p : I => List.range ⟪p.1.1, p.2.1⟫) := Primrec.list_range.comp hie
    refine ((h_all.comp hrange (Primrec.pair hr hey)).decide).of_eq fun p => ?_
    simp [WithBot.some_eq_coe]

/--
`findWitness?` is primitive recursive.
-/
lemma primrec₂_findWitness? : Primrec (fun a : ℕ × ℕ × FMStage => findWitness? a.1 a.2.1 a.2.2) := by
  refine Primrec.list_find? ?_ primrec₂_isWitness
  refine Primrec.list_product.comp ?_ ?_
  all_goals exact .comp .list_range (.comp .fst .snd)

/--
`extend` is primitive recursive.
-/
lemma primrec₂_extend : Primrec (fun a : ℕ × ℕ × FMStage => extend a.1 a.2.1 a.2.2) := by
  set A : Type := ℕ × ℕ × FMStage
  -- Projections on A
  have hi : Primrec (fun a : A => a.1) := .fst
  have hk : Primrec (fun a : A => a.2.1) := .comp .fst .snd
  have hp : Primrec (fun a : A => a.2.2.1) := .comp .fst (.comp .snd .snd)
  have hr : Primrec (fun a : A => a.2.2.2) := .comp .snd (.comp .snd .snd)
  -- The none branch: just return `s = (p, r)`
  have hnone : Primrec (fun a : A => a.2.2) := .comp .snd .snd
  -- The some branch: `some (e, y) => ((i, ⟪e, y⟫) :: p, r.takeI ⟪i, e⟫ ++ [WithBot.some k])`
  have hsome : Primrec₂ (fun (a : A) (x : ℕ × ℕ) =>
      ((a.1, ⟪x.1, x.2⟫) :: a.2.2.1, a.2.2.2.takeI ⟪a.1, x.1⟫ ++ [.some a.2.1])) := by
    have he : Primrec (fun b : A × (ℕ × ℕ) => b.2.1) := Primrec.fst.comp .snd
    have hy : Primrec (fun b : A × (ℕ × ℕ) => b.2.2) := Primrec.snd.comp .snd
    refine Primrec.pair ?_ ?_
    · refine Primrec.list_cons.comp ?_ (hp.comp .fst)
      exact Primrec.pair (hi.comp .fst) (Primrec₂.natPair.comp he hy)
    · refine Primrec.list_append.comp ?_ ?_
      · refine Primrec.list_takeI.comp (hr.comp .fst) ?_
        exact Primrec₂.natPair.comp (hi.comp .fst) he
      · refine Primrec.list_cons.comp ?_ (.const [])
        exact Primrec.option_some.comp (hk.comp .fst)
  -- Combine with option_casesOn
  refine (Primrec.option_casesOn primrec₂_findWitness? hnone hsome).of_eq fun ⟨i, k, s⟩ => ?_
  simp only [extend]
  cases findWitness? i k s with rfl

/--
Define the construction by invoking `extend` at each stage.

Note: `extend k.unpair.1 k.unpair.2 (stage k)` would also be valid.
This has the benefit of doing a little less pairing/unpairing. The consequence is that for each `i`, `extend i` is invoked with infinitely many `k`, not with all `k`. So we need to prove some kind of monotonicity fact at some point.
-/
def stage : ℕ → FMStage
  | 0 => ([], [])
  | k + 1 => extend k.unpair.1 k (stage k)

/--
The sequence of approximations of the RE predicates.
-/
def approx (k : ℕ) : List (ℕ × ℕ) := (stage k).1

/--
The sequence of approximations to the `i`th oracle, which is the oracle that will not be able to compute `fmPred i`. At the `k`th stage, we try to ensure `p.i` is not computable relative to `approxOracle i k`. Unlike `approx`, the elements of this list are already paired.
-/
def approxOracle (i k : ℕ) : List ℕ :=
  ((approx k).filter fun x => x.1 ≠ i).map Nat.pair.uncurry

/--
An alternative definition of `approxOracle`.
-/
lemma approxOracle_eq (i k : ℕ) :
    approxOracle i k = ((approx k).map Nat.pair.uncurry).filter fun x => x.unpair.1 ≠ i := by
  simp only [approxOracle, List.filter_map]
  congr
  funext x
  simp [Function.uncurry]

/--
For each `i`, `fmPred i : ℕ → Prop` is one of the predicates witnessing Friedberg-Muchnik.
-/
def fmPred (i x : ℕ) : Prop := ∃ k, (i, x) ∈ approx k

/--
For each `i`, `fmOracle i : ℕ → Prop` is the oracle obtained by zeroing out the `i`th predicate of `fmPred`.
-/
def fmOracle (i x : ℕ) : Prop := ∃ k, x ∈ approxOracle i k

/--
The restraint table. `res n m = some j` if the requirement corresponding to `n` was satisfied at an earlier stage `j < n`, and not injured since then. Otherwise, `res n m = ⊥`.
-/
def res (n m : ℕ) : WithBot ℕ := (stage n).2.getI m

@[simp]
lemma approx_zero : approx 0 = [] := rfl

@[simp]
lemma res_zero (n : ℕ) : res 0 n = ⊥ := rfl

/--
The sequence of approxiations is monotone.
-/
lemma approx_mono (n : ℕ) : approx n ⊆ approx (n+1) :=
  subset_extend

/--
Each sequence of oracle approxiations is monotone.
-/
lemma approxOracle_mono (i n : ℕ) : approxOracle i n ⊆ approxOracle i (n+1) :=
  List.map_subset _ (List.filter_subset _ (approx_mono n))

/--
`stage` is primitive recursive.
-/
lemma primrec_stage : Primrec stage := by
  -- step: (k, ih) => extend k.unpair.1 k ih
  have hstep : Primrec₂ fun k ih => extend k.unpair.1 k ih :=
    primrec₂_extend.comp <| .pair (.comp .fst (.comp .unpair .fst)) .id
  refine (Primrec.nat_rec₁ ([], []) hstep).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n IH => simp [stage, IH]

/--
`approx` is primitive recursive.
-/
lemma primrec_approx : Primrec approx :=
  Primrec.fst.comp primrec_stage

/--
`fmPred` is RE.
-/
lemma re_fmPred : REPred (fun x : ℕ × ℕ => fmPred x.1 x.2) :=
  re_of_primrec_seq primrec_approx

/--
Each `fmPred i` is RE.
-/
lemma re_fmPred_fiber (i : ℕ) : REPred (fmPred i) := by
  refine re_fmPred.comp_computable (?_ : Computable (i, ·))
  exact (Primrec.pair (.const i) .id).to_comp

lemma isWitness_iff {k x}
  : isWitness k.unpair.1 k (stage k) x
  ↔ res k ⟪k.unpair.1, x.1⟫ = ⊥
    ∧ (k.unpair.1, ⟪x.1, x.2⟫) ∉ approx k
    ∧ 0 ∈ (ofNat Code x.1).evaln k (fun a => if a ∈ approxOracle k.unpair.1 k then 1 else 0) ⟪x.1, x.2⟫
    ∧ ∀ n < ⟪k.unpair.1, x.1⟫, res k n < .some ⟪x.1, x.2⟫ := by
  simp [isWitness, res, approx]
  rintro - - -
  rw [iff_iff_eq]
  congr
  funext a
  simp [approxOracle, approx]
  congr
  simp [← ne_eq]
  constructor
  · intro ⟨ha, ha'⟩
    use a.unpair.1, a.unpair.2
    simp [ha']
    exact ha.symm
  · rintro ⟨a1, a2, ha, rfl⟩
    simp only [Nat.unpair_pair]
    exact ⟨ha.2.symm, ha.1⟩

/--
The two elements returned by `findWitness?` are always `< k`.
-/
lemma findWitness?_lt {i k : ℕ} {s : FMStage} {e y : ℕ} (hfw : findWitness? i k s = some (e, y)) : e < k ∧ y < k := by
  apply List.mem_of_find?_eq_some at hfw
  simp only [List.mem_product, List.mem_range] at hfw
  exact hfw

/--
Helper: values in `(extend i k s).2` at position `a < ⟪i, e⟫` are preserved from `s.2` when action occurs.
-/
lemma extend_snd_getI_lt {i k : ℕ} {s : FMStage} {e y a : ℕ}
    (h : findWitness? i k s = some (e, y)) (ha : a < ⟪i, e⟫) :
    (extend i k s).2.getI a = s.2.getI a := by
  simp only [extend, h]
  rw [List.getI_append _ _ _ (by rw [List.takeI_length]; exact ha)]
  exact List.getI_takeI s.2 ⟪i, e⟫ a ha

/--
Helper: value at position `⟪i, e⟫` of `(extend i k s).2` is `some k` when action occurs.
-/
lemma extend_snd_getI_eq {i k : ℕ} {s : FMStage} {e y : ℕ}
    (h : findWitness? i k s = some (e, y)) :
    (extend i k s).2.getI ⟪i, e⟫ = .some k := by
  simp only [extend, h]
  rw [List.getI_append_right _ _ _ (by rw [List.takeI_length])]
  rw [List.takeI_length]
  simp

/--
Helper: value at position `a > ⟪i, e⟫` of `(extend i k s).2` is `⊥` when action occurs.
-/
lemma extend_snd_getI_gt {i k : ℕ} {s : FMStage} {e y a : ℕ}
    (h : findWitness? i k s = some (e, y)) (ha : ⟪i, e⟫ < a) :
    (extend i k s).2.getI a = ⊥ := by
  simp only [extend, h]
  exact List.getI_eq_default _ (by simpa)

/--
Helper: `findWitness?` precondition gives `s.2.getI ⟪i, e⟫ = ⊥` when it returns `some (e, y)`.
-/
lemma findWitness?_some_getI_eq_none {i k : ℕ} {s : FMStage} {e y : ℕ}
    (h : findWitness? i k s = some (e, y)) :
    s.2.getI ⟪i, e⟫ = ⊥ := by
  unfold findWitness? isWitness at h
  have := List.find?_some h
  simp only [decide_eq_true_eq] at this
  exact this.1

/--
Helper: if all `some m` values in `u.2` satisfy `m ≤ k`, then the same holds for `(extend f k u).2`.
-/
lemma extend_snd_bound_le {i k : ℕ} {s : FMStage} {a m : ℕ}
    (h : s.2.getI a = .some m → m ≤ k)
    (hget : (extend i k s).2.getI a = .some m) : m ≤ k := by
  cases hfw : findWitness? i k s with
  | none =>
    have heq : (extend i k s).2 = s.2 := by simp [extend, hfw]
    rw [heq] at hget
    exact h hget
  | some p =>
    obtain ⟨e, y⟩ := p
    rcases lt_trichotomy a ⟪i, e⟫ with hi | rfl | hi
    · rw [extend_snd_getI_lt hfw hi] at hget
      exact h hget
    · rw [extend_snd_getI_eq hfw] at hget
      have : m = k := by injection hget with h; exact h.symm
      subst this; rfl
    · rw [extend_snd_getI_gt hfw hi] at hget
      contradiction

/--
Helper: any `some k` value in `res k` satisfies `m < k`.
-/
lemma res_lt_stage {k n m : ℕ} (h : res k n = .some m) : m < k := by
  induction k with
  | zero => contradiction
  | succ n IH =>
    apply Nat.lt_succ_of_le
    simp only [res, stage] at h
    refine extend_snd_bound_le (fun h' => ?_) h
    exact (IH h').le

/--
If `res (k+1) i = some m`, then either `m < k` and `res k i = some m`, or `m = k` and `res k i = none`.
-/
lemma res_lt_or_eq {k i e m : ℕ} (h : res (k+1) ⟪i, e⟫ = .some m)
    : (m < k ∧ res k ⟪i, e⟫ = .some m)
    ∨ (m = k ∧ res k ⟪i, e⟫ = ⊥ ∧ m.unpair.1 = i ∧ ∃ y, findWitness? i k (stage k) = some (e, y))
    := by
  have hm_le : m ≤ k := Nat.le_of_lt_succ (res_lt_stage h)
  rcases hfw : findWitness? k.unpair.1 k (stage k) with - | ⟨e', y⟩
  · left
    simp only [res, stage, extend, hfw] at h
    exact ⟨res_lt_stage h, h⟩
  · simp only [res, stage, extend, hfw] at h
    rcases lt_trichotomy ⟪i, e⟫ ⟪k.unpair.1, e'⟫ with hlt | heq | hgt
    · -- In this case `⟪i, e⟫` is not injured, so its value persists from the previous stage.
      left
      rw [List.getI_append_takeI_left _ _ hlt] at h
      exact ⟨res_lt_stage h, h⟩
    · -- This is the only case where we end up on right side of the disjunction.
      right
      simp only [Nat.pair_eq_pair] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp_all
      exact findWitness?_some_getI_eq_none hfw
    · -- This contradicts `h`, just by length considerations.
      rw [List.getI_eq_default _ ?_] at h
      · contradiction
      simp [Nat.succ_le_of_lt hgt]

/--
If `res k ⟪i,e⟫ = some m`, then this value was set at stage `m+1` and has persisted since then. Also, this gives some information about the result of `findWitness?` at that stage.
-/
lemma res_set_at_stage {k i e m : ℕ} (h : res k ⟪i, e⟫ = .some m)
    : (∀ n ∈ Set.Ioc m k, res n ⟪i, e⟫ = .some m) ∧ res m ⟪i, e⟫ = ⊥ ∧ m.unpair.1 = i
    ∧ ∃ y, findWitness? i m (stage m) = some (e, y) := by
  have hm : m < k := res_lt_stage h
  induction k, hm using Nat.le_induction with
  | base =>
    have := res_lt_or_eq h
    grind
  | succ k hk IH =>
    have : Set.Ioc m (k+1) = Set.Ioc m k ∪ {k+1} := by
      ext x; simp; omega
    rw [this]
    simp only [Set.union_singleton, Set.mem_insert_iff, forall_eq_or_imp, h, true_and]
    apply IH
    rcases res_lt_or_eq h with ⟨-, hres⟩ | ⟨rfl, -, -, -⟩
    · exact hres
    · omega

/--
This means that requirement `n` is stable starting at stage `k₀`, i.e., it is either satisfied and never again injured, or it is never set.
-/
abbrev IsStableAfter (n : ℕ) (k₀ : ℕ) : Prop := ∃ o, ∀ k ≥ k₀, res k n = o

/--
If strategy `n` is stable after `k₀`, then for all `k` we have `res k n < some k₀`.
-/
lemma res_lt_stage_of_stable {n k₀ : ℕ} (hstable : IsStableAfter n k₀) (k : ℕ) : res k n < .some k₀ := by
  obtain ⟨o, ho⟩ := hstable
  by_cases! hk : k ≥ k₀
  · rw [ho k hk, ← ho k₀ le_rfl]
    rcases hres : res k₀ n with - | j
    · simp [WithBot.none_eq_bot]
    · simp [WithBot.some_eq_coe]
      exact res_lt_stage hres
  · rcases hres : res k n with - | j
    · simp [WithBot.none_eq_bot]
    · simp [WithBot.some_eq_coe]
      exact lt_trans (res_lt_stage hres) hk

/--
If for all `m < n`, `res k m` is constant for `k ≥ k₀`, and if for some `k₁ ≥ k₀` we have `res k₁ n = some j`, then this value persists forever.
-/
lemma res_eq_some_of_stable_prefix {n k₀ k₁ j} (hk₀ : ∀ m < n, IsStableAfter m k₀) (hle : k₀ ≤ k₁) (hk₁ : res k₁ n = .some j) : ∀ k ≥ k₁, res k n = .some j := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hk₁
  | succ k hk IH =>
    -- The goal is to show `res (k+1) n = some j`. This is true because strategies `≤ n` cannot act at stage `k`.
    unfold res stage
    unfold res at IH
    set i := k.unpair.1
    rcases hfw : findWitness? i k (stage k) with - | ⟨e, y⟩
    · -- No strategy acts. Then we conclude immediately.
      simp [extend, hfw, IH]
    · -- Strategy `⟪i, e⟫` acts. It suffices to show `n < ⟪i, e⟫`.
      rwa [extend_snd_getI_lt hfw ?_]
      by_contra! hn
      rcases lt_or_eq_of_le hn with hn | rfl
      · -- `⟪i, e⟫ < n`: use stability + `res_lt_stage`.
        obtain ⟨o, ho⟩ := hk₀ ⟪i, e⟫ hn
        have hres_k := ho k (by omega)
        have hres_k1 := ho (k+1) (by omega)
        have heq : res (k+1) ⟪i, e⟫ = some k := extend_snd_getI_eq hfw
        rw [← hres_k1, heq] at hres_k
        exact lt_irrefl k (res_lt_stage hres_k)
      · -- `⟪i, e⟫ = n`: use induction hypothesis.
        rw [findWitness?_some_getI_eq_none hfw] at IH
        contradiction

/--
Each strategy is injured finitely many times. This is expressed by saying that for each index `m`, the function `fun k => res k m` is eventually constant.
-/
lemma finite_injury (n : ℕ) : ∃ k₀, ∀ m < n, IsStableAfter m k₀ := by
  induction n with
  | zero => simp
  | succ n IH =>
    obtain ⟨k₀, hk₀⟩ := IH
    -- Reduce to finding a `k₁ ≥ k₀` such that `res k n` is eventually constant.
    suffices ∃ k₁ ≥ k₀, ∃ o, ∀ k ≥ k₁, res k n = o by
      obtain ⟨k₁, hk₁, o, ho⟩ := this
      use k₁
      intro i hi_lt
      by_cases! hi_eq : i = n
      · subst hi_eq
        exact ⟨o, ho⟩
      · obtain ⟨o, ho⟩ := hk₀ i (by omega)
        use o
        grind
    -- The current strategy cannot be injured after step `k₀`, so the value changes at most one more time.
    by_cases! h : ∀ k ≥ k₀, res k n = ⊥
    · -- If for every `k ≥ k₀` the value is `none`, then we conclude immediately.
      exact ⟨k₀, le_refl k₀, ⊥, h⟩
    · -- Otherwise, we find a `k₁ ≥ k₀` where the value is `some j`, and this value persists forever by `res_eq_some_of_stable_prefix`.
      simp only [WithBot.ne_bot_iff_exists] at h
      obtain ⟨k₁, hle, j, hk₁⟩ := h
      exact ⟨k₁, hle, .some j, res_eq_some_of_stable_prefix hk₀ hle hk₁.symm⟩

open Filter

/--
This is a version/consequence of the use principle. If `s k` is an increasing sequence of lists, then a code `c` halts on input `n` given oracle `⋃ k, s k`, if and only if there is some `k₀` such that for all `i,k ≥ k₀`, `c` halts on input `n` in `< i` steps given oracle `s k`.

Remark: The right-to-left direction would be false if we replaced the right side with `∃ k₀, ∀ k ≥ k₀, ...`. A *uniform* bound on time is necessary.
-/
lemma eval_iff_eventually_evaln_of_tendsTo {c : Code} {f : ℕ → ℕ → ℕ} {g : ℕ → ℕ} (hlim : ∀ m, ∀ᶠ k in atTop, f k m = g m) {n x}
    : x ∈ c.eval g n
    ↔ ∃ k₀, ∀ t ≥ k₀, ∀ k ≥ k₀, x ∈ c.evaln t (f k) n := by
  have hlim' (t₀ : ℕ) : ∃ k₀, ∀ k ≥ k₀, ∀ m < t₀, f k m = g m := by
    simp [← eventually_atTop, Nat.forall_lt_iff_fin, eventually_all]
    exact fun ⟨i, _⟩ => hlim i
  rw [Code.evaln_complete]
  constructor
  · intro h
    obtain ⟨t₀, ht₀⟩ := h
    obtain ⟨k₀, hk₀⟩ := hlim' t₀
    use max t₀ k₀
    intro t ht k hk
    simp at ht hk
    apply Code.evaln_mono ht.1
    rwa [Code.evaln_eq_of_oracle_eq (hk₀ k hk.2)]
  · intro ⟨k₀, h⟩
    obtain ⟨k₁, hk₁⟩ := hlim' k₀
    use k₀
    rw [← Code.evaln_eq_of_oracle_eq (hk₁ _ (le_max_right _ _))]
    exact h _ le_rfl _ (le_max_left _ _)

open Classical in
/--
This is a version of `eval_iff_eventually_evaln_of_tendsTo` where the functions in the sequence are indicator functions of a monotone sequence of lists.
-/
lemma eval_iff_eventually_evaln_of_mono {c : Code} {s : ℕ → List ℕ} (hs : ∀ k, s k ⊆ s (k+1)) {n x}
    : x ∈ c.eval (ofPred fun y => ∃ k, y ∈ s k) n
    ↔ ∃ k₀, ∀ t ≥ k₀, ∀ k ≥ k₀, x ∈ c.evaln t (fun a => if a ∈ s k then 1 else 0) n := by
  apply eval_iff_eventually_evaln_of_tendsTo
  intro m
  rw [Filter.eventually_atTop, ofPred]
  by_cases h : ∃ k, m ∈ s k <;> simp [h]
  · obtain ⟨k₀, hk₀⟩ := h
    use k₀
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hk₀
    | succ k hk IH => exact hs k IH
  · push Not at h
    exact ⟨0, fun k _ => h k⟩

open Classical in
lemma eval_oracle_iff_eventually_evaln_approxOracle {c : Code} {i n x : ℕ}
    : x ∈ c.eval (ofPred (fmOracle i)) n
    ↔ ∃ k₀, ∀ t ≥ k₀, ∀ k ≥ k₀, x ∈ c.evaln t (fun a => if a ∈ approxOracle i k then 1 else 0) n :=
  eval_iff_eventually_evaln_of_mono (approxOracle_mono i)

lemma approx_eq_of_res_eventually_eq_some {n m} (h : ∀ k > m, res k n = .some m) : ∀ a ≤ m, ∀ k > m, a.unpair ∈ approx k ↔ a.unpair ∈ approx (m+1) := by
  intro a ha k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk IH =>
    rw [← IH]
    rcases hfw : findWitness? k.unpair.1 k (stage k) with - | ⟨e, y⟩
    · simp [approx, stage, extend, hfw]
    · simp [approx, stage, extend, hfw]
      have hiw := List.find?_some hfw
      simp [isWitness_iff, -Option.mem_def] at hiw
      obtain ⟨-, -, -, hbound⟩ := hiw
      rcases lt_trichotomy ⟪k.unpair.1, e⟫ n with hn_lt | hn_eq | hn_gt
      · have : res (k+1) n = ⊥ := by
          simp [res, stage, extend, hfw]
          rw [lt_iff_exists_add] at hn_lt
          obtain ⟨c, hc, rfl⟩ := hn_lt
          simp [List.getI, hc.ne', default]
        rw [h (k+1) (Nat.le_succ_of_le hk)] at this
        contradiction
      · have : res (k+1) n = .some k := by
          simp [res, stage, extend, hfw, hn_eq]
        rw [h (k+1) (by  omega), WithBot.coe_inj] at this
        omega
      · specialize hbound n hn_gt
        specialize h k hk
        rw [h] at hbound
        rw [WithBot.coe_lt_coe] at hbound
        intro h''
        apply congr_arg Nat.pair.uncurry at h''
        simp [Function.uncurry] at h''
        have : ⟪e, y⟫ ≤ a := by
          rw [h'']
          exact Nat.right_le_pair _ _
        omega

open Classical in
/--
If `res k ⟪i, e⟫` is eventually `⊥`, then there is some `x` such that `fmPred i x` does not hold, yet `e.eval (fmOracle i) x ≠ 0`. Thus `e` does not compute `fmPred i` using oracle `fmOracle i`.
-/
lemma res_bot {i e k₀ : ℕ} (hk₀ : ∀ k ≥ k₀, res k ⟪i, e⟫ = ⊥)
    : ∃ x, ¬fmPred i x ∧ 0 ∉ (ofNat Code e).eval (ofPred (fmOracle i)) x
    := by
  -- `v` is some stage after which no strategy `n < ⟪i, e⟫` acts.
  have ⟨v, hv⟩ := finite_injury ⟪i, e⟫
  have hres_lt {n : ℕ} (hn : n < ⟪i, e⟫) : ∀ k, res k n < .some v :=
    res_lt_stage_of_stable (hv n hn)
  -- `res k ⟪i, e⟫` cannot be `some j` at any stage `≥ v`.
  have hne_some {k j : ℕ} (hk : k ≥ v) : res k ⟪i, e⟫ ≠ some j := by
    intro hres
    have hk' := res_eq_some_of_stable_prefix hv hk hres
    specialize hk₀ (max k₀ k) (Nat.le_max_left _ _)
    specialize hk' (max k₀ k) (Nat.le_max_right _ _)
    rw [hk₀] at hk'
    contradiction
  -- The witness `x` is `⟪e, y⟫`, where `y` is any number `> v` such that `⟪e, y⟫ ∉ seq1 v`.
  have ⟨y, hy⟩ : ∃ y, v < y ∧ (i, ⟪e, y⟫) ∉ approx v := by
    -- (This proof should be easy, since the predicate defines a coinfinite set. But I am not sure how to tell this to lean.)
    set x := max v (((approx v).map (·.2.unpair.2)).max?.getD 0) + 1 with x_def
    refine ⟨x, lt_of_le_of_lt (le_max_left _ _) (Nat.lt_add_one _), fun h => ?_⟩
    have hx : x ∈ (approx v).map (·.2.unpair.2) := by
      convert List.mem_map_of_mem h; simp
    simp [List.max?_eq_some_max (List.ne_nil_of_mem hx)] at x_def
    have : x + 1 ≤ _ := Nat.succ_le_succ (List.le_max_of_mem hx)
    omega
  -- `⟪e, y⟫` is not enumerated into `p1`.
  have hnp : ¬fmPred i ⟪e, y⟫ := by
    -- Suppose otherwise. Let `k₁` be the stage where the enumeration occurs.
    intro henum
    set k₁ := Nat.find henum with k₁_def
    have hk₁ : (i, ⟪e, y⟫) ∈ approx k₁ := Nat.find_spec henum
    -- We know that `k₁` is a successor (since `approx 0 = []`), so we destructure it.
    rcases k₁ with - | k₁
    · contradiction
    have hk₁' : (i, ⟪e, y⟫) ∉ approx k₁ := Nat.find_min henum
      (by rw [← k₁_def]; apply Nat.lt_add_one)
    -- The fact that `(i, ⟪e, y⟫)` was enumerated at stage `k₁+1` implies that `⟪e, y⟫` is the result of `findWitness?` on stage `k₁`.
    have ⟨hfw, hi⟩ : findWitness? i k₁ (stage k₁) = (e, y) ∧ i = k₁.unpair.1 := by
      rcases h : findWitness? k₁.unpair.1 k₁ (stage k₁) <;>
        simp_all [approx, stage, extend]
    -- Also that `res (k₁+1) ⟪i, e⟫ = some k₁`.
    have hres : res (k₁+1) ⟪i, e⟫ = .some k₁ := by
      unfold res stage extend
      simp [hfw, ← hi]
    -- Since `v < y`, this enumeration must have happened at a stage `> v` (might have an off by one error here).
    have hle : v < k₁ := hy.1.trans (findWitness?_lt hfw).2
    -- Thus we contradict `hne_some`.
    exact hne_some (by omega) hres
  use ⟪e, y⟫, hnp
  -- Suppose `e.eval (fmOracle i) ⟪e, y⟫ = 0`.
  intro heval
  -- Then `e.evaln i (seq2 k) ⟪e, y⟫ = 0` for `i` and `k` sufficiently large.
  rw [eval_oracle_iff_eventually_evaln_approxOracle] at heval
  obtain ⟨k₁, heval⟩ := heval
  let K := ⟪i, max v k₁⟫
  have Kge : max v k₁ ≤ K := Nat.right_le_pair _ _
  specialize heval K (by omega) K (by omega)
  have he_lt : e < K :=
    lt_of_le_of_lt (Nat.left_le_pair e y) (Code.evaln_bound heval)
  have hy_lt : y < K :=
    lt_of_le_of_lt (Nat.right_le_pair e y) (Code.evaln_bound heval)
  -- If `res K ⟪i, e⟫ = some j`, we can conclude immediately using `hne_some`.
  rcases hres : res K ⟪i, e⟫ with - | j
  case some =>
    refine hne_some ?_ hres
    exact le_trans (le_max_left _ _) (Nat.right_le_pair _ _)
    -- exc
  -- If it is `none`, then we show `findWitness? i K (stage K) = some (e, y)`. First we show it satisfies `isWitness`.
  have hiw : isWitness i K (stage K) (e, y) := by
    simp [isWitness, -Option.mem_def]
    refine ⟨hres, ?_, ?_, ?_⟩
    · intro h; exact hnp ⟨_, h⟩
    · convert heval with a
      simp [approxOracle, approx, ← ne_eq]
      constructor
      · intro ⟨ha, ha'⟩
        use a.unpair.1, a.unpair.2
        simp [ha']
        exact ha.symm
      · rintro ⟨a1, a2, ha, rfl⟩
        simp only [Nat.unpair_pair]
        exact ⟨ha.2.symm, ha.1⟩
    · intro n hn
      refine lt_trans (hres_lt hn K) ?_
      rw [WithBot.coe_lt_coe]
      exact lt_of_lt_of_le hy.1 (Nat.right_le_pair _ _)
  have : (e, y) ∈ List.product (.range K) (.range K) := by
    rw [List.pair_mem_product, List.mem_range, List.mem_range]
    exact ⟨he_lt, hy_lt⟩
  have hfw := List.find?_isSome.mpr ⟨_, this, hiw⟩
  rw [Option.isSome_iff_exists] at hfw
  obtain ⟨⟨e', y'⟩, hfw : findWitness? _ _ _ = _⟩ := hfw
  obtain ⟨hiw', he', hy', hnw1, hnw2⟩ := List.find?_product_range.mp hfw
  rcases lt_trichotomy e e' with hlt | rfl | hgt
  · exact hnw1 e hlt y hy_lt hiw
  · have hres : res (K+1) ⟪i, e⟫ = .some K := by
      unfold res stage extend
      simp [hfw, K]
    exact hne_some (by omega) hres
  · have hres : res (K+1) ⟪i, e'⟫ = .some K := by
      unfold res stage extend
      simp [hfw, K]
    have := hres_lt (Nat.pair_lt_pair_right i hgt) (K+1)
    rw [hres, WithBot.coe_lt_coe] at this
    -- This contradicts the choice of `K ≥ v`.
    omega

open Classical in
/--
If `res k ⟪i, e⟫` is eventually `some m`, then there is some `x` such that `p.i x` holds, while `e.eval p.(≠ i) x = 0`. Thus `e` does not compute `p.i` using the oracle `p.(≠ i)`.
-/
lemma res_some {i e k₀ m : ℕ} (h : ∀ k ≥ k₀, res k ⟪i, e⟫ = .some m)
    : ∃ x, fmPred i x ∧ 0 ∈ (ofNat Code e).eval (ofPred (fmOracle i)) x
    := by
  -- The action must have occurred at stage `m`.
  obtain ⟨hm, -, rfl, y, hfw⟩ := res_set_at_stage (h k₀ le_rfl)
  -- Merge the interval `(m,k₀]` provided by `res_set_at_stage` with the interval `[k₀,∞)` provided by `h`.
  replace hm : ∀ k > m, res k ⟪m.unpair.1, e⟫ = .some m := by grind
  clear k₀ h
  have hfw_spec := List.find?_some hfw
  simp [isWitness_iff, -Option.mem_def] at hfw_spec
  obtain ⟨-, -, hevaln, -⟩ := hfw_spec
  -- The witness `x` is `⟪e, y⟫`.
  refine ⟨⟪e, y⟫, ?_, ?_⟩
  · -- Show `fmPred i ⟪e, y⟫` holds.
    use m + 1
    simp only [approx, stage, extend, hfw]
    exact List.mem_cons_self
  · -- Show `0 ∈ (ofNat Code e).eval (ofPred (fmOracle i)) ⟪e, y⟫` via the use principle.
    rw [eval_oracle_iff_eventually_evaln_approxOracle]
    use m
    intro t ht k hk
    apply Code.evalp_take at hevaln
    apply Code.evalp_mono ht at hevaln
    refine Code.evalp_mono_in_oracle ?_ hevaln
    simp [ht]
    rcases hk.lt_or_eq with hk_lt | rfl; swap
    · simp
    have : approxOracle m.unpair.1 (m+1) = approxOracle m.unpair.1 m := by
      simp [approxOracle, approx, stage, extend, hfw]
    rw [← this]
    intro n hn
    have := n.pair_unpair
    generalize n.unpair.1 = q, n.unpair.2 = q' at this
    subst this
    have := approx_eq_of_res_eventually_eq_some hm ⟪q,q'⟫ hn.le k hk_lt
    simp [approxOracle]
    simp at this
    simp [this]

open Classical in
/--
No `fmPred i` is Turing reducible to the join of the others (`fmOracle i`).
-/
lemma not_fmPred_le_fmOracle (i : ℕ) : ¬(ofPred (fmPred i) ≤ᵀ ofPred (fmOracle i)) := by
  rw [Code.exists_code, not_exists]
  intro c
  have hc := ofNat_encode c
  generalize Encodable.encode c = e at hc
  subst hc
  apply Function.ne_iff.mpr
  obtain ⟨k₀, hk₀⟩ := finite_injury (⟪i, e⟫ + 1)
  obtain ⟨o, ho⟩ := hk₀ ⟪i, e⟫ (Nat.lt_succ_self _)
  rcases o with - | j
  · obtain ⟨x, hx_neg, hx_ne0⟩ := res_bot ho
    use x
    simpa [ofPred, hx_neg, Part.eq_some_iff]
  · obtain ⟨x, hx_pos, hx_eq0⟩ := res_some ho
    use x
    simp [ofPred, hx_pos, Part.eq_some_iff]
    intro hx_eq1
    exact zero_ne_one (Part.mem_unique hx_eq0 hx_eq1)

/--
A family of functions is *mutually incomparable* if no function is Turing reducible to the join of the others.
-/
def MutuallyIncomparable (f : ℕ → ℕ → ℕ) : Prop :=
  ∀ i, ¬ f i ≤ᵀ (Nat.unpaired (Function.update f i fun _ => 0) : ℕ → ℕ)

/--
A family of functions is *pairwise incomparable* if no function is Turing reducible to another.
-/
def PairwiseIncomparable {α} (f : α → ℕ → ℕ) : Prop :=
  ∀ i j, i ≠ j → ¬ f i ≤ᵀ f j

lemma pairwiseIncomparable_of_mutuallyIncomparable {f : ℕ → ℕ → ℕ} (hf : MutuallyIncomparable f) : PairwiseIncomparable f := by
  intro i j hne hle
  refine hf i (hle.trans ?_)
  refine (TuringReducible.rfl.comp (?_ : Nat.Primrec (⟪j, ·⟫)).recursiveIn).of_eq ?_
  · exact Nat.Primrec.pair (Nat.Primrec.const j) Nat.Primrec.id
  · simp [hne.symm]

open Classical in
theorem mutuallyIncomparable_fmPred : MutuallyIncomparable (ofRel fmPred) := by
  unfold MutuallyIncomparable
  convert not_fmPred_le_fmOracle with i
  funext x
  by_cases hx1 : x.unpair.1 = i <;> simp [Function.update, ofRel, ofPred, fmOracle, fmPred, approxOracle_eq, Bool.toNat, hx1]
  congr
  funext k
  simp only [eq_iff_iff]
  refine ⟨?_, ?_⟩
  · intro h
    exact ⟨x.unpair.1, x.unpair.2, by simpa⟩
  · rintro ⟨a, b, h, rfl⟩
    simpa

open Classical in
/--
The **Friedberg-Muchnik Theorem**: there exists a mutually incomparable family of uniformly RE predicates.
-/
theorem exists_mutuallyIncomparable_rePreds : ∃ p : ℕ → ℕ → Prop, REPred (Nat.unpaired p) ∧ MutuallyIncomparable (ofRel p) :=
  ⟨ fmPred, re_fmPred, mutuallyIncomparable_fmPred ⟩

open Classical in
/--
This is the classical statement of Friedberg-Muchnik.
-/
theorem exists_two_incomparable_rePreds : ∃ p q : ℕ → Prop, REPred p ∧ REPred q ∧ ¬(ofPred p ≤ᵀ ofPred q) ∧ ¬(ofPred q ≤ᵀ ofPred p) :=
  have h := pairwiseIncomparable_of_mutuallyIncomparable mutuallyIncomparable_fmPred
  ⟨ fmPred 0, fmPred 1,
    re_fmPred_fiber 0, re_fmPred_fiber 1,
    h 0 1 Nat.zero_ne_one, h 1 0 Nat.one_ne_zero ⟩

end Computability.FriedbergMuchnik
