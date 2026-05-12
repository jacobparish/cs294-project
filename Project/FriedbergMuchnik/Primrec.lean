module

public import Project.FriedbergMuchnik.Defs
public import Project.Primrec
public import Project.RE

@[expose] public section

namespace Computability.FriedbergMuchnik

open Nat.RecursiveIn Denumerable

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

end Computability.FriedbergMuchnik

end
