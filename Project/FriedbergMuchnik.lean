module

public import Mathlib.Computability.Halting
public import Mathlib.Data.List.GetD
public import Project.OracleCode
public import Project.Queries
public import Project.Substitute
public import Project.PartrecCode


namespace List

/-
TODO: move list helper lemmas to a different file?
-/

/--
Helper: if `i < n`, then `(l.takeI n).getI i = l.getI i`.
-/
private lemma getI_takeI {α : Type*} [Inhabited α] :
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

namespace Computability

open RecursiveIn Denumerable

-- TODO: Why are the following instances not in mathlib?

instance {α} [LE α] [DecidableLE α] : DecidableLE (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

instance {α} [LT α] [DecidableLT α] : DecidableLT (Option α) := fun a b => by
  cases a <;> cases b <;> simp <;> infer_instance

/--
See `extend` for a description of the parameters.
-/
def findWitness? (f : ℕ → ℕ) (k : ℕ) : (List ℕ × List ℕ) × List (Option ℕ) → Option (ℕ × ℕ) := fun (p, r) =>
  -- `List.Product` is ordered so that this checks all `y`-values for `e = 0`, then all `y`-values for `e = 1`, and so on.
  List.product (.range k) (.range k) |>.find? fun (e, y) =>
    let x := Nat.pair e y
    -- We need the requirement `Rₑ` to not already be satisfied, as well as a witness `x` such that:
    -- (1) `x` is not already enumerated into `p.1`,
    -- (2) the eval of the code encoded by `e` with oracle `p.2` halts in `< k` steps and outputs `x`, and
    -- (3) `r[i] < x` for every `i < f e`.
    (r.getI (f e)).isNone
      ∧ x ∉ p.1
      ∧ 0 ∈ ((ofNat Code e).substPartrec (.listMem p.2)).evaln k x
      ∧ ∀ i < f e, r.getI i < x

/--
The roles of the parameters are as follows:
* `p = (p.1, p.2)` : The pair of finite sets (represented as lists) enumerated so far. In this stage, we are trying to ensure that `p.1` is not computable relative to `p.2`.
* `k` : A bound on (1) the number of codes to check at this stage, (2) the number of witnesses to check at this stage, and (3) the number of steps to run `evaln` at this stage.
* `f` : The index from a code into the restraint list `r`.
* `r` : The list of restraints. `r[f e] = none` (or the index is out of bounds) if requirement `Rₑ` is not currently satisfied. `r[f e] = some j'` if requirement `Rₑ` has been satisfied at some earlier stage `j < k`, and has not been injured since then.
-/
def extend (f : ℕ → ℕ) (k : ℕ) : (List ℕ × List ℕ) × List (Option ℕ) → (List ℕ × List ℕ) × List (Option ℕ) := fun (p, r) =>
  match findWitness? f k (p, r) with
  -- If no strategy needs to act, then do nothing.
  | none => (p, r)
  -- If `Rₑ` needs to act, then add the witness to `p.1`. Also, injure all strategies `Rᵢ` for `i > f e`, and set `r[f e] = some k`.
  | some (e, y) => ((Nat.pair e y :: p.1, p.2), r.takeI (f e) ++ [some k])

lemma extend_fst {f k u} : u.1.1 ⊆ (extend f k u).1.1 := by
  simp only [extend]
  cases findWitness? f k u with simp

lemma extend_snd {f k u} : (extend f k u).1.2 = u.1.2 := by
  simp only [extend]
  cases findWitness? f k u with rfl

/-!
### Helper primrec lemmas

The following three lemmas are standard facts that are not (yet) in Mathlib:
primitive recursiveness of `List.takeI`, `List.product`, and a binary version of
`List.find?`. They are held as `sorry` so the main proofs below may depend on them.
-/

private theorem Primrec.list_takeI {α : Type*} [Inhabited α] [Primcodable α] :
    Primrec₂ (fun (l : List α) (n : ℕ) => l.takeI n) := by
  -- Use the equivalent formulation: `l.takeI n = (List.range n).map (fun i => l.getI i)`.
  have h : Primrec (fun (p : List α × ℕ) => (List.range p.2).map (fun i => p.1.getI i)) := by
    apply Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    exact Primrec.list_getI.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  refine h.to₂.of_eq fun l n => ?_
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.takeI_length]
  · intro i _ hi
    rw [List.getElem_map, List.getElem_range]
    rw [List.takeI_length] at hi
    rw [← List.getI_eq_getElem _ (by rw [List.takeI_length]; exact hi)]
    exact (List.getI_takeI l n i hi).symm

private theorem Primrec.list_product' {α β : Type*} [Primcodable α] [Primcodable β] :
    Primrec₂ (List.product : List α → List β → List (α × β)) := by
  -- `List.product l₁ l₂ = l₁.flatMap (fun a => l₂.map (Prod.mk a))`.
  refine Primrec.list_flatMap .fst ?_
  refine Primrec.list_map (.comp .snd .fst) ?_
  exact Primrec.pair (.comp .snd .fst) .snd

private theorem Primrec.list_find?' {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α → List β} {p : α → β → Bool}
    (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => (f a).find? (p a)) := by
  -- Use the equivalence `l.find? p = l[l.findIdx p]?`.
  have h_idx : Primrec (fun a => (f a).findIdx (p a)) := Primrec.list_findIdx hf hp
  have h_get : Primrec (fun a => (f a)[(f a).findIdx (p a)]?) :=
    Primrec.list_getElem?.comp hf h_idx
  refine h_get.of_eq fun a => ?_
  -- Show: (f a)[(f a).findIdx (p a)]? = (f a).find? (p a)
  generalize (f a) = l
  generalize (p a) = q
  clear hf hp h_idx h_get f p
  induction l with
  | nil => rfl
  | cons b t IH =>
    by_cases hb : q b
    · simp [List.findIdx_cons, hb]
    · simp [List.findIdx_cons, hb]
      exact IH

/--
`findWitness?` is primitive recursive (if the indexing function is).
The structure is: apply `list_find?'` to the Cartesian product `range k × range k`, with
a predicate combining (isNone restraint) ∧ (witness not yet enumerated) ∧ (evaln halts to 0)
∧ (bounded restraint check). The predicate composition runs into typeclass resolution
timeouts, so we hold the proof as `sorry` pending optimisation.
-/
lemma primrec₂_findWitness? {f} (hf : Primrec f) : Primrec₂ (findWitness? f) := by
  refine Primrec.list_find?' ?_ ?_
  · exact Primrec.list_product'.comp
      (.comp .list_range .fst) (.comp .list_range .fst)
  · simp only [Option.isNone_iff_eq_none, Option.mem_def, Bool.decide_and, decide_not]
    refine Primrec.and.comp ?_ (Primrec.and.comp ?_ (Primrec.and.comp ?_ ?_))
    · sorry
    · sorry
    · sorry
    · sorry

/--
`extend` is primitive recursive (if the indexing function is).
-/
lemma primrec₂_extend {f} (hf : Primrec f) : Primrec₂ (extend f) := by
  set A : Type := ℕ × (List ℕ × List ℕ) × List (Option ℕ)
  -- Projections on A
  have hk : Primrec (Prod.fst : A → ℕ) := Primrec.fst
  have hp : Primrec (fun a : A => a.2.1) := Primrec.fst.comp .snd
  have hp1 : Primrec (fun a : A => a.2.1.1) := Primrec.fst.comp hp
  have hp2 : Primrec (fun a : A => a.2.1.2) := Primrec.snd.comp hp
  have hr : Primrec (fun a : A => a.2.2) := Primrec.snd.comp .snd
  -- findWitness? as Primrec
  have hfw : Primrec (fun a : A => findWitness? f a.1 a.2) := primrec₂_findWitness? hf
  -- The none branch: just return (p, r)
  have hnone : Primrec (fun a : A => a.2) := Primrec.snd
  -- The some branch: (a, (e, y)) ↦ ((Nat.pair e y :: p.1, p.2), r.takeI (f e) ++ [some k])
  -- Let B := ℕ × ℕ. Input type for g is A × B.
  have hsome : Primrec₂ (fun (a : A) (ey : ℕ × ℕ) =>
      ((Nat.pair ey.1 ey.2 :: a.2.1.1, a.2.1.2), a.2.2.takeI (f ey.1) ++ [some a.1])) := by
    -- Projections on A × B
    have he : Primrec (fun ab : A × (ℕ × ℕ) => ab.2.1) := Primrec.fst.comp .snd
    have hy : Primrec (fun ab : A × (ℕ × ℕ) => ab.2.2) := Primrec.snd.comp .snd
    refine Primrec.pair ?_ ?_
    · refine Primrec.pair ?_ (hp2.comp .fst)
      refine Primrec.list_cons.comp ?_ (hp1.comp .fst)
      exact Primrec₂.natPair.comp he hy
    · refine Primrec.list_append.comp ?_ ?_
      · exact Primrec.list_takeI.comp (hr.comp .fst) (hf.comp he)
      · refine Primrec.list_cons.comp ?_ (.const [])
        exact Primrec.option_some.comp (hk.comp .fst)
  -- Combine with option_casesOn
  refine (Primrec.option_casesOn hfw hnone hsome).of_eq fun ⟨k, p, r⟩ => ?_
  simp only [extend]
  cases findWitness? f k (p, r) with rfl

/--
Having defined the `extend` function, we can build the increasing sequence of finite sets easily.
Note that `extend` is invoked on `(p.1, p.2)` using the indexing function `2 * ·`, and then on `(p.2, p.1)` using the indexing function `2 * · + 1`.
-/
def seq : ℕ → (List ℕ × List ℕ) × List (Option ℕ)
  | 0 => (([], []), [])
  | k + 1 =>
    Prod.map .swap id <|
    extend (2 * · + 1) k <|
    Prod.map .swap id <|
    extend (2 * ·) k <|
    seq k

def seq1 (k : ℕ) := (seq k).1.1

def seq2 (k : ℕ) := (seq k).1.2

def p1 (x : ℕ) : Prop := ∃ k, x ∈ seq1 k

def p2 (x : ℕ) : Prop := ∃ k, x ∈ seq2 k

/--
The restraint table. `res k n = some j` if the requirement corresponding to `n` was satisfied at an earlier stage `j < k`, and not injured since then.
-/
def res (k : ℕ) (n : ℕ) : Option ℕ := (seq k).2.getI n

/--
`seq1` is monotone.
-/
lemma seq1_mono (k : ℕ) : seq1 k ⊆ seq1 (k + 1) := by
  simp [seq1, seq, extend_fst, extend_snd]

/--
`seq2` is monotone.
-/
lemma seq2_mono (k : ℕ) : seq2 k ⊆ seq2 (k + 1) := by
  simp only [seq2, seq, Prod.map]
  exact List.Subset.trans (by simp [extend_snd]) extend_fst

/--
`seq` is primitive recursive.
-/
lemma primrec_seq : Primrec seq := by
  -- Prod.map Prod.swap id is primrec: ((a, b), c) ↦ ((b, a), c)
  have hswap : Primrec (Prod.map Prod.swap id :
      (List ℕ × List ℕ) × List (Option ℕ) → (List ℕ × List ℕ) × List (Option ℕ)) :=
    .pair (.pair (.comp .snd .fst) (.comp .fst .fst)) .snd
  have hf1 : Primrec (2 * ·) := Primrec.nat_mul.comp (.const 2) .id
  have hf2 : Primrec (2 * · + 1) := Primrec.succ.comp hf1
  -- step: (k, prev) ↦ Prod.map .swap id (extend (2*·+1) k (Prod.map .swap id (extend (2*·) k prev)))
  have hstep := hswap.comp
    ((primrec₂_extend hf2).comp Primrec.fst
      (hswap.comp ((primrec₂_extend hf1).comp Primrec.fst Primrec.snd)))
  refine (Primrec.nat_rec₁ (([], []), []) hstep.to₂).of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n IH => rw [seq, ← IH]

/--
`seq1` is primitive recursive.
-/
lemma primrec_seq1 : Primrec seq1 :=
  Primrec.fst.comp (Primrec.fst.comp primrec_seq)

/--
`seq2` is primitive recursive.
-/
lemma primrec_seq2 : Primrec seq2 :=
  Primrec.snd.comp (Primrec.fst.comp primrec_seq)

/--
If a sequence `s : ℕ → List ℕ` is primitive recursive, then the predicate `fun n => ∃ k, n ∈ s k` is RE.
-/
lemma re_of_primrec_seq {s : ℕ → List ℕ} (hs : Primrec s) : REPred (fun x => ∃ k, x ∈ s k) := by
  -- `x ∈ l` is a primitive recursive relation in `(l, x)`.
  have hmem_list : PrimrecRel (fun (l : List ℕ) (x : ℕ) => x ∈ l) :=
    Primrec.eq.exists_mem_list.of_eq fun l b => ⟨fun ⟨_, ha, rfl⟩ => ha, fun h => ⟨b, h, rfl⟩⟩
  have hmem_seq : PrimrecRel (fun x k => x ∈ s k) :=
    hmem_list.comp (hs.comp Primrec.snd) Primrec.fst
  have hpartrec : Partrec₂ fun x k => Part.some (decide (x ∈ s k)) :=
    hmem_seq.decide.to₂.to_comp.partrec₂
  -- Nat.rfind (fun k => Part.some (decide (x ∈ s k))) has domain p1 x
  refine (Partrec.rfind hpartrec).dom_re.of_eq fun x => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff]
  constructor
  · rintro ⟨k, hk, -⟩; exact ⟨k, decide_eq_true_iff.mp hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk], fun _ => trivial⟩

/--
The predicate `p1` is RE.
-/
lemma re_p1 : REPred p1 := re_of_primrec_seq primrec_seq1

/--
The predicate `p2` is RE.
-/
lemma re_p2 : REPred p2 := re_of_primrec_seq primrec_seq2

/--
Helper: values in `(extend f k u).2` at position `i < f e` are preserved from `u.2` when action occurs.
-/
lemma extend_snd_getI_lt {f : ℕ → ℕ} {k : ℕ}
    {u : (List ℕ × List ℕ) × List (Option ℕ)} {e y i : ℕ}
    (h : findWitness? f k u = some (e, y)) (hi : i < f e) :
    (extend f k u).2.getI i = u.2.getI i := by
  simp only [extend, h]
  rw [List.getI_append _ _ _ (by rw [List.takeI_length]; exact hi)]
  exact List.getI_takeI u.2 (f e) i hi

/--
Helper: value at position `f e` of `(extend f k u).2` is `some k` when action occurs.
-/
lemma extend_snd_getI_eq {f : ℕ → ℕ} {k : ℕ}
    {u : (List ℕ × List ℕ) × List (Option ℕ)} {e y : ℕ}
    (h : findWitness? f k u = some (e, y)) :
    (extend f k u).2.getI (f e) = some k := by
  simp only [extend, h]
  rw [List.getI_append_right _ _ _ (by rw [List.takeI_length])]
  rw [List.takeI_length]
  simp

/--
Helper: value at position `i > f e` of `(extend f k u).2` is `none` when action occurs.
-/
lemma extend_snd_getI_gt {f : ℕ → ℕ} {k : ℕ}
    {u : (List ℕ × List ℕ) × List (Option ℕ)} {e y i : ℕ}
    (h : findWitness? f k u = some (e, y)) (hi : f e < i) :
    (extend f k u).2.getI i = none := by
  simp only [extend, h]
  have hlen : (u.2.takeI (f e) ++ [some k]).length ≤ i := by
    rw [List.length_append, List.takeI_length, List.length_singleton]
    omega
  exact List.getI_eq_default _ hlen

/--
Helper: `findWitness?` precondition gives `u.2.getI (f e) = none` when it returns `some (e, y)`.
-/
lemma findWitness?_some_getI_eq_none {f : ℕ → ℕ} {k : ℕ}
    {u : (List ℕ × List ℕ) × List (Option ℕ)} {e y : ℕ}
    (h : findWitness? f k u = some (e, y)) :
    u.2.getI (f e) = none := by
  unfold findWitness? at h
  have := List.find?_some h
  simp only [decide_eq_true_eq] at this
  obtain ⟨hnone, _, _, _⟩ := this
  exact Option.isNone_iff_eq_none.mp hnone

/--
Helper: if all `some m` values in `u.2` satisfy `m ≤ k`, then the same holds for `(extend f k u).2`.
-/
lemma extend_snd_bound_le {f k u}
    (i m : ℕ)
    (h : u.2.getI i = some m → m ≤ k)
    (hget : (extend f k u).2.getI i = some m) : m ≤ k := by
  cases hfw : findWitness? f k u with
  | none =>
    have heq : (extend f k u).2 = u.2 := by simp [extend, hfw]
    rw [heq] at hget
    exact h hget
  | some p =>
    obtain ⟨e, y⟩ := p
    rcases lt_trichotomy i (f e) with hi | hi | hi
    · rw [extend_snd_getI_lt hfw hi] at hget
      exact h hget
    · subst hi
      rw [extend_snd_getI_eq hfw] at hget
      have : m = k := by injection hget with h; exact h.symm
      subst this; rfl
    · rw [extend_snd_getI_gt hfw hi] at hget
      contradiction

/--
Helper: any `some m` value in `res k` satisfies `m < k`.
-/
lemma res_lt_stage (k i m : ℕ) (h : res k i = some m) : m < k := by
  induction k with
  | zero => contradiction
  | succ k IH =>
    apply Nat.lt_succ_of_le
    simp only [res, seq, Prod.map_snd, id_eq] at h
    refine extend_snd_bound_le i m (fun h1 => ?_) h
    refine extend_snd_bound_le i m (fun h2 => ?_) h1
    exact (IH i m h2).le
    exact (IH h2).le

/--
Each strategy is injured finitely many times. This is expressed by saying that for each index `i`, the function `fun k => res k i` is eventually constant.
-/
lemma finite_injury (n : ℕ) : ∃ k₀, ∀ i < n, ∃ o, ∀ k ≥ k₀, res k i = o := by
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
    -- If for every `k ≥ k₀` the value is `none`, then we conclude immediately.
    by_cases! h : ∀ k ≥ k₀, res k n = none
    · exact ⟨k₀, le_refl k₀, none, h⟩
    -- Otherwise, we find a `k₁ ≥ k₀` where the value is `some j`, and we must show this value persists forever.
    simp only [Option.ne_none_iff_exists'] at h
    obtain ⟨k₁, hk₁, j, hj⟩ := h
    use k₁, hk₁, some j
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact hj
    | succ k hk IH =>
      -- The goal is to show `res (k+1) n = some j`. This is true because no
      -- action in either `extend` call at stage `k` can occur at position
      -- `≤ n`, and hence both calls preserve position `n`.
      have k_ge : k ≥ k₀ := le_trans hk₁ hk
      have k1_ge : k+1 ≥ k₀ := Nat.le_succ_of_le k_ge
      -- `k` doesn't appear as a value in `res k`.
      have no_k_in_r₀ (i : ℕ) : res k i ≠ some k :=
        fun hi => lt_irrefl k (res_lt_stage k i k hi)
      -- Unfold seq (k+1).
      have hseq : seq (k+1) = _ := seq.eq_2 k
      simp only [res, seq, Prod.map_snd, id_eq]
      -- Introduce the two extend stages.
      set u₀ := seq k with hu₀
      set u₁ := extend (2 * ·) k u₀ with hu₁
      set u₂ := Prod.map Prod.swap id u₁ with hu₂
      have hr₀n : u₀.2.getI n = some j := IH
      -- Show u₁.2.getI n = some j: first extend preserves position n.
      have hr₁n : u₁.2.getI n = some j := by
        rw [hu₁]
        rcases hfw : findWitness? (2 * ·) k u₀ with - | ⟨e, y⟩
        · simp [extend, hfw, hr₀n]
        · -- Position 2e: action occurs at 2e. Reduce to showing 2e > n.
          rwa [extend_snd_getI_lt hfw ?_]
          by_contra! hle
          rcases lt_or_eq_of_le hle with h2e_lt | rfl
          · -- 2e < n: use stability + no_k_in_r₀.
            obtain ⟨o, ho⟩ := hk₀ (2 * e) h2e_lt
            have hres_k : res k (2 * e) = o := ho k k_ge
            have hres_k1 : res (k+1) (2 * e) = o := ho (k+1) k1_ge
            -- After extend at stage k, value at 2e should appear as some k somewhere.
            -- Position 2e in u₁ is some k. But this intermediate state is not `seq`.
            -- We trace through second extend:
            -- Either second extend doesn't act, or acts at some 2e'+1.
            -- In either sub-case, the final value at some position ≤ n is some k,
            -- contradicting no_k_in_r₀ via stability.
            have h1 : u₁.2.getI (2 * e) = some k := extend_snd_getI_eq hfw
            rcases hfw2 : findWitness? (2 * · + 1) k u₂ with - | ⟨e', y'⟩
            · -- r₃ = r₂ = r₁. So r₃.getI (2e) = some k. But res (k+1) (2e) = o = r₃.getI (2e).
              have heq : res (k+1) (2 * e) = some k := by
                simp only [res, hseq, extend, hfw2]
                exact h1
              rw [heq] at hres_k1
              rw [← hres_k1] at hres_k
              exact no_k_in_r₀ (2 * e) hres_k
            · -- Second extend acts at 2e'+1. Position 2e+1's role vs 2e depends on ordering.
              by_cases! hord : 2 * e < 2 * e' + 1
              · -- 2e' + 1 > 2e, so position 2e is preserved in r₃.
                have heq : res (k+1) (2 * e) = some k := by
                  simp only [res, hseq, Prod.map_snd, id_eq, extend_snd_getI_lt hfw2 hord]
                  exact h1
                rw [heq] at hres_k1
                rw [← hres_k1] at hres_k
                exact no_k_in_r₀ (2 * e) hres_k
              · -- 2e'+1 ≤ 2e, but different parity so 2e'+1 < 2e.
                -- Second extend acts at 2e'+1 < 2e < n. Apply stability at 2e'+1.
                obtain ⟨o', ho'⟩ := hk₀ (2 * e' + 1) (hord.trans_lt h2e_lt)
                have hres'_k : res k (2 * e' + 1) = o' := ho' k k_ge
                have hres'_k1 : res (k+1) (2 * e' + 1) = o' := ho' (k+1) k1_ge
                -- res (k+1) (2e'+1) = some k (it's where second extend just acted)
                have heq : res (k+1) (2 * e' + 1) = some k :=
                  extend_snd_getI_eq hfw2
                rw [heq] at hres'_k1
                rw [← hres'_k1] at hres'_k
                exact no_k_in_r₀ (2 * e' + 1) hres'_k
          · -- 2e = n
            -- findWitness? required u₀.2.getI (2e) = u₀.2.getI n = none.
            rw [findWitness?_some_getI_eq_none hfw] at hr₀n
            contradiction
      -- Now show second extend preserves position n.
      have hr₂n : u₂.2.getI n = some j := hr₁n
      rcases hfw2 : findWitness? (2 * · + 1) k u₂ with - | ⟨e, y⟩
      · simp [extend, hfw2, hr₂n]
      · rwa [extend_snd_getI_lt hfw2 ?_]
        by_contra! hle
        rcases lt_or_eq_of_le hle with h_lt | rfl
        · -- 2e+1 < n.
          obtain ⟨o, ho⟩ := hk₀ (2 * e + 1) h_lt
          have hres_k : res k (2 * e + 1) = o := ho k k_ge
          have hres_k1 : res (k+1) (2 * e + 1) = o := ho (k+1) k1_ge
          have heq : res (k+1) (2 * e + 1) = some k :=
            extend_snd_getI_eq hfw2
          rw [heq] at hres_k1
          rw [← hres_k1] at hres_k
          exact no_k_in_r₀ (2 * e + 1) hres_k
        · -- 2e+1 = n.
          rw [findWitness?_some_getI_eq_none hfw2] at hr₂n
          contradiction

/--
Convert a predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [DecidablePred p] : α → ℕ :=
  fun a => (decide (p a)).toNat

open Classical in
/--
If `res k (2 * e)` is eventually `none`, then there is some `x` such that `p1 x` does not hold, yet `e.eval p2 x ≠ 0`. Thus `e` does not compute `p1` using the oracle `p2`.
-/
lemma res_none_even {e k₀ : ℕ} (h : ∀ k ≥ k₀, res k (2 * e) = none)
    : ∃ x, ¬ p1 x ∧ (ofNat Code e).eval (ofPred p2) x ≠ 0
    := by
  sorry

open Classical in
/--
See `res_none_even`.
TODO: can we do without so much duplication for the even/odd cases?
-/
lemma res_none_odd {e k₀ : ℕ} (h : ∀ k ≥ k₀, res k (2 * e + 1) = none)
    : ∃ x, ¬ p2 x ∧ (ofNat Code e).eval (ofPred p1) x ≠ 0
    := by
  sorry

open Classical in
/--
If `res k (2 * e)` is eventually `some j`, then there is some `x` such that `p1 x` holds, while `e.eval p2 x = 0`. Thus `e` does not compute `p1` using the oracle `p2`.
-/
lemma res_some_even {e k₀ j : ℕ} (h : ∀ k ≥ k₀, res k (2 * e) = some j)
    : ∃ x, p1 x ∧ (ofNat Code e).eval (ofPred p2) x = 0 :=
  sorry

open Classical in
/--
See `res_some_even`.
TODO: can we do without so much duplication for the even/odd cases?
-/
lemma res_some_odd {e k₀ j : ℕ} (h : ∀ k ≥ k₀, res k (2 * e + 1) = some j)
    : ∃ x, p2 x ∧ (ofNat Code e).eval (ofPred p1) x = 0 :=
  sorry

open Classical in
/--
The **Friedberg-Muchnik Theorem**: there exist two Turing-incomparable RE predicates.
-/
theorem exists_incomparable_rePreds : ∃ p q : ℕ → Prop, REPred p ∧ REPred q ∧ ¬(ofPred p ≤ᵀ ofPred q) ∧ ¬(ofPred q ≤ᵀ ofPred p) := by
  use p1, p2, re_p1, re_p2
  simp only [Code.exists_code, not_exists]
  refine ⟨fun c => ?_, fun c => ?_⟩
  · -- Goal: eval c (ofPred p2) ≠ ofPred p1
    apply Function.ne_iff.mpr
    let e := Encodable.encode c
    have hce : ofNat Code e = c := ofNat_encode c
    obtain ⟨k₀, hk₀⟩ := finite_injury (2 * e + 1)
    obtain ⟨o, ho⟩ := hk₀ (2 * e) (Nat.lt_succ_self _)
    rcases o with - | j
    · obtain ⟨x, hx_neg, hx_ne⟩ := res_none_even ho
      use x
      simpa [← hce, ofPred, hx_neg]
    · obtain ⟨x, hx_pos, hx_eq⟩ := res_some_even ho
      use x
      simp [← hce, hx_eq, ofPred, hx_pos]
      exact fun h => Nat.zero_ne_one (Part.some_inj.mp h)
  · -- Symmetric argument for the other direction
    apply Function.ne_iff.mpr
    let e := Encodable.encode c
    have hce : ofNat Code e = c := ofNat_encode c
    obtain ⟨k₀, hk₀⟩ := finite_injury (2 * e + 2)
    obtain ⟨o, ho⟩ := hk₀ (2 * e + 1) (Nat.lt_succ_self _)
    rcases o with - | j
    · obtain ⟨x, hx_neg, hx_ne⟩ := res_none_odd ho
      use x
      simpa [← hce, ofPred, hx_neg]
    · obtain ⟨x, hx_pos, hx_eq⟩ := res_some_odd ho
      use x
      simp [← hce, hx_eq, ofPred, hx_pos]
      exact fun h => Nat.zero_ne_one (Part.some_inj.mp h)

end Computability
