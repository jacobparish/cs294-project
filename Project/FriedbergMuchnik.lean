module

public import Mathlib.Computability.Halting
public import Mathlib.Data.List.GetD
public import Project.OracleCode
public import Project.Queries
public import Project.Substitute
public import Project.PartrecCode

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

lemma extend_fst (f : ℕ → ℕ) (k : ℕ) (u : (List ℕ × List ℕ) × List (Option ℕ)) : u.1.1 ⊆ (extend f k u).1.1 := by
  simp only [extend]
  cases findWitness? f k u with simp

lemma extend_snd (f : ℕ → ℕ) (k : ℕ) (u : (List ℕ × List ℕ) × List (Option ℕ)) : u.1.2 = (extend f k u).1.2 := by
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
  -- Inline auxiliary lemma: `(l.takeI n).getI i = l.getI i` for `i < n`.
  have getI_takeI : ∀ (l : List α) (n i : ℕ), i < n → (l.takeI n).getI i = l.getI i := by
    intro l n
    induction n generalizing l with
    | zero => intro i hi; omega
    | succ n IH =>
      intro i hi
      cases l with
      | nil =>
        rw [List.takeI_nil, List.getI_nil]
        have hlen : i < (List.replicate (n+1) (default : α)).length := by
          rw [List.length_replicate]; exact hi
        rw [List.getI_eq_getElem _ hlen]; simp
      | cons a xs =>
        cases i with
        | zero => rfl
        | succ i =>
          show (a :: xs.takeI n).getI (i+1) = _
          rw [List.getI_cons_succ, List.getI_cons_succ]
          exact IH xs i (Nat.lt_of_succ_lt_succ hi)
  refine h.to₂.of_eq fun l n => ?_
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, List.takeI_length]
  · intro i _ hi
    rw [List.getElem_map, List.getElem_range]
    rw [List.takeI_length] at hi
    rw [← List.getI_eq_getElem _ (by rw [List.takeI_length]; exact hi)]
    exact (getI_takeI l n i hi).symm

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
  sorry

/--
`extend` is primitive recursive (if the indexing function is).
-/
lemma primrec₂_extend {f} (hf : Primrec f) : Primrec₂ (extend f) := by
  -- extend f k (p, r) =
  --   match findWitness? f k (p, r) with
  --   | none => (p, r)
  --   | some (e, y) => ((Nat.pair e y :: p.1, p.2), r.takeI (f e) ++ [some k])
  set A : Type := ℕ × (List ℕ × List ℕ) × List (Option ℕ)
  -- Projections on A
  have hk : Primrec (Prod.fst : A → ℕ) := Primrec.fst
  have hp : Primrec (fun a : A => a.2.1) := Primrec.fst.comp Primrec.snd
  have hp1 : Primrec (fun a : A => a.2.1.1) := Primrec.fst.comp hp
  have hp2 : Primrec (fun a : A => a.2.1.2) := Primrec.snd.comp hp
  have hr : Primrec (fun a : A => a.2.2) := Primrec.snd.comp Primrec.snd
  -- findWitness? as Primrec
  have hfw : Primrec (fun a : A => findWitness? f a.1 a.2) := primrec₂_findWitness? hf
  -- The none branch: just return (p, r)
  have hnone : Primrec (fun a : A => a.2) := Primrec.snd
  -- The some branch: (a, (e, y)) ↦ ((Nat.pair e y :: p.1, p.2), r.takeI (f e) ++ [some k])
  -- Let B := ℕ × ℕ. Input type for g is A × B.
  have hsome : Primrec₂ (fun (a : A) (ey : ℕ × ℕ) =>
      ((Nat.pair ey.1 ey.2 :: a.2.1.1, a.2.1.2), a.2.2.takeI (f ey.1) ++ [some a.1])) := by
    -- Projections on A × B
    have hka : Primrec (fun ab : A × (ℕ × ℕ) => ab.1.1) := hk.comp Primrec.fst
    have hp1a : Primrec (fun ab : A × (ℕ × ℕ) => ab.1.2.1.1) := hp1.comp Primrec.fst
    have hp2a : Primrec (fun ab : A × (ℕ × ℕ) => ab.1.2.1.2) := hp2.comp Primrec.fst
    have hra : Primrec (fun ab : A × (ℕ × ℕ) => ab.1.2.2) := hr.comp Primrec.fst
    have he : Primrec (fun ab : A × (ℕ × ℕ) => ab.2.1) := Primrec.fst.comp Primrec.snd
    have hy : Primrec (fun ab : A × (ℕ × ℕ) => ab.2.2) := Primrec.snd.comp Primrec.snd
    have hpair : Primrec (fun ab : A × (ℕ × ℕ) => Nat.pair ab.2.1 ab.2.2) :=
      Primrec₂.natPair.comp he hy
    have hfe : Primrec (fun ab : A × (ℕ × ℕ) => f ab.2.1) := hf.comp he
    have hcons : Primrec (fun ab : A × (ℕ × ℕ) => Nat.pair ab.2.1 ab.2.2 :: ab.1.2.1.1) :=
      Primrec.list_cons.comp hpair hp1a
    have hfst_out : Primrec (fun ab : A × (ℕ × ℕ) =>
        (Nat.pair ab.2.1 ab.2.2 :: ab.1.2.1.1, ab.1.2.1.2)) :=
      Primrec.pair hcons hp2a
    -- takeI: use list_takeI
    have htake : Primrec (fun ab : A × (ℕ × ℕ) => ab.1.2.2.takeI (f ab.2.1)) :=
      Primrec.list_takeI.comp hra hfe
    -- [some k] = some k :: []
    have hsomek : Primrec (fun ab : A × (ℕ × ℕ) => (some ab.1.1 : Option ℕ)) :=
      Primrec.option_some.comp hka
    have hsing : Primrec (fun ab : A × (ℕ × ℕ) => [(some ab.1.1 : Option ℕ)]) :=
      Primrec.list_cons.comp hsomek (Primrec.const [])
    have hsnd_out : Primrec (fun ab : A × (ℕ × ℕ) =>
        ab.1.2.2.takeI (f ab.2.1) ++ [(some ab.1.1 : Option ℕ)]) :=
      Primrec.list_append.comp htake hsing
    exact Primrec.pair hfst_out hsnd_out
  -- Combine with option_casesOn
  refine (Primrec.option_casesOn hfw hnone hsome).of_eq fun a => ?_
  obtain ⟨k, p, r⟩ := a
  simp only [extend]
  cases findWitness? f k (p, r) with
  | none => rfl
  | some ey => obtain ⟨e, y⟩ := ey; rfl

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
  -- seq1 (k+1) reduces to (extend (2*·+1) k ...).1.2  via Prod.map_fst + Prod.fst_swap
  -- By ← extend_snd, this equals (Prod.map .swap id (extend (2*·) k (seq k))).1.2
  -- By Prod.map_fst + Prod.snd_swap, this is (extend (2*·) k (seq k)).1.1
  -- Which contains (seq k).1.1 = seq1 k by extend_fst.
  show (seq k).1.1 ⊆ (seq (k + 1)).1.1
  simp only [seq, Prod.map_fst, Prod.fst_swap]
  rw [← extend_snd (2 * · + 1) k]
  simp only [Prod.map_fst, Prod.snd_swap]
  exact extend_fst _ _ _

/--
`seq2` is monotone.
-/
lemma seq2_mono (k : ℕ) : seq2 k ⊆ seq2 (k + 1) := by
  -- seq2 (k+1) reduces to (extend (2*·+1) k ...).1.1  via Prod.map_fst + Prod.snd_swap
  -- By extend_fst, (seq k).1.2 ⊆ input to extend's .1.1 = (Prod.map .swap id ...).1.1
  -- By Prod.map_fst + Prod.fst_swap, that is (extend (2*·) k (seq k)).1.2
  -- By extend_snd reversed, that equals (seq k).1.2 = seq2 k.
  show (seq k).1.2 ⊆ (seq (k + 1)).1.2
  simp only [seq, Prod.map_fst, Prod.snd_swap]
  apply List.Subset.trans _ (extend_fst (2 * · + 1) k _)
  simp only [Prod.map_fst, Prod.fst_swap]
  rw [← extend_snd (2 * ·) k]
  exact List.Subset.refl _

/--
`seq` is primitive recursive.
-/
lemma primrec_seq : Primrec seq := by
  -- Prod.map Prod.swap id is primrec: ((a, b), c) ↦ ((b, a), c)
  have hswap : Primrec (Prod.map Prod.swap id :
      (List ℕ × List ℕ) × List (Option ℕ) → (List ℕ × List ℕ) × List (Option ℕ)) :=
    Primrec.pair
      (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
      Primrec.snd
  have hf1 : Primrec (fun x => 2 * x) :=
    Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  have hf2 : Primrec (fun x => 2 * x + 1) :=
    Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id)
  -- step: (k, prev) ↦ Prod.map .swap id (extend (2*·+1) k (Prod.map .swap id (extend (2*·) k prev)))
  have hstep : Primrec₂ (fun k x =>
      Prod.map Prod.swap id (extend (2 * · + 1) k (Prod.map Prod.swap id (extend (2 * ·) k x)))) :=
    hswap.comp
      ((primrec₂_extend hf2).comp Primrec.fst
        (hswap.comp ((primrec₂_extend hf1).comp Primrec.fst Primrec.snd)))
  exact (Primrec.nat_rec₁ (([], []), []) hstep).of_eq fun n => by
    induction n with
    | zero => simp [seq]
    | succ n ih =>
      have hseq : seq (n + 1) = Prod.map Prod.swap id
          (extend (2 * · + 1) n (Prod.map Prod.swap id (extend (2 * ·) n (seq n)))) := by
        simp [seq]
      rw [hseq, ← ih]

/--
The predicate `p1` is RE.
-/
lemma re_p1 : REPred p1 := by
  -- seq1 k = (seq k).1.1 is primitive recursive
  have primrec_seq1 : Primrec seq1 :=
    Primrec.fst.comp (Primrec.fst.comp primrec_seq)
  -- x ∈ L is a primitive recursive relation in (L, x)
  have hmem_rel : PrimrecRel (fun (L : List ℕ) (b : ℕ) => b ∈ L) :=
    Primrec.eq.exists_mem_list.of_eq fun L b => ⟨fun ⟨_, ha, rfl⟩ => ha, fun h => ⟨b, h, rfl⟩⟩
  -- x ∈ seq1 k is primitive recursive in (x, k)
  have hmem_pred : PrimrecPred (fun q : ℕ × ℕ => q.1 ∈ seq1 q.2) :=
    hmem_rel.comp (primrec_seq1.comp Primrec.snd) Primrec.fst
  -- fun x k => Part.some (decide (x ∈ seq1 k)) is partrec
  have hpartrec : Partrec₂ (fun x k => (Part.some (decide (x ∈ seq1 k)) : Part Bool)) :=
    hmem_pred.decide.to₂.to_comp.partrec₂
  -- Nat.rfind (fun k => Part.some (decide (x ∈ seq1 k))) has domain p1 x
  refine (Partrec.rfind hpartrec).dom_re.of_eq fun x => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff, p1]
  constructor
  · rintro ⟨k, hk, -⟩; exact ⟨k, decide_eq_true_iff.mp hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk], fun _ => trivial⟩

/--
The predicate `p2` is RE.
-/
lemma re_p2 : REPred p2 := by
  -- seq2 k = (seq k).1.2 is primitive recursive
  have primrec_seq2 : Primrec seq2 :=
    Primrec.snd.comp (Primrec.fst.comp primrec_seq)
  have hmem_rel : PrimrecRel (fun (L : List ℕ) (b : ℕ) => b ∈ L) :=
    Primrec.eq.exists_mem_list.of_eq fun L b => ⟨fun ⟨_, ha, rfl⟩ => ha, fun h => ⟨b, h, rfl⟩⟩
  have hmem_pred : PrimrecPred (fun q : ℕ × ℕ => q.1 ∈ seq2 q.2) :=
    hmem_rel.comp (primrec_seq2.comp Primrec.snd) Primrec.fst
  have hpartrec : Partrec₂ (fun x k => (Part.some (decide (x ∈ seq2 k)) : Part Bool)) :=
    hmem_pred.decide.to₂.to_comp.partrec₂
  refine (Partrec.rfind hpartrec).dom_re.of_eq fun x => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff, p2]
  constructor
  · rintro ⟨k, hk, -⟩; exact ⟨k, decide_eq_true_iff.mp hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk], fun _ => trivial⟩

/--
Helper: if `i < n`, then `(l.takeI n).getI i = l.getI i`.
-/
private lemma List.getI_takeI {α : Type*} [Inhabited α] :
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
lemma extend_snd_bound_le (f : ℕ → ℕ) (k : ℕ)
    (u : (List ℕ × List ℕ) × List (Option ℕ))
    (h : ∀ i m, u.2.getI i = some m → m ≤ k) :
    ∀ i m, (extend f k u).2.getI i = some m → m ≤ k := by
  intro i m hget
  cases hfw : findWitness? f k u with
  | none =>
    have heq : (extend f k u).2 = u.2 := by simp [extend, hfw]
    rw [heq] at hget
    exact h i m hget
  | some p =>
    obtain ⟨e, y⟩ := p
    rcases lt_trichotomy i (f e) with hi | hi | hi
    · rw [extend_snd_getI_lt hfw hi] at hget
      exact h i m hget
    · subst hi
      rw [extend_snd_getI_eq hfw] at hget
      have : m = k := by injection hget with h; exact h.symm
      subst this; rfl
    · rw [extend_snd_getI_gt hfw hi] at hget
      contradiction

/--
Helper: any `some m` value in `(seq k).2` satisfies `m < k`.
-/
lemma res_lt_stage : ∀ (k i m : ℕ), res k i = some m → m < k := by
  intro k
  induction k with
  | zero =>
    intro i m hget
    unfold res at hget
    simp [seq, List.getI, List.getD] at hget
  | succ k IH =>
    intro i m hget
    apply Nat.lt_succ_of_le
    unfold res at hget
    have hseq : seq (k+1) = Prod.map Prod.swap id
        (extend (2 * · + 1) k (Prod.map Prod.swap id (extend (2 * ·) k (seq k)))) := by
      simp [seq]
    rw [hseq] at hget
    simp only [Prod.map_snd, id_eq] at hget
    have h_seq_le : ∀ i' m', (seq k).2.getI i' = some m' → m' ≤ k :=
      fun i' m' h => le_of_lt (IH i' m' h)
    have h1 := extend_snd_bound_le (2 * ·) k (seq k) h_seq_le
    have h2 : ∀ i' m', (Prod.map Prod.swap id (extend (2 * ·) k (seq k))).2.getI i' = some m' → m' ≤ k := by
      intro i' m' hget'
      simp only [Prod.map_snd, id_eq] at hget'
      exact h1 i' m' hget'
    exact extend_snd_bound_le _ _ _ h2 i m hget

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
      -- Goal: res (k+1) n = some j
      -- Strategy: no action in either extend call at stage k can occur at position ≤ n.
      -- Hence both extends preserve position n.
      show res (k+1) n = some j
      -- Stability of res at positions i < n, from hk₀ at stages k and k+1.
      have k_ge : k ≥ k₀ := le_trans hk₁ hk
      have k1_ge : k+1 ≥ k₀ := by omega
      -- `k` doesn't appear as a value in `(seq k).2`.
      have no_k_in_r₀ : ∀ i, (seq k).2.getI i ≠ some k := by
        intro i hi
        exact absurd (res_lt_stage k i k hi) (lt_irrefl _)
      -- Unfold seq (k+1).
      have hseq : seq (k+1) = Prod.map Prod.swap id
          (extend (2 * · + 1) k (Prod.map Prod.swap id (extend (2 * ·) k (seq k)))) := by
        simp [seq]
      unfold res
      rw [hseq]
      simp only [Prod.map_snd, id_eq]
      -- Goal: (extend (2·+1) k (Prod.map .swap id (extend (2·) k (seq k)))).2.getI n = some j
      -- Introduce the two extend stages.
      set u₀ := seq k with hu₀
      set u₁ := extend (2 * ·) k u₀ with hu₁
      have hu₁_snd : u₁.2 = (Prod.map Prod.swap id u₁).2 := rfl
      set u₂ := Prod.map Prod.swap id u₁ with hu₂
      -- u₂.2 = u₁.2
      have hr₀n : u₀.2.getI n = some j := IH
      -- Show u₁.2.getI n = some j: first extend preserves position n.
      have hr₁n : u₁.2.getI n = some j := by
        rw [hu₁]
        cases hfw : findWitness? (2 * ·) k u₀ with
        | none => simp [extend, hfw, hr₀n]
        | some p =>
          obtain ⟨e, y⟩ := p
          -- Position 2e: action occurs at 2e. Show 2e > n.
          have h2e_gt : 2 * e > n := by
            by_contra hle
            push_neg at hle
            rcases lt_or_eq_of_le hle with h2e_lt | h2e_eq
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
              cases hfw2 : findWitness? (2 * · + 1) k u₂ with
              | none =>
                -- r₃ = r₂ = r₁. So r₃.getI (2e) = some k. But res (k+1) (2e) = o = r₃.getI (2e).
                have heq : res (k+1) (2 * e) = some k := by
                  show (seq (k+1)).2.getI (2 * e) = some k
                  rw [hseq]
                  simp only [Prod.map_snd, id_eq]
                  simp only [extend, hfw2]
                  change u₁.2.getI (2 * e) = some k
                  exact h1
                rw [heq] at hres_k1
                rw [← hres_k1] at hres_k
                exact absurd hres_k (no_k_in_r₀ (2 * e))
              | some p' =>
                obtain ⟨e', y'⟩ := p'
                -- Second extend acts at 2e'+1. Position 2e+1's role vs 2e depends on ordering.
                by_cases hord : 2 * e < 2 * e' + 1
                · -- 2e' + 1 > 2e, so position 2e is preserved in r₃.
                  have h3 : (extend (2 * · + 1) k u₂).2.getI (2 * e) = some k := by
                    rw [extend_snd_getI_lt hfw2 hord]
                    change u₁.2.getI (2 * e) = some k
                    exact h1
                  have heq : res (k+1) (2 * e) = some k := by
                    show (seq (k+1)).2.getI (2 * e) = some k
                    rw [hseq]
                    simp only [Prod.map_snd, id_eq]
                    exact h3
                  rw [heq] at hres_k1
                  rw [← hres_k1] at hres_k
                  exact absurd hres_k (no_k_in_r₀ (2 * e))
                · -- 2e'+1 ≤ 2e, but different parity so 2e'+1 < 2e.
                  push_neg at hord
                  have hstrict : 2 * e' + 1 < 2 * e := by omega
                  -- Second extend acts at 2e'+1 < 2e < n. Apply stability at 2e'+1.
                  have h2e'_lt_n : 2 * e' + 1 < n := by omega
                  obtain ⟨o', ho'⟩ := hk₀ (2 * e' + 1) h2e'_lt_n
                  have hres'_k : res k (2 * e' + 1) = o' := ho' k k_ge
                  have hres'_k1 : res (k+1) (2 * e' + 1) = o' := ho' (k+1) k1_ge
                  -- res (k+1) (2e'+1) = some k (it's where second extend just acted)
                  have heq : res (k+1) (2 * e' + 1) = some k := by
                    show (seq (k+1)).2.getI (2 * e' + 1) = some k
                    rw [hseq]
                    simp only [Prod.map_snd, id_eq]
                    exact extend_snd_getI_eq hfw2
                  rw [heq] at hres'_k1
                  rw [← hres'_k1] at hres'_k
                  exact absurd hres'_k (no_k_in_r₀ (2 * e' + 1))
            · -- 2e = n
              subst h2e_eq
              -- findWitness? required u₀.2.getI (2e) = u₀.2.getI n = none.
              have := findWitness?_some_getI_eq_none hfw
              rw [this] at hr₀n
              contradiction
          -- So 2e > n, first extend preserves position n.
          rw [extend_snd_getI_lt hfw h2e_gt]
          exact hr₀n
      -- Now show second extend preserves position n.
      have hr₂n : u₂.2.getI n = some j := hr₁n
      show (extend (2 * · + 1) k u₂).2.getI n = some j
      cases hfw2 : findWitness? (2 * · + 1) k u₂ with
      | none => simp [extend, hfw2, hr₂n]
      | some p =>
        obtain ⟨e, y⟩ := p
        have h_gt : 2 * e + 1 > n := by
          by_contra hle
          push_neg at hle
          rcases lt_or_eq_of_le hle with h_lt | h_eq
          · -- 2e+1 < n.
            obtain ⟨o, ho⟩ := hk₀ (2 * e + 1) h_lt
            have hres_k : res k (2 * e + 1) = o := ho k k_ge
            have hres_k1 : res (k+1) (2 * e + 1) = o := ho (k+1) k1_ge
            have heq : res (k+1) (2 * e + 1) = some k := by
              show (seq (k+1)).2.getI (2 * e + 1) = some k
              rw [hseq]
              simp only [Prod.map_snd, id_eq]
              exact extend_snd_getI_eq hfw2
            rw [heq] at hres_k1
            rw [← hres_k1] at hres_k
            exact absurd hres_k (no_k_in_r₀ (2 * e + 1))
          · -- 2e+1 = n.
            subst h_eq
            have := findWitness?_some_getI_eq_none hfw2
            rw [this] at hr₂n
            contradiction
        rw [extend_snd_getI_lt hfw2 h_gt]
        exact hr₂n

/--
Convert a predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [∀ a, Decidable (p a)] : α → ℕ :=
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
