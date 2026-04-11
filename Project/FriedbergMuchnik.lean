module

public import Mathlib.Computability.Halting
public import Project.OracleCode
public import Project.Queries
public import Project.Substitute
public import Project.PartrecCode

namespace Computability

open RecursiveIn

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
      ∧ 0 ∈ ((Denumerable.ofNat Code e).substPartrec (.listMem p.2)).evaln k x
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

/--
`findWitness?` is primitive recursive (if the indexing function is).
-/
lemma primrec₂_findWitness? {f} (hf : Primrec f) : Primrec₂ (findWitness? f) := by
  sorry

/--
`extend` is primitive recursive (if the indexing function is).
-/
lemma primrec₂_extend {f} (hf : Primrec f) : Primrec₂ (extend f) := by
  sorry

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

def p1 (x : ℕ) : Prop := ∃ k, x ∈ seq1 k

def p2 (x : ℕ) : Prop := ∃ k, x ∈ seq2 k

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
      sorry

/--
Convert a predicate `α → Prop` into an indicator function `α → ℕ`.
-/
def ofPred {α} (p : α → Prop) [∀ a, Decidable (p a)] : α → ℕ :=
  fun a => (decide (p a)).toNat

open Classical in
/--
The **Friedberg-Muchnik Theorem**: there exist two Turing-incomparable RE predicates.
-/
theorem exists_incomparable_rePreds : ∃ p q : ℕ → Prop, REPred p ∧ REPred q ∧ ¬(ofPred p ≤ᵀ ofPred q) ∧ ¬(ofPred q ≤ᵀ ofPred p) := by
  use p1, p2, re_p1, re_p2
  simp only [Code.exists_code, not_exists]
  refine ⟨fun c => ?_, fun c => ?_⟩
  · let e := Encodable.encode c
    sorry
  · let e := Encodable.encode c
    sorry

end Computability
