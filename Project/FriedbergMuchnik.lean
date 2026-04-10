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
* `r` : The list of restraints. `r[f e] = none` (or the index is out of bounds) if requirement `Rₑ` is not currently satisfied. `r[f e] = some k` if requirement `Rₑ` has been satisfied at some earlier stage, and has not been injured since then.
-/
def extend (f : ℕ → ℕ) (k : ℕ) : (List ℕ × List ℕ) × List (Option ℕ) → (List ℕ × List ℕ) × List (Option ℕ) := fun (p, r) =>
  match findWitness? f k (p, r) with
  -- If no strategy needs to act, then do nothing.
  | none => (p, r)
  -- If `Rₑ` needs to act, then add the witness to `p.1`. Also, injure all strategies `Rᵢ` for `i > f e`, and set `r [f e] = some k`.
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
`seq1` is monotone.
-/
lemma seq1_mono (k : ℕ) : seq1 k ⊆ seq1 (k + 1) := by
  sorry

/--
`seq2` is monotone.
-/
lemma seq2_mono (k : ℕ) : seq2 k ⊆ seq2 (k + 1) := by
  sorry

/--
`seq` is primitive recursive.
-/
lemma primrec_seq : Primrec seq := by
  sorry

/--
Each strategy is injured finitely many times. This is expressed by saying that for each index `i`, the function `fun k => (seq k).2.getI i` is eventually constant.
-/
theorem finite_injury (n : ℕ) : ∃ k₀, ∀ i < n, ∃ o, ∀ k ≥ k₀, (seq k).2.getI i = o := by
  induction n with
  | zero => simp
  | succ n IH =>
    obtain ⟨k₀, hk₀⟩ := IH
    sorry

def p1 (x : ℕ) : Prop := ∃ k, x ∈ seq1 k

def p2 (x : ℕ) : Prop := ∃ k, x ∈ seq2 k

/--
The predicate `p1` is RE.
-/
lemma re_p1 : REPred p1 := by
  sorry

/--
The predicate `p2` is RE.
-/
lemma re_p2 : REPred p2 := by
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
