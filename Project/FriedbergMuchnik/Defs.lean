module

public import Project.Basic
public import Project.OracleCode
public import Project.Evaln

@[expose] public section

namespace Primcodable

instance {α : Type*} [Primcodable α] : Primcodable (WithBot α) :=
  Primcodable.option

end Primcodable

namespace Computability.FriedbergMuchnik

/--
Notation for the pairing function `Nat.pair`.
-/
notation "⟪" a "," b "⟫" => Nat.pair a b

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

@[simp]
lemma approx_zero : approx 0 = [] := rfl

/--
The sequence of approximations to the `i`th oracle, which is the oracle that will not be able to compute `fmPred i`. At the `k`th stage, we try to ensure `p.i` is not computable relative to `approxOracle i k`. Unlike `approx`, the elements of this list are already paired.
-/
def approxOracle (i k : ℕ) : List ℕ :=
  ((approx k).filter fun x => x.1 ≠ i).map Nat.pair.uncurry

/--
An alternative definition of `approxOracle`.
-/
lemma approxOracle_eq_filter_map (i k : ℕ) :
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
The sequence of approximations is monotone.
-/
lemma approx_mono (k : ℕ) : approx k ⊆ approx (k+1) :=
  subset_extend

/--
Each sequence of oracle approximations is monotone.
-/
lemma approxOracle_mono (i k : ℕ) : approxOracle i k ⊆ approxOracle i (k+1) :=
  List.map_subset _ (List.filter_subset _ (approx_mono k))

/--
The restraint table. `res k n = some m` if the requirement corresponding to `n` was satisfied at an earlier stage `m < k`, and not injured since then. Otherwise, `res k n = ⊥`.
-/
def res (k n : ℕ) : WithBot ℕ := (stage k).2.getI n

@[simp]
lemma res_zero (n : ℕ) : res 0 n = ⊥ := rfl

end Computability.FriedbergMuchnik

end
