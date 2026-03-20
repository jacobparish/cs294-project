module

public import Project.OracleCode


namespace TuringDegree

open RecursiveIn

noncomputable section

/--
Given a `RecursiveIn.Code` `c` and a pair of lists `(s, t)`, output `(s', t')` such that for all `f` extending `s'`, `c.eval f` is not a function extending `t'`.
-/
def extend (c : Code) : List ℕ × List ℕ → List ℕ × List ℕ :=
  fun (s, t) =>
  -- Case 1: there is some s' ⊇ s such that Φ_n^{s'}(|t|) = m. Then return (s', t ++ [m+1]).
  -- Case 2: there is no s' ⊇ s such that Φ_n^{s'}(|t|) halts. Then return (s, t).
  sorry

/--
`extend` is increasing in the first argument.
-/
lemma prefix_extend_fst (c : Code) (p : List ℕ × List ℕ) : p.1 <+: (extend c p).1 := by
  sorry

/--
`extend` is increasing in the second argument.
-/
lemma prefix_extend_snd (c : Code) (p : List ℕ × List ℕ) : p.2 <+: (extend c p).2 := by
  sorry

/--
The key property of `extend n p`.

TODO: This should formally express the property described by `extend`.
-/
theorem extend_spec (c : Code) (p : List ℕ × List ℕ) : 0 = 1 := by
  sorry

/--
Build the sequence using `extend` twice at each step.
Notes:
- We start with ([0], [0]) so that `n < (seq n).length` holds for every `n`.
- The length increasing is handled by `Prod.map (. ++ [0]) (. ++ [0])`, rather than making `extend` do extra work.
-/
def seq : ℕ → List ℕ × List ℕ
  | 0 => ([0], [0])
  | n + 1 => Prod.map (. ++ [0]) (. ++ [0]) <|
    Prod.swap <|
    extend (Denumerable.ofNat Code n) <|
    Prod.swap <|
    extend (Denumerable.ofNat Code n) <|
    seq n

def seq1 : ℕ → List ℕ := fun n => (seq n).1

def seq2 : ℕ → List ℕ := fun n => (seq n).2

/--
`seq1` is increasing.
-/
lemma prefix_seq1_succ {n : ℕ} : seq1 n <+: seq1 (n+1) := by
  sorry

/--
`seq2` is increasing.
-/
lemma prefix_seq2_succ {n : ℕ} : seq2 n <+: seq2 (n+1) := by
  sorry

/--
`seq1` is strictly increasing in length.
-/
lemma lt_length_seq1 (n : ℕ) : n < (seq1 n).length := by
  sorry

/--
`seq2` is strictly increasing in length.
-/
lemma lt_length_seq2 (n : ℕ) : n < (seq2 n).length := by
  sorry


/--
Given a sequence of lists `s : ℕ → List α` such that `n < (s n).length` for every `n`, we can define their limit: `limit s hs n` is defined to be `(s n)[n]`.

TODO: does a construction like this already exist in mathlib?

TODO: prove that if `s` is monotone in the sense that `s n` is a prefix of `s (n+1)`, then `limit s` is "well-defined" in the sense that `limit s n = (s i)[n]`, whenever the right side is defined.
-/
def limit {α} (s : ℕ → List α) (hs : ∀ n, n < (s n).length) : ℕ → α :=
  fun n => (s n).get ⟨n, hs n⟩

/--
The Kleene-Post Theorem: there exist two incomparable Turing degrees.
-/
theorem exists_incomparable_turingDegrees : ∃ a b : TuringDegree, ¬(a ≤ b) ∧ ¬(b ≤ a) := by
  let f := limit seq1 lt_length_seq1
  let g := limit seq2 lt_length_seq2
  use ⟦f⟧, ⟦g⟧
  sorry

end

end TuringDegree
