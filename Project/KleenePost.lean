module

public import Project.OracleCode

namespace List

/--
Given a sequence of lists `s : ℕ → List α` such that `n < (s n).length` for every `n`, we can define their limit: `limit s hs n` is defined to be `(s n)[n]`.

TODO: does something like this already exist in mathlib?
-/
def limit {α} (s : ℕ → List α) (hs : ∀ n, n < (s n).length) : ℕ → α :=
  fun n => (s n).get ⟨n, hs n⟩

/--
A list `l` is a prefix of a function `f : ℕ → α` if for every `n < l.length`, `l[n] = f n`.
-/
def IsPrefixOfFun {α} (l : List α) (f : ℕ → α) : Prop :=
  ∀ (n : ℕ) (hn : n < l.length), l.get ⟨n, hn⟩ = f n

/--
If list `l` is a prefix of list `l'`, and `l'` is a prefix of function `f`, then `l` is also a prefix of `f`.
-/
lemma prefixOfFun_of_prefix_of_prefixOfFun {α} {l l' : List α} {f : ℕ → α} (h1 : l <+: l') (h2 : l'.IsPrefixOfFun f) : l.IsPrefixOfFun f :=
  by
    intro n hn
    have hn' : n < l'.length := lt_of_lt_of_le hn h1.length_le
    have hprefix : l'[n]? = some ((l[n]'hn)) := (List.prefix_iff_getElem?.mp h1) n hn
    have hfun : l'[n]? = some (f n) := by
      rw [List.getElem?_eq_getElem hn']
      exact congrArg some (h2 n hn')
    exact Option.some.inj (hprefix.symm.trans hfun)

/--
If `s` is monotone in the sense that `s n` is a prefix of `s (n+1)` for all `n`, then each `s n` is a prefix of `limit s`.
-/
lemma prefixOfFun_limit {α} (s : ℕ → List α) (hs : ∀ n, n < (s n).length) (hs_mono : ∀ n, s n <+: s (n+1)) : ∀ n, (s n).IsPrefixOfFun (limit s hs) := by
  have hs_mono' : ∀ {a b : ℕ}, a ≤ b → s a <+: s b := by
    intro a b hab
    induction hab with
    | refl =>
      exact List.prefix_rfl
    | @step b hab ih =>
      exact ih.trans (hs_mono b)
  intro n m hm
  by_cases hnm : n ≤ m
  · have hprefix : s n <+: s m := hs_mono' hnm
    have h1 : (s m)[m]? = some ((s n)[m]'hm) := (List.prefix_iff_getElem?.mp hprefix) m hm
    have h2 : (s m)[m]? = some ((s m)[m]'(hs m)) := List.getElem?_eq_getElem (hs m)
    exact Option.some.inj (h1.symm.trans h2)
  · have hmn : m ≤ n := Nat.le_of_not_ge hnm
    have hprefix : s m <+: s n := hs_mono' hmn
    have h1 : (s n)[m]? = some ((s m)[m]'(hs m)) := (List.prefix_iff_getElem?.mp hprefix) m (hs m)
    have h2 : (s n)[m]? = some ((s n)[m]'hm) := List.getElem?_eq_getElem hm
    exact Option.some.inj (h2.symm.trans h1)

end List


namespace TuringDegree

open RecursiveIn

noncomputable section

open Classical in
/--
Given a `RecursiveIn.Code` `c` and a pair of lists `(s, t)`, `extend c (s, t)` returns a pair `(s', t')` such that `s' ⊇ s`, `t' ⊇ t`, and for all `f` extending `s'`, `c.eval f` is not a function extending `t'`.
-/
def extend (c : Code) : List ℕ × List ℕ → List ℕ × List ℕ := fun (s, t) =>
  if h : ∃ s', s <+: s' ∧ t.length ∈ (c.eval fun n => s'[n]?).Dom then
    -- Case 1: there is some `s' ⊇ s` such that `c.eval s' |t|` halts and outputs `k`. Then return `(s', t ++ [k+1])`.
    let s' := h.choose;
    let k := (c.eval (fun n => s'[n]?) t.length).get h.choose_spec.2;
    (s', t ++ [k+1])
  else
    -- Case 2: there is no `s' ⊇ s` such that `c.eval s' |t|` halts. Then return `(s, t)`.
    (s, t)

/--
`extend` is increasing in the first argument.
-/
lemma prefix_extend_fst (c : Code) (p : List ℕ × List ℕ) : p.1 <+: (extend c p).1 := by
  rcases p with ⟨s, t⟩
  unfold extend
  simp only
  split_ifs with h
  · simpa using h.choose_spec.1
  · simp

/--
`extend` is increasing in the second argument.
-/
lemma prefix_extend_snd (c : Code) (p : List ℕ × List ℕ) : p.2 <+: (extend c p).2 := by
  rcases p with ⟨s, t⟩
  unfold extend
  simp only
  split_ifs with h
  · exact List.prefix_append t [((c.eval fun n => h.choose[n]?) t.length).get h.choose_spec.2 + 1]
  · simp


/--
If `c.eval` halts at `n` with the finite oracle `s`, then evaluating with a total extension `f`
returns the same value.
-/
lemma oracle_use_forward (c : Code) (s : List ℕ) (f : ℕ → ℕ) (n : ℕ)
    (hsf : s.IsPrefixOfFun f) :
    ∀ hdom : n ∈ (c.eval fun i => s[i]?).Dom,
      c.eval f n = Part.some ((c.eval (fun i => s[i]?) n).get hdom) := by
  induction c generalizing n with
  | zero =>
    intro hdom
    simp [RecursiveIn.Code.eval]
  | succ =>
    intro hdom
    simp [RecursiveIn.Code.eval]
  | left =>
    intro hdom
    simp [RecursiveIn.Code.eval]
  | right =>
    intro hdom
    simp [RecursiveIn.Code.eval]
  | oracle =>
    intro hdom
    simp [RecursiveIn.Code.eval] at hdom ⊢
    rw [List.getElem?_eq_getElem hdom, ← hsf n hdom]
    simp
  | pair cf cg ihf ihg =>
    intro hdom
    sorry
  | comp cf cg ihf ihg =>
    intro hdom
    sorry
  | prec cf cg ihf ihg =>
    intro hdom
    sorry
  | rfind' cf ihf =>
    intro hdom
    sorry


/--
If `c.eval f n` halts with a total oracle `f`, then some finite extension of `s` already witnesses
halting at `n`.
-/
lemma oracle_use_backward (c : Code) (s : List ℕ) (f : ℕ → ℕ) (n : ℕ)
    (hsf : s.IsPrefixOfFun f) :
    n ∈ (c.eval f).Dom → ∃ s', s <+: s' ∧ n ∈ (c.eval fun i => s'[i]?).Dom := by
  intro hdom_f
  by_contra hno
  push_neg at hno
  have hs_self : s <+: s := List.prefix_rfl
  have hnot_s : n ∉ (c.eval fun i => s[i]?).Dom := by
    intro hdom_s
    exact hno s hs_self hdom_s
  -- Blocker: from `hdom_f` and `hsf`, we still need a finite-use/continuity argument for `c.eval`
  -- to derive a contradiction with `hnot_s`.
  sorry

/--
Helper lemma for switching between a finite oracle prefix and a total oracle extension.
-/
lemma oracle_use (c : Code) (s : List ℕ) (f : ℕ → ℕ) (n : ℕ) (hsf : s.IsPrefixOfFun f) :
    (∀ hdom : n ∈ (c.eval fun i => s[i]?).Dom,
      c.eval f n = Part.some ((c.eval (fun i => s[i]?) n).get hdom)) ∧
    (n ∈ (c.eval f).Dom → ∃ s', s <+: s' ∧ n ∈ (c.eval fun i => s'[i]?).Dom) := by
  exact ⟨oracle_use_forward c s f n hsf, oracle_use_backward c s f n hsf⟩

/--
The key property of `extend c p`. Suppose `extend c p = (s', t')`. If (1) `f` is a function `ℕ → ℕ` extending `s'`, and (2) `g` is a function `ℕ → ℕ` extending `t'`, then `c.eval f ≠ g`.
-/

theorem extend_spec (c : Code) (p : List ℕ × List ℕ) (f g : ℕ → ℕ) (hf : (extend c p).1.IsPrefixOfFun f) (hg : (extend c p).2.IsPrefixOfFun g) : c.eval f ≠ g := by
  let s := p.1; let t := p.2
  by_cases h : ∃ s', s <+: s' ∧ t.length ∈ (c.eval fun n => s'[n]?).Dom
  · -- Case 1: `c.eval f |t| = k`, while `g |t| = k + 1`.
    simp only [extend] at hf hg
    rw [dif_pos h] at hf hg
    simp at hf hg
    intro a
    let w := h.choose
    let k := (c.eval (fun n => w[n]?) t.length).get h.choose_spec.2
    have hf' : w.IsPrefixOfFun f := by
      simpa [w] using hf
    have hg' : (p.2 ++ [((c.eval (fun n => h.choose[n]?) p.2.length).get h.choose_spec.2 + 1)]).IsPrefixOfFun g := by
      simpa using hg
    have hfg_at : c.eval f t.length = Part.some (g t.length) := by
      simpa using congrArg (fun q => q t.length) a
    have hgt : g t.length = k + 1 := by
      have htlt : t.length <
          (p.2 ++ [((c.eval (fun n => h.choose[n]?) p.2.length).get h.choose_spec.2 + 1)]).length := by
        simpa [t]
      simpa [w, k, t] using (hg' t.length htlt).symm
    have hval : c.eval f t.length = Part.some k :=
      (oracle_use c w f t.length hf').1 (by simpa [w] using h.choose_spec.2)
    have hsome :
        Part.some k = Part.some (k + 1) := by
      calc
        Part.some k = c.eval f t.length := hval.symm
        _ = Part.some (g t.length) := hfg_at
        _ = Part.some (k + 1) := by simpa [hgt]
    exact (Nat.succ_ne_self _) (Part.some_injective hsome).symm
  · -- Case 2: `|t| ∉ (c.eval f).Dom`, while `g` is total.
    simp only [extend] at hf
    rw [dif_neg h] at hf
    simp at hf
    push_neg at h
    intro a
    have hfg_at : c.eval f t.length = Part.some (g t.length) := by
      simpa using congrArg (fun q => q t.length) a
    have hdom_f : t.length ∈ (c.eval f).Dom := by
      change (c.eval f t.length).Dom
      rw [hfg_at]
      simp
    rcases (oracle_use c s f t.length hf).2 hdom_f with ⟨s', hs', hdom'⟩
    exact (h s' hs') hdom'

/--
Build the sequence using `extend` twice at each step.
Notes:
- We start with ([0], [0]) so that `n < (seq n).length` holds for every `n`.
- The length increasing is handled by `Prod.map (. ++ [0]) (. ++ [0])`, rather than making `extend` do extra work.
-/
def seq : ℕ → List ℕ × List ℕ
  | 0 => ([0], [0])
  | n + 1 =>
    let c := Denumerable.ofNat Code n;
    Prod.map (. ++ [0]) (. ++ [0]) <|
    Prod.swap <| extend c <| Prod.swap <| extend c <| seq n

def seq1 : ℕ → List ℕ := fun n => (seq n).1

def seq2 : ℕ → List ℕ := fun n => (seq n).2

/--
`seq1` is monotone.
-/
lemma seq1_mono (n : ℕ) : seq1 n <+: seq1 (n+1) := by
  let c := Denumerable.ofNat Code n
  have h1 : (seq n).1 <+: (extend c (seq n)).1 := prefix_extend_fst c (seq n)
  have h2 : (extend c (seq n)).1 <+: (extend c (Prod.swap (extend c (seq n)))).2 := by
    simpa using (prefix_extend_snd c (Prod.swap (extend c (seq n))))
  have h3 : (extend c (Prod.swap (extend c (seq n)))).2 <+:
      (extend c (Prod.swap (extend c (seq n)))).2 ++ [0] := List.prefix_append _ _
  simpa [seq1, seq, c] using h1.trans (h2.trans h3)

/--
`seq2` is monotone.
-/
lemma seq2_mono (n : ℕ) : seq2 n <+: seq2 (n+1) := by
  let c := Denumerable.ofNat Code n
  have h1 : (seq n).2 <+: (extend c (seq n)).2 := prefix_extend_snd c (seq n)
  have h2 : (extend c (seq n)).2 <+: (extend c (Prod.swap (extend c (seq n)))).1 := by
    simpa using (prefix_extend_fst c (Prod.swap (extend c (seq n))))
  have h3 : (extend c (Prod.swap (extend c (seq n)))).1 <+:
      (extend c (Prod.swap (extend c (seq n)))).1 ++ [0] := List.prefix_append _ _
  simpa [seq2, seq, c] using h1.trans (h2.trans h3)

/--
For every `n`, `n < (seq1 n).length`. This is used to define the limit.
-/
lemma lt_length_seq1 (n : ℕ) : n < (seq1 n).length := by
  induction n with
  | zero =>
    simp [seq1, seq]
  | succ n ih =>
    let c := Denumerable.ofNat Code n
    let q := extend c (Prod.swap (extend c (seq n)))
    have h1 : (seq n).1 <+: (extend c (seq n)).1 := prefix_extend_fst c (seq n)
    have h2 : (extend c (seq n)).1 <+: q.2 := by
      simpa [q] using (prefix_extend_snd c (Prod.swap (extend c (seq n))))
    have hn : n < q.2.length := lt_of_lt_of_le ih (h1.trans h2).length_le
    have hsucc : n + 1 < (q.2 ++ [0]).length := by
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.succ_lt_succ hn
    simpa [seq1, seq, c, q]

/--
For every `n`, `n < (seq2 n).length`. This is used to define the limit.
-/
lemma lt_length_seq2 (n : ℕ) : n < (seq2 n).length := by
  induction n with
  | zero =>
    simp [seq2, seq]
  | succ n ih =>
    let c := Denumerable.ofNat Code n
    let q := extend c (Prod.swap (extend c (seq n)))
    have h1 : (seq n).2 <+: (extend c (seq n)).2 := prefix_extend_snd c (seq n)
    have h2 : (extend c (seq n)).2 <+: q.1 := by
      simpa [q] using (prefix_extend_fst c (Prod.swap (extend c (seq n))))
    have hn : n < q.1.length := lt_of_lt_of_le ih (h1.trans h2).length_le
    have hsucc : n + 1 < (q.1 ++ [0]).length := by
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.succ_lt_succ hn
    simpa [seq2, seq, c, q]

/--
The **Kleene-Post Theorem**: there exist two incomparable Turing degrees.
-/
theorem exists_incomparable_turingDegrees : ∃ a b : TuringDegree, ¬(a ≤ b) ∧ ¬(b ≤ a) := by
  let f := List.limit seq1 lt_length_seq1
  let g := List.limit seq2 lt_length_seq2
  use ⟦f⟧, ⟦g⟧
  change ¬TuringReducible f g ∧ ¬TuringReducible g f
  constructor <;> rw [Code.exists_code] <;> intro ⟨c, hc⟩
  · let n := Encodable.encode c
    -- `p` is what gets fed into `extend c` to ensure `¬ (f ≤ᵀ g)`.
    let p := Prod.swap (extend c (seq n))
    refine extend_spec c p g f ?_ ?_ hc
    · exact List.prefixOfFun_of_prefix_of_prefixOfFun
        (by simp [seq2, seq, p, n])
        (List.prefixOfFun_limit seq2 lt_length_seq2 seq2_mono (n+1))
    · exact List.prefixOfFun_of_prefix_of_prefixOfFun
        (by simp [seq1, seq, p, n])
        (List.prefixOfFun_limit seq1 lt_length_seq1 seq1_mono (n+1))
  · let n := Encodable.encode c
    -- `p` is what gets fed into `extend c` to ensure `¬ (g ≤ᵀ f)`.
    let p := seq n
    refine extend_spec c p f g ?_ ?_ hc
    · refine List.prefixOfFun_of_prefix_of_prefixOfFun ?_
        (List.prefixOfFun_limit seq1 lt_length_seq1 seq1_mono (n+1))
      simp [seq1, seq, p, n]
      grind [prefix_extend_snd]
    · refine List.prefixOfFun_of_prefix_of_prefixOfFun ?_
        (List.prefixOfFun_limit seq2 lt_length_seq2 seq2_mono (n+1))
      simp [seq2, seq, p, n]
      grind [prefix_extend_fst]

end

end TuringDegree
