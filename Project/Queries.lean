module

public import Project.OracleCode

namespace RecursiveIn.Code

/--
Given a code `c` and an oracle `o`, `evalq c o` is a partial function `ℕ →. ℕ × Finset ℕ` with the same domain as `eval c o`. If defined, the first coordinate of `evalq c o n` is `eval c o n`, and the second coordinate is the set of all oracle queries made during the evaluation of `eval c o n`.
-/
def evalq (c : Code) (o : ℕ →. ℕ) : ℕ →. ℕ × Finset ℕ := match c with
  | zero => fun _ => pure (0, ∅)
  | succ => fun n => pure (n.succ, ∅)
  | left => fun n => pure (n.unpair.1, ∅)
  | right => fun n => pure (n.unpair.2, ∅)
  | oracle => fun n => do
    let m ← o n
    pure (m, {n})
  | pair cf cg => fun n => do
    let p ← cf.evalq o n
    let q ← cg.evalq o n
    pure (Nat.pair p.1 q.1, p.2 ∪ q.2)
  | comp cf cg => fun n => do
    let p ← cg.evalq o n
    let q ← cf.evalq o p.1
    pure (q.1, p.2 ∪ q.2)
  | prec cf cg =>
    Nat.unpaired fun a m =>
      m.rec (cf.evalq o a) fun k IH => do
        let p ← IH
        let q ← cg.evalq o (Nat.pair a (Nat.pair k p.1))
        pure (q.1, p.2 ∪ q.2)
  | rfind' cf =>
    -- TODO: It would be better if there were a sort of `rfind` + `fold`, so that we don't have to do this.
    Nat.unpaired fun a m => do
      -- First run `rfind` to see if it actually halts.
      let n ← Nat.rfind fun n => (fun p => p.1 = 0) <$> cf.evalq o (Nat.pair a (n + m))
      -- If it halts, then we can go back and take the union of all oracle queries made.
      let s ← n.succ.rec (pure ∅) fun k IH => do
        let s ← IH
        let p ← cf.evalq o (Nat.pair a (k + m))
        pure (s ∪ p.2)
      pure (n + m, s)

@[simp]
lemma evalq_zero (o : ℕ →. ℕ) (n : ℕ) : evalq zero o n = Part.some (0, ∅) := rfl

@[simp]
lemma evalq_succ (o : ℕ →. ℕ) (n : ℕ) : evalq succ o n = Part.some (n+1, ∅) := rfl

@[simp]
lemma evalq_left (o : ℕ →. ℕ) (n : ℕ) : evalq left o n = Part.some (n.unpair.1, ∅) := rfl

@[simp]
lemma evalq_right (o : ℕ →. ℕ) (n : ℕ) : evalq right o n = Part.some (n.unpair.2, ∅) := rfl

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem evalq_prec_zero (cf cg : Code) (o : ℕ →. ℕ) (a : ℕ) : (prec cf cg).evalq o (Nat.pair a 0) = cf.evalq o a := by
  rw [evalq, Nat.unpaired, Nat.unpair_pair]
  simp

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem evalq_prec_succ (cf cg : Code) (o : ℕ →. ℕ) (a k : ℕ) :
    (prec cf cg).evalq o (Nat.pair a (Nat.succ k)) =
      do {let p ← evalq (prec cf cg) o (Nat.pair a k); let q ← evalq cg o (Nat.pair a (Nat.pair k p.1)); pure (q.1, p.2 ∪ q.2)} := by
  rw [evalq, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp

/--
Given a code `c`, an oracle `o`, `queries c o` is a partial function `ℕ →. Finset ℕ` with the same domain as `eval c o`. If defined, `queries c o n` is the set of all oracle queries made during the evaluation of `eval c o n`.
-/
def queries (c : Code) (o : ℕ →. ℕ) : ℕ →. Finset ℕ :=
  fun n => Prod.snd <$> c.evalq o n

@[simp]
lemma queries_zero (o : ℕ →. ℕ) (n : ℕ) : queries zero o n = Part.some ∅ := rfl

@[simp]
lemma queries_succ (o : ℕ →. ℕ) (n : ℕ) : queries succ o n = Part.some ∅ := rfl

@[simp]
lemma queries_left (o : ℕ →. ℕ) (n : ℕ) : queries left o n = Part.some ∅ := rfl

@[simp]
lemma queries_right (o : ℕ →. ℕ) (n : ℕ) : queries right o n = Part.some ∅ := rfl

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem queries_prec_zero (cf cg : Code) (o : ℕ →. ℕ) (a : ℕ) : (prec cf cg).queries o (Nat.pair a 0) = cf.queries o a := by
  simp [queries]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem queries_prec_succ (cf cg : Code) (o : ℕ →. ℕ) (a k : ℕ) :
    (prec cf cg).queries o (Nat.pair a (Nat.succ k)) =
      do {let p ← evalq (prec cf cg) o (Nat.pair a k); let s ← queries cg o (Nat.pair a (Nat.pair k p.1)); pure (p.2 ∪ s)} := by
  simp [queries, evalq_prec_succ]

/--
If `(f k a).Dom` holds for all `k < n` and all `a`, then also `(pure a >>= f 0 >>= f 1 >>= ... >>= f (n-1)).Dom` holds.
-/
private lemma rec_dom {α} {f : ℕ → α →. α} {n : ℕ} (hf : ∀ k < n, ∀ a, (f k a).Dom) (a : α) : (n.rec (pure a) (fun k IH => IH.bind (f k)) : Part α).Dom := by
  induction n with
  | zero => simp
  | succ n IH => exact ⟨IH (by grind), hf n n.lt_add_one _⟩

/--
`p.bind` followed by a constant function is equal to the constant, if `p.Dom` holds.
-/
private lemma bind_const_eq_of_dom {α β} {p : Part α} (hp : p.Dom) (b : Part β) : p.bind (fun _ => b) = b := by
  grind only [Part.Dom.bind]

/--
The first coordinate of `evalq` agrees with `eval`.
-/
theorem evalq_fst (c : Code) (o : ℕ →. ℕ) (n : ℕ) : Prod.fst <$> c.evalq o n = c.eval o n := by
  induction c generalizing n with
  | zero | succ | left | right => rfl
  | oracle => simp [evalq, eval]
  | pair cf cg IHcf IHcg | comp cf cg IHcf IHcg =>
    simp [evalq, eval, ← IHcf, ← IHcg, Part.bind_some_eq_map]
    rfl
  | prec cf cg IHcf IHcg =>
    suffices ∀ a m, Prod.fst <$> (cf.prec cg).evalq o (Nat.pair a m) = (cf.prec cg).eval o (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2 <;> simp
    intro a m
    induction m with
    | zero =>
      simp
      apply IHcf
    | succ m IHm =>
      simp [eval_prec_succ, evalq_prec_succ, Part.bind_some_eq_map, ← IHm]
      congr
      funext p
      apply IHcg
  | rfind' cf IHcf =>
    suffices ∀ a m, Prod.fst <$> (cf.rfind').evalq o (Nat.pair a m) = (cf.rfind').eval o (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2 <;> simp
    intro a m
    let g1 := fun n => (fun m => decide (m = 0)) <$> cf.eval o (Nat.pair a (n + m))
    let g2 := fun n => (fun p => decide (p.1 = 0)) <$> cf.evalq o (Nat.pair a (n + m))
    have : g1 = g2 := by simp [g1, g2, ← IHcf]; rfl
    by_cases h1 : (Nat.rfind g1).Dom
    · have h2 : (Nat.rfind g2).Dom := by rwa [this] at h1
      let n := (Nat.rfind g1).get h1
      have hn1 : Nat.rfind g1 = Part.some n := by simp [n]
      have hn2 : Nat.rfind g2 = Part.some n := by simp [n, this]
      simp only [evalq, eval, Nat.unpaired, Nat.unpair_pair]
      rw [hn1, hn2]
      simp
      -- The `eval` side is now `Part.some (n+m)`. We need to show that the `evalq` side also evaluates to `Part.some (n+m)`. Right now it is some sequence of binds followed by a `.bind fun _ => Part.some (n+m)`. So all we need to show is that each of those binds returns `some`.
      apply bind_const_eq_of_dom
      simp
      have hn : n ∈ (Nat.rfind g2) := Part.eq_some_iff.mp hn2
      constructor
      · refine rec_dom (fun k hk _ => ?_) _
        have h := Nat.rfind_min hn hk
        simp [g2] at h ⊢
        exact h.choose_spec.1.choose_spec.1
      · have h := Nat.rfind_spec hn
        simp [g2] at h
        exact h.choose_spec.1
    · have h2 : ¬(Nat.rfind g2).Dom := by rwa [this] at h1
      rw [← Part.eq_none_iff'] at h1 h2
      simp only [evalq, eval, Nat.unpaired, Nat.unpair_pair]
      rw [h1, h2]
      simp

/--
If `evalq c o n` halts, then the set of oracle queries made is contained in the domain of `o`.
-/
theorem queries_subset_oracle_dom {c : Code} {o : ℕ →. ℕ} {n : ℕ} (hn : n ∈ (c.evalq o).Dom) : ↑((c.queries o n).get hn) ⊆ o.Dom := by
  induction c generalizing n with
  | zero | succ | left | right => simp
  | oracle =>
    simp [queries, evalq, Part.bind, Part.assert, ← Part.dom_iff_mem] at hn ⊢
    exact hn
  | pair cf cg IHcf IHcg | comp cf cg IHcf IHcg =>
    simp [queries, evalq, Part.bind, Part.assert] at hn ⊢
    solve_by_elim
  | prec cf cg IHcf IHcg =>
    revert hn
    suffices ∀ a m (ham : Nat.pair a m ∈ ((cf.prec cg).evalq o).Dom), ↑(((cf.prec cg).queries o (Nat.pair a m)).get ham) ⊆ o.Dom by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m ham
    induction m with
    | zero =>
      simp [queries, evalq] at ham ⊢
      exact IHcf ham
    | succ m IHm =>
      simp [queries_prec_succ, Part.bind, Part.assert]
      simp [evalq_prec_succ] at ham
      obtain ⟨z, y, ⟨s, h1, h2⟩, ⟨t, h3⟩⟩ := ham
      use IHm h1
      grind
  | rfind' cf IHcf =>
    revert hn
    suffices ∀ a m (ham : Nat.pair a m ∈ (cf.rfind'.evalq o).Dom), ↑((cf.rfind'.queries o (Nat.pair a m)).get ham) ⊆ o.Dom by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m ham
    sorry

/--
The main theorem about `evalq`: if `evalq c o n` is defined and returns `(m, s)`, and if another oracle `o'` agrees with `o` on `s`, then `evalq c o n = evalq c o' n`.
-/
theorem evalq_spec {c : Code} {o : ℕ →. ℕ} {n : ℕ} (hn : n ∈ (c.evalq o).Dom) {o' : ℕ →. ℕ} (ho' : ∀ i ∈ (c.queries o n).get hn, o i = o' i) : c.evalq o n = c.evalq o' n := by
  induction c generalizing n with
  | zero | succ | left | right => simp [evalq]
  | oracle => simp_all [evalq, queries, Part.bind_some_eq_map]
  | pair cf cg IHcf IHcg =>
    simp [evalq] at hn ⊢
    simp [queries, evalq, Part.bind, Part.assert] at ho'
    rw [IHcf hn.1 (fun i hi => ho' i (.inl hi)), IHcg hn.2 (fun i hi => ho' i (.inr hi))]
  | comp cf cg IHcf IHcg =>
    simp [evalq] at hn ⊢
    simp [queries, evalq, Part.bind, Part.assert] at ho'
    rw [← IHcg hn.1 (fun i hi => ho' i (.inl hi))]
    simp [Part.bind, Part.assert_pos hn.1]
    rw [← IHcf hn.2 (fun i hi => ho' i (.inr hi))]
  | prec cf cg IHcf IHcg =>
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
    revert hn ho'
    suffices ∀ a m (ham : Nat.pair a m ∈ ((cf.prec cg).evalq o).Dom) (ho' : ∀ i ∈ ((cf.prec cg).queries o (Nat.pair a m)).get ham, o i = o' i), (cf.prec cg).evalq o (Nat.pair a m) = (cf.prec cg).evalq o' (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m ham ho'
    induction m with
    | zero =>
      simp at ho' ⊢
      refine IHcf ?_ ho'
      simp at ham ⊢
      exact ham
    | succ m IHm =>
      simp [evalq_prec_succ] at ham ⊢
      simp [queries_prec_succ] at ho'
      obtain ⟨y, k, ⟨s, hs⟩, ⟨t, ht⟩⟩ := ham
      have h1 : (cf.prec cg).evalq o (Nat.pair a m) = (cf.prec cg).evalq o' (Nat.pair a m) := by
        refine IHm hs.1 ?_
        intro i hi
        refine ho' i ?_
        simp [Part.bind, Part.assert]
        exact .inl hi
      have h2 : cg.evalq o (Nat.pair a (Nat.pair m k)) = cg.evalq o' (Nat.pair a (Nat.pair m k)) := by
        refine IHcg ht.1 ?_
        intro i hi
        refine ho' i ?_
        simp [queries, Part.bind, Part.assert] at hi ⊢
        rw [Part.get_eq_of_mem ht] at hi
        have := congrArg Prod.fst <| (Part.get_eq_iff_mem hs.1).mpr hs
        simp at this
        rw [← this] at ht
        rw [Part.get_eq_of_mem ht]
        exact .inr hi
      rw [← h1, Part.bind_of_mem hs, Part.bind_of_mem hs, ← h2]
  | rfind' cf IHcf =>
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
    revert hn ho'
    suffices ∀ a m (ham : Nat.pair a m ∈ (cf.rfind'.evalq o).Dom) (ho' : ∀ i ∈ (cf.rfind'.queries o (Nat.pair a m)).get ham, o i = o' i), cf.rfind'.evalq o (Nat.pair a m) = cf.rfind'.evalq o' (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m ham ho'
    sorry

end RecursiveIn.Code
