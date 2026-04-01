module

public import Project.OracleCode

@[expose] public section

namespace Nat

def rfindFold {α β} (f : ℕ →. Bool × α) (g : α → β → β) (init : β) : Part (ℕ × β) := do
  let n ← rfind (Prod.fst <$> f)
  let b ← n.succ.rec (pure init) fun k pb => do
    let b ← pb
    let (_, a) ← f k
    pure (g a b)
  pure (n, b)

lemma rfindFold_fst_eq_rfind {α β} {f : ℕ →. Bool × α} {g : α → β → β} {init} : Prod.fst <$> rfindFold f g init = rfind (Prod.fst <$> f) := by
  sorry

lemma rfindFold_dom {α β} {f : ℕ →. Bool × α} {g : α → β → β} {init} {p} (h : p ∈ rfindFold f g init) : ∀ k ≤ p.1, (f k).Dom := by
  sorry

lemma rfindFold_snd_eq_fold {α β} {f : ℕ →. Bool × α} {g : α → β → β} {init} {p} (h : p ∈ rfindFold f g init) :
    p.2 = (p.1+1).fold (fun k hk b => g ((f k).get (rfindFold_dom h k (le_of_lt_succ hk))).2 b) init := by
  sorry

end Nat

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
    Nat.unpaired fun a m => Prod.map (· + m) id <$>
      Nat.rfindFold (fun n => Prod.map (· = 0) id <$> cf.evalq o (Nat.pair a (n + m))) (· ∪ ·) ∅

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
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
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
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
    suffices ∀ a m, Prod.fst <$> (cf.rfind').evalq o (Nat.pair a m) = (cf.rfind').eval o (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2 <;> simp only [Nat.pair_unpair]
    intro a m
    have : (fun n => Part.map (fun x => decide (x = 0)) (Prod.fst <$> cf.evalq o (Nat.pair a (n+m)))) = (fun n => Part.map (fun x => decide (x = 0)) (cf.eval o (Nat.pair a (n + m)))) := by
      funext n
      rw [IHcf]
    simp [eval, evalq]
    rw [← this, Part.map_map, Prod.map_fst', ← Part.map_map, ← Part.map_eq_map, ← Part.map_eq_map, Nat.rfindFold_fst_eq_rfind]
    rfl

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
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
    revert hn
    suffices ∀ a m (hm : Nat.pair a m ∈ ((cf.prec cg).evalq o).Dom), ↑(((cf.prec cg).queries o (Nat.pair a m)).get hm) ⊆ o.Dom by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m hm
    induction m with
    | zero =>
      simp [queries, evalq] at hm ⊢
      exact IHcf hm
    | succ m IHm =>
      simp [queries_prec_succ, Part.bind, Part.assert]
      simp [evalq_prec_succ] at hm
      obtain ⟨z, y, ⟨s, h1, h2⟩, ⟨t, h3⟩⟩ := hm
      use IHm h1
      grind
  | rfind' cf IHcf =>
    -- TODO: Is there a better way to replace `n` by `Nat.pair a m`.
    revert hn
    suffices ∀ a m (hm : Nat.pair a m ∈ (cf.rfind'.evalq o).Dom), ↑((cf.rfind'.queries o (Nat.pair a m)).get hm) ⊆ o.Dom by
      convert this n.unpair.1 n.unpair.2
      simp only [Nat.pair_unpair]
    intro a m hm
    simp [evalq] at hm
    let p := Nat.rfindFold (fun n => Part.map (Prod.map (fun x => decide (x = 0)) id) (cf.evalq o (Nat.pair a (n + m)))) (· ∪ ·) ∅ |>.get hm
    have hp : p ∈ _ := Part.get_mem hm
    simp [queries, evalq]
    rw [Nat.rfindFold_snd_eq_fold hp]
    have hn := Nat.rfindFold_dom hp
    simp at hn
    simp only [Part.map_get, Function.comp_apply, Prod.map_snd, id_eq]
    simp only [queries, Part.map_eq_map, Part.map_get, Function.comp_apply] at IHcf
    suffices ∀ x (hx : x ≤ p.1 + 1), ↑(x.fold (fun k hk b => ((cf.evalq o (Nat.pair a (k + m))).get (by grind)).2 ∪ b) ∅) ⊆ o.Dom from
      this (p.1 + 1) le_rfl
    intro x hx
    induction x with
    | zero => simp
    | succ x IHx =>
      simp
      exact ⟨IHcf <| hn x (Nat.le_of_succ_le_succ hx), IHx <| Nat.le_of_succ_le hx⟩

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
    suffices ∀ a m (hm : Nat.pair a m ∈ ((cf.prec cg).evalq o).Dom) (ho' : ∀ i ∈ ((cf.prec cg).queries o (Nat.pair a m)).get hm, o i = o' i), (cf.prec cg).evalq o (Nat.pair a m) = (cf.prec cg).evalq o' (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2
      simp
    intro a m hm ho'
    induction m with
    | zero =>
      simp at ho' ⊢
      refine IHcf ?_ ho'
      simp at hm ⊢
      exact hm
    | succ m IHm =>
      simp [evalq_prec_succ] at hm ⊢
      simp [queries_prec_succ] at ho'
      obtain ⟨y, k, ⟨s, hs⟩, ⟨t, ht⟩⟩ := hm
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
    suffices ∀ a m (hm : Nat.pair a m ∈ (cf.rfind'.evalq o).Dom) (ho' : ∀ i ∈ (cf.rfind'.queries o (Nat.pair a m)).get hm, o i = o' i), cf.rfind'.evalq o (Nat.pair a m) = cf.rfind'.evalq o' (Nat.pair a m) by
      convert this n.unpair.1 n.unpair.2
      simp only [Nat.pair_unpair]
    intro a m hm ho'
    sorry

end RecursiveIn.Code
