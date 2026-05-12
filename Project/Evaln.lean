module

public import Project.OracleCode
public import Project.List

/-!
Mathlib defines `Nat.Partrec.Code.evaln`, a modified evaluation which returns an `Option ℕ` instead of a `Part ℕ`. To avoid undecidability, it takes a parameter `k` and fails if it encounters a number `≥ k` in the course of its execution. There are two generalizations of this that we need in the oracle setting:

The first is like `Nat.Partrec.Code.evaln`, except that it also takes in a list of the first `k` oracle values. This function is primitive recursive. This fact is crucial to constructions like Friedberg-Muchnik, where each stage of the construction requires reasoning about evaluation with partial oracles, and also each stage is required to be computable. We call this function `evalp`, where `p` is for partial.

The second is a relativization of `Nat.Partrec.Code.evaln` that takes in the whole oracle `o : ℕ → ℕ` and plugs the first `k` values into `evalp k`. This function is primitive recursive *relative to `o`*, and this is used to show that `eval` is recursive in `o`. This fact is crucial to reasoning about relative (non)computability; for instance we need it to prove the relative fixed point theorem. We call this function `evaln`, since it is a direct relativization of the original `evaln`.
-/

@[expose] public section

namespace Nat.RecursiveIn.Code

/--
-/
def evalp : ℕ → Code → List ℕ → ℕ → Option ℕ
  | 0, _ => fun _ _ => Option.none
  | k + 1, zero => fun _ n => do
    guard (n ≤ k)
    return 0
  | k + 1, succ => fun _ n => do
    guard (n ≤ k)
    return (Nat.succ n)
  | k + 1, left => fun _ n => do
    guard (n ≤ k)
    return n.unpair.1
  | k + 1, right => fun _ n => do
    guard (n ≤ k)
    pure n.unpair.2
  | k + 1, oracle => fun o n => do
    guard (n ≤ k)
    o[n]?
  | k + 1, pair cf cg => fun o n => do
    guard (n ≤ k)
    Nat.pair <$> evalp (k + 1) cf o n <*> evalp (k + 1) cg o n
  | k + 1, comp cf cg => fun o n => do
    guard (n ≤ k)
    let x ← evalp (k + 1) cg o n
    evalp (k + 1) cf o x
  | k + 1, prec cf cg => fun o n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evalp (k + 1) cf o a) fun y => do
        let i ← evalp k (prec cf cg) o (Nat.pair a y)
        evalp (k + 1) cg o (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun o n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evalp (k + 1) cf o (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evalp k (rfind' cf) o (Nat.pair a (m + 1))

/--
-/
def evaln (k : ℕ) (c : Code) (o : ℕ → ℕ) (n : ℕ) : Option ℕ :=
    evalp k c (List.ofFnNat o k) n

/--
If two oracles `o` and `o'` agree below `k`, then their `evaln k`'s agree.
-/
lemma evaln_eq_of_oracle_eq {k : ℕ} {c : Code} {o o'} {n : ℕ} (heq : ∀ i < k, o i = o' i): evaln k c o n = evaln k c o' n := by
  simp [evaln, List.ofFnNat_eq_iff.mpr heq]

/--
If `evalp k ...` halts on input `n`, then `n < k`.
-/
theorem evalp_bound : ∀ {k c o n x}, x ∈ evalp k c o n → n < k
  | 0, c, o, n, x, h => by simp [evalp] at h
  | k + 1, c, o, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evalp] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

/--
If `evaln k ...` halts on input `n`, then `n < k`.
-/
theorem evaln_bound : ∀ {k c o n x}, x ∈ evaln k c o n → n < k :=
  evalp_bound

/--
-/
theorem evalp_mono : ∀ {k₁ k₂ c o n x}, k₁ ≤ k₂ → x ∈ evalp k₁ c o n → x ∈ evalp k₂ c o n
  | 0, k₂, c, o, n, x, _, h => by simp [evalp] at h
  | k + 1, k₂ + 1, c, o, n, x, hl, h => by
    have hl' := Nat.le_of_succ_le_succ hl
    have :
      ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
        k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂ h₃
      exact ⟨le_trans h₂ h, h₁ h₃⟩
    simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
    induction c generalizing x n <;> rw [evalp] at h ⊢ <;> refine this hl' (fun h => ?_) h
    iterate 5 exact h
    case pair cf cg hf hg _ =>
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evalp_mono hl' h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evalp_mono hl'

/--
-/
theorem evalp_mono_in_oracle : ∀ {k c o₁ o₂ n x}, o₁ <+: o₂ → x ∈ evalp k c o₁ n → x ∈ evalp k c o₂ n
  | 0, c, o₁, o₂, n, x, _, h => by simp [evalp] at h
  | k + 1, c, o₁, o₂, n, x, hpre, h => by
    have :
      ∀ {k n x : ℕ} {o₁ o₂ : Option ℕ},
        (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂
      exact ⟨h₁, h h₂⟩
    induction c generalizing x n <;> rw [evalp] at h ⊢ <;> refine this (fun h => ?_) h
    iterate 4 exact h
    case oracle =>
      rw [List.prefix_iff_forall_getElem?] at hpre
      exact hpre _ _ h
    case pair cf cg hf hg _ =>
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg _ =>
      revert h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evalp_mono_in_oracle hpre h₁, hg _ _ h₂⟩
    case rfind' cf hf _ =>
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact evalp_mono_in_oracle hpre

/--
-/
theorem evaln_mono : ∀ {k₁ k₂ c o n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c o n → x ∈ evaln k₂ c o n := by
  intro k₁ k₂ c o n x hle h
  exact evalp_mono_in_oracle (by simpa) (evalp_mono hle h)

/--
-/
theorem evalp_take : ∀ {k c o n x}, x ∈ evalp k c o n → x ∈ evalp k c (o.take k) n
  | 0, c, o, n, x, h => by simp [evalp] at h
  | k + 1, c, o, n, x, h => by
    have :
      ∀ {k n x : ℕ} {o₁ o₂ : Option ℕ},
        (x ∈ o₁ → x ∈ o₂) →
          x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k); o₂ } := by
      simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
        exists_and_left, exists_const, and_imp]
      introv h h₁ h₂
      exact ⟨h₁, h h₂⟩
    induction c generalizing x n <;> rw [evalp] at h ⊢
    iterate 4 exact this id h
    case oracle => by_cases hn : n ≤ k <;> simp_all [Nat.lt_succ_iff]
    case pair cf cg hf hg =>
      refine this (fun h => ?_) h
      simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
        simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
          Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
      exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    case comp cf cg hf hg =>
      refine this (fun h => ?_) h
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
      exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    case prec cf cg hf hg =>
      refine this ?_ h
      simp only [unpaired, bind, Option.mem_def]
      induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
      · apply hf
      · exact fun y h₁ h₂ => ⟨y, evalp_mono_in_oracle (List.take_prefix_take_left (Nat.le_succ _)) (evalp_take h₁), hg _ _ h₂⟩
    case rfind' cf hf =>
      refine this (fun h => ?_) h
      simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
        simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
          Option.bind_eq_some_iff] at h ⊢
      refine h.imp fun x => And.imp (hf _ _) ?_
      by_cases x0 : x = 0 <;> simp [x0]
      exact fun h₁ => evalp_mono_in_oracle (List.take_prefix_take_left (Nat.le_succ _)) (evalp_take h₁)

/--
-/
theorem evalp_sound : ∀ {k c o n x}, x ∈ evalp k c o n → x ∈ eval c (fun i => o[i]?) n
  | 0, _, o, n, x, h => by simp [evalp] at h
  | k + 1, c, o, n, x, h => by
    induction c generalizing x n <;> simp [eval, evalp, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 5 simpa [pure, PFun.pure, eq_comm] using h
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evalp_mono k.le_succ h₁
          simp [evalp, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · have := evalp_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

/--
-/
theorem evaln_sound : ∀ {k c o n x}, x ∈ evaln k c o n → x ∈ eval c o n
  | 0, _, o, n, x, h => by simp [evaln, evalp] at h
  | k + 1, c, o, n, x, h => by
    induction c generalizing x n <;> simp [eval, evaln, evalp, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
      obtain ⟨_, h⟩ := h
    iterate 4 simpa [pure, PFun.pure, eq_comm] using h
    case oracle =>
      exact h.2.symm
    case pair cf cg hf hg _ =>
      rcases h with ⟨y, ef, z, eg, rfl⟩
      exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
    case comp cf cg hf hg _ =>
      rcases h with ⟨y, eg, ef⟩
      exact ⟨_, hg _ _ eg, hf _ _ ef⟩
    case prec cf cg hf hg _ =>
      revert h
      induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
      | zero => apply hf
      | succ m IH =>
        refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
        · have := evalp_mono k.le_succ h₁
          simp [evalp, Option.bind_eq_some_iff] at this
          exact this.2
        · exact hg _ _ h₂
    case rfind' cf hf _ =>
      rcases h with ⟨m, h₁, h₂⟩
      by_cases m0 : m = 0 <;> simp [m0] at h₂
      · exact
          ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
      · apply evalp_take at h₂
        rw [List.take_ofFnNat _ (Nat.le_succ _)] at h₂
        have := evaln_sound h₂
        simp [eval] at this
        rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
        refine
          ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
            simp [add_comm, add_left_comm]⟩
        rcases i with - | i
        · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
        · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
          exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

/--
-/
theorem evalp_complete {c o n x} : x ∈ eval c (fun i => o[i]?) n ↔ ∃ k, x ∈ evalp k c o n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evalp_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evalp (k + 1) c o n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
      simp [eval, evalp, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
  | oracle => exact ⟨⟨_, le_rfl⟩, h⟩
  | pair cf cg hf hg =>
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁, _,
        evalp_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evalp_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁, _,
        evalp_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evalp_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
    induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
    | zero =>
      intro h
      rcases hf h with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evalp_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      intro y hy hx
      rcases IH (n := max n (Nat.pair n₁ m)) hy with ⟨k₁, nk₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      refine
        ⟨(max k₁ k₂).succ,
          (Nat.le_succ_of_le <| le_max_of_le_left <|
            le_trans (le_max_left n (Nat.pair n₁ m)) nk₁), y,
          evalp_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
          evalp_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
      simp only [evalp.eq_9, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
        Option.guard_eq_some', exists_and_left, exists_const]
      exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
  | rfind' cf hf =>
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evalp (k + 1) (rfind' cf) o (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evalp, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evalp, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evalp_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁
      use a
      use evalp_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simpa [a0, add_comm, add_left_comm] using
        evalp_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
  | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

/--
This is essentially the use principle for total oracles.
-/
theorem evaln_complete {c} {o : ℕ → ℕ} {n x} : x ∈ eval c o n ↔ ∃ k, x ∈ evaln k c o n := by
  refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
  rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k + 1) c o n
  · exact ⟨k + 1, h⟩
  induction c generalizing n x with
  | oracle =>
    simp [eval, evaln, evalp, Option.bind_eq_some_iff] at h ⊢
    exact ⟨_, le_rfl, by simp [h]⟩
  | pair cf cg hf hg =>
    simp [eval, evaln, evalp, Seq.seq, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨x, hx, y, hy, rfl⟩
    rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    refine
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
  | comp cf cg hf hg =>
    simp [eval, evaln, evalp, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨y, hy, hx⟩
    rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
    refine ⟨max k₁ k₂, ?_⟩
    exact
      ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁, _,
        evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
        evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
  | prec cf cg hf hg =>
    revert h
    have := n.pair_unpair
    generalize n.unpair.1 = n₁, n.unpair.2 = n₂ at this
    subst this
    induction n₂ generalizing x with
    | zero =>
      simp [eval_prec_zero, evaln, evalp, Option.bind_eq_some_iff]
      intro hx
      rcases hf hx with ⟨k, hk⟩
      exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
    | succ m IH =>
      simp [eval_prec_succ, evaln, evalp, Option.bind_eq_some_iff]
      intro y hy hx
      rcases IH hy with ⟨k₁, hk₁⟩
      rcases hg hx with ⟨k₂, hk₂⟩
      let kₘ := max (max k₁ k₂ + 1) (Nat.pair n₁ (m+1))
      refine ⟨kₘ, le_max_right _ _, y, ?_, ?_⟩
      · apply evaln_mono (by omega : k₁ + 1 ≤ kₘ) at hk₁
        exact evalp_mono_in_oracle (by simp) hk₁
      · apply evaln_mono (by omega : k₂ + 1 ≤ kₘ + 1) at hk₂
        exact evalp_mono_in_oracle (by simp) hk₂
  | rfind' cf hf =>
    simp [eval, evaln, evalp, pure, Option.bind_eq_some_iff] at h ⊢
    rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    suffices ∃ k, y + n.unpair.2 ∈ evaln (k + 1) (rfind' cf) o (Nat.pair n.unpair.1 n.unpair.2) by
      simpa [evaln, evalp, Option.bind_eq_some_iff]
    revert hy₁ hy₂
    generalize n.unpair.2 = m
    intro hy₁ hy₂
    induction y generalizing m with simp [evaln, evalp, Option.bind_eq_some_iff]
    | zero =>
      simp at hy₁
      rcases hf hy₁ with ⟨k, hk⟩
      exact ⟨_, Nat.le_of_lt_succ <| evalp_bound hk, _, hk, by simp⟩
    | succ y IH =>
      rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
      rcases hf ha with ⟨k₁, hk₁⟩
      rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
          fun {i} hi => by
          simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
            hy₂ (Nat.succ_lt_succ hi) with
        ⟨k₂, hk₂⟩
      use (max k₁ k₂).succ
      rw [zero_add] at hk₁
      use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evalp_bound hk₁
      use a
      use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
      simp [a0, add_comm, add_left_comm]
      apply evaln_mono (Nat.succ_le_succ <| le_max_right k₁ _) at hk₂
      exact evalp_mono_in_oracle (by simp) hk₂
  | _ =>
    simp [eval, evaln, evalp, pure, PFun.pure, Option.bind_eq_some_iff] at h ⊢
    exact ⟨⟨_, le_rfl⟩, h.symm⟩

section

open Primrec Encodable Denumerable

/--
Short for "lookup". Interpret `L` as the partial function `(ℕ × Code × List ℕ) × ℕ → ℕ`, `L(p, n) = evalp p.1 p.2.1 p.2.2 n`.
-/
private def lup (L : List (List (Option ℕ))) (p : ℕ × Code × List ℕ) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

/--
`lup` is primitive recursive.
-/
private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

/--
`G` takes in `L` as described above, and generates the next list to append to `L`, corresponding to the values of `evalp k c o`.
-/
private def G (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × Code × List ℕ) L.length
    let k := a.1
    let c := a.2.1
    let o := a.2.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.RecursiveIn.Code.recOn c
          (some 0)
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (o[n]?)
          (fun cf cg _ _ => do
            let x ← lup L (k, cf, o) n
            let y ← lup L (k, cg, o) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg, o) n
            lup L (k, cf, o) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf, o) z) fun y => do
              let i ← lup L (k', c, o) (Nat.pair z y)
              lup L (k, cg, o) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf, o) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c, o) (Nat.pair z (m + 1)))

private theorem hG : Primrec G := by
  have a := (Primrec.ofNat (ℕ × Code × List ℕ)).comp (Primrec.list_length (α := List (Option ℕ)))
  have k := Primrec.fst.comp a
  refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  replace k := k.comp (Primrec.fst (β := ℕ))
  have n := Primrec.snd (α := List (List (Option ℕ))) (β := ℕ)
  refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  have k := k.comp (Primrec.fst (β := ℕ))
  have n := n.comp (Primrec.fst (β := ℕ))
  have k' := Primrec.snd (α := List (List (Option ℕ)) × ℕ) (β := ℕ)
  have c := Primrec.fst.comp <| Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  have o := Primrec.snd.comp <| Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  apply
    Nat.RecursiveIn.Code.primrec_recOn c
      (_root_.Primrec.const (some 0))
      (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
      (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
      (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
      (Primrec.list_getElem?.comp o (.comp .snd .fst))
  · -- `pair`.
    have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have o := o.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair (cf.pair o)).pair n) ?_
    unfold Primrec₂
    conv =>
      congr
      · ext p
        dsimp only []
        erw [Option.bind_eq_bind, ← Option.map_eq_bind]
    refine Primrec.option_map ((hlup.comp <| L.pair <| (k.pair (cg.pair o)).pair n).comp .fst) ?_
    exact Primrec₂.natPair.comp (.comp .snd .fst) .snd
  · -- `comp`.
    have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have o := o.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair (cg.pair o)).pair n) ?_
    unfold Primrec₂
    have h :=
      hlup.comp ((L.comp .fst).pair <| ((k.pair (cf.pair o)).comp .fst).pair .snd)
    exact h
  · -- `prec`.
    have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have o1 := o.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have cg := (Primrec.fst.comp Primrec.snd).comp
      (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Code × Option ℕ × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    refine
      Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n))
        (hlup.comp <| L.pair <| (k.pair (cf.pair o1)).pair z)
        (?_ : Primrec _)
    have L := L.comp (Primrec.fst (β := ℕ))
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := Primrec.snd
      (α := ((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) (β := ℕ)
    have h₁ := hlup.comp <| L.pair <| (((k'.pair (c.pair o)).comp Primrec.fst).comp Primrec.fst).pair <|
        (Primrec₂.natPair.comp z y)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have z := z.comp (Primrec.fst (β := ℕ))
    have y := y.comp (Primrec.fst (β := ℕ))
    have i := Primrec.snd
      (α := (((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) × ℕ)
      (β := ℕ)
    have h₂ := hlup.comp ((L.comp Primrec.fst).pair <|
      ((k.pair (cg.pair o1)).comp <| Primrec.fst.comp Primrec.fst).pair <|
        Primrec₂.natPair.comp z <| Primrec₂.natPair.comp y i)
    exact h₂
  · -- `rfind'`.
    have L := (Primrec.fst.comp Primrec.fst).comp
      (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Option ℕ))
    have k := k.comp (Primrec.fst (β := Code × Option ℕ))
    have o1 := o.comp (Primrec.fst (β := Code × Option ℕ))
    have n := n.comp (Primrec.fst (β := Code × Option ℕ))
    have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
        (β := Code × Option ℕ))
    have z := Primrec.fst.comp (Primrec.unpair.comp n)
    have m := Primrec.snd.comp (Primrec.unpair.comp n)
    have h₁ := hlup.comp <| L.pair <| (k.pair (cf.pair o1)).pair (Primrec₂.natPair.comp z m)
    refine Primrec.option_bind h₁ (?_ : Primrec _)
    have m := m.comp (Primrec.fst (β := ℕ))
    refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
    unfold Primrec₂
    exact (hlup.comp ((L.comp Primrec.fst).pair <|
      ((k'.pair (c.pair o)).comp <| Primrec.fst.comp Primrec.fst).pair
        (Primrec₂.natPair.comp (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)))).comp
      Primrec.fst

private theorem evalp_map (k c o n) :
    ((List.range k)[n]?.bind fun a => evalp k c o a) = evalp k c o n := by
  by_cases kn : n < k
  · simp [List.getElem?_range kn]
  · rw [List.getElem?_eq_none]
    · cases e : evalp k c o n
      · rfl
      exact kn.elim (evalp_bound e)
    simpa using kn

/--
`evalp` is primitive recursive.
-/
theorem primrec_evalp : Primrec fun a : (ℕ × Code × List ℕ) × ℕ => evalp a.1.1 a.1.2.1 a.1.2.2 a.2 :=
  have :
    Primrec₂ fun (_ : Unit) (n : ℕ) =>
      let a := ofNat (ℕ × Code × List ℕ) n
      (List.range a.1).map (evalp a.1 a.2.1 a.2.2) :=
    Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
      simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
        Nat.pair_unpair, Option.some_inj]
      refine List.map_congr_left fun n => ?_
      have : List.range p = List.range (Nat.pair p.unpair.1 (Nat.pair (encode (ofNat Code p.unpair.2.unpair.1)) (encode (ofNat (List ℕ) p.unpair.2.unpair.2)))) := by
        simp
      rw [this]
      generalize p.unpair.1 = k
      generalize ofNat Code p.unpair.2.unpair.1 = c
      generalize ofNat (List ℕ) p.unpair.2.unpair.2 = o
      intro nk
      rcases k with - | k'
      · simp [evalp]
      let k := k' + 1
      simp only
      simp only [List.mem_range, Nat.lt_succ_iff] at nk
      have hg :
        ∀ {k' c' o' n},
          Nat.pair k' (Nat.pair (encode c') (encode o')) < Nat.pair k (Nat.pair (encode c) (encode o)) →
            lup ((List.range (Nat.pair k (Nat.pair (encode c) (encode o)))).map fun n =>
              (List.range n.unpair.1).map (evalp n.unpair.1 (ofNat Code n.unpair.2.unpair.1) (ofNat (List ℕ) n.unpair.2.unpair.2))) (k', c', o') n =
            evalp k' c' o' n := by
        intro k₁ c₁ o₁ n₁ hl
        simp [lup, List.getElem?_range hl, evalp_map, Bind.bind, Option.bind_map]
      obtain - | - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
        simp [evalp, nk, Bind.bind, Functor.map, Seq.seq, pure]
      · obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
        have lfo := Nat.pair_lt_pair_left (encode o) lf
        have lgo := Nat.pair_lt_pair_left (encode o) lg
        rw [hg (Nat.pair_lt_pair_right _ lfo), hg (Nat.pair_lt_pair_right _ lgo)]
        cases evalp k cf o n
        · rfl
        cases evalp k cg o n <;> rfl
      · obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
        have lfo := Nat.pair_lt_pair_left (encode o) lf
        have lgo := Nat.pair_lt_pair_left (encode o) lg
        rw [hg (Nat.pair_lt_pair_right _ lgo)]
        cases evalp k cg o n
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lfo)]
      · obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
        have lfo := Nat.pair_lt_pair_left (encode o) lf
        have lgo := Nat.pair_lt_pair_left (encode o) lg
        rw [hg (Nat.pair_lt_pair_right _ lfo)]
        cases n.unpair.2
        · rfl
        simp only
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
        cases evalp k' _ _ _
        · rfl
        simp [k, hg (Nat.pair_lt_pair_right _ lgo)]
      · have lf := encode_lt_rfind' cf
        have lfo := Nat.pair_lt_pair_left (encode o) lf
        rw [hg (Nat.pair_lt_pair_right _ lfo)]
        rcases evalp k cf o n with - | x
        · rfl
        simp only [Option.bind_some]
        cases x <;> simp
        rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
  (Primrec.option_bind
    (Primrec.list_getElem?.comp (this.comp (_root_.Primrec.const ())
      (Primrec.encode_iff.2 Primrec.fst)) Primrec.snd) Primrec.snd.to₂).of_eq
    fun ⟨⟨k, c, o⟩, n⟩ => by simp [evalp_map, Option.bind_map]

/--
`evaln` is computable relative to its oracle.

TODO: if there is `PrimrecIn`, then we should use that instead.
-/
theorem computableIn_evaln (o : ℕ → ℕ) : ComputableIn {↑o} fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 o a.2 := by
  -- TODO
  sorry

end

section

open Partrec Computable Denumerable

theorem eval_eq_rfindOpt (c : Code) (o : ℕ → ℕ) (n : ℕ) : eval c o n = Nat.rfindOpt fun k => evaln k c o n :=
  Part.ext fun x => by
    refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
    intro a m n hl; apply evaln_mono hl

/--
`eval` is recursive in its *total* oracle.
-/
theorem recursiveIn₂_eval (o : ℕ → ℕ) : RecursiveIn₂ {↑o} (fun c n => eval c o n) :=
  -- TODO
  sorry
  -- (Partrec.rfindOpt
  --   (primrec_evalp.to_comp.comp
  --     ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂)
      -- .of_eq
    -- fun a => by simp [eval_eq_rfindOpt]

/-- **Relative Roger's fixed-point theorem**: any total, computable `f` has a fixed point.
That is, under the interpretation given by `Nat.RecursiveIn.Code.eval`, there is a code `c`
such that `c` and `f c` have the same evaluation, *for all oracles `o`*.

TODO: Is this the right relativization?
-/
theorem fixed_point {f : Code → Code} (hf : Computable f) : ∃ c : Code, eval (f c) = eval c :=
  sorry
-- let g (o : ℕ →. ℕ) (x y : ℕ) : Part ℕ := eval (ofNat Code x) o x >>= fun b => eval (ofNat Code b) o y
--   have : Partrec₂ g :=
--     (eval_part.comp ((Computable.ofNat _).comp fst) fst).bind
--       (eval_part.comp ((Computable.ofNat _).comp snd) (snd.comp fst)).to₂
--   let ⟨cg, eg⟩ := exists_code.1 this
--   have eg' : ∀ a n, eval cg (Nat.pair a n) = Part.map encode (g a n) := by simp [eg]
--   let F (x : ℕ) : Code := f (curry cg x)
--   have : Computable F :=
--     hf.comp (primrec₂_curry.comp (_root_.Primrec.const cg) _root_.Primrec.id).to_comp
--   let ⟨cF, eF⟩ := exists_code.1 this
--   have eF' : eval cF (encode cF) = Part.some (encode (F (encode cF))) := by simp [eF]
--   ⟨curry cg (encode cF),
--     funext fun n =>
--       show eval (f (curry cg (encode cF))) n = eval (curry cg (encode cF)) n by
--         simp [F, g, eg', eF', Part.map_id']⟩

-- TODO:
/--
**Kleene's second recursion theorem**

TODO: Is this the right relativization?
-/
theorem fixed_point₂ {f : Code → ℕ →. ℕ} {o} (hf : RecursiveIn₂ {o} f) : ∃ c : Code, eval c o = f c :=
  sorry
--   let ⟨cf, ef⟩ := exists_code.1 hf
--   (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
--     fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

end

end Nat.RecursiveIn.Code
