module

public import Mathlib.Computability.Halting

/-!
# Lemmas about RE predicates.
-/

@[expose] public section

/--
If a sequence `s : ℕ → List α ` is primitive recursive, then the predicate `fun n => ∃ k, n ∈ s k` is RE.
-/
lemma re_of_primrec_seq {α} [Primcodable α] [DecidableEq α] {s : ℕ → List α} (hs : Primrec s) : REPred (fun a => ∃ k, a ∈ s k) := by
  -- `x ∈ l` is a primitive recursive relation in `(l, x)`.
  have hmem_list : PrimrecRel (fun (l : List α) (a : α) => a ∈ l) :=
    Primrec.eq.exists_mem_list.of_eq fun l b => ⟨fun ⟨_, ha, rfl⟩ => ha, fun h => ⟨b, h, rfl⟩⟩
  have hmem_seq : PrimrecRel (fun a k => a ∈ s k) :=
    hmem_list.comp (hs.comp Primrec.snd) Primrec.fst
  have hpartrec : Partrec₂ fun a k => Part.some (decide (a ∈ s k)) :=
    hmem_seq.decide.to₂.to_comp.partrec₂
  -- Nat.rfind (fun k => Part.some (decide (x ∈ s k))) has domain p1 x
  refine (Partrec.rfind hpartrec).dom_re.of_eq fun a => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff]
  constructor
  · rintro ⟨k, hk, -⟩; exact ⟨k, decide_eq_true_iff.mp hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk], fun _ => trivial⟩

end
