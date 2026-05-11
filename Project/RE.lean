module

public import Mathlib.Computability.Halting

@[expose] public section

variable {α β} [Primcodable α] [Primcodable β]

/--
If a sequence `s : ℕ → List α ` is primitive recursive, then the predicate `fun n => ∃ k, n ∈ s k` is RE.
-/
lemma re_of_primrec_seq [DecidableEq α] {s : ℕ → List α} (hs : Primrec s) : REPred (fun x => ∃ k, x ∈ s k) := by
  -- `x ∈ l` is a primitive recursive relation in `(l, x)`.
  have hmem_list : PrimrecRel (fun (l : List α) (x : α) => x ∈ l) :=
    Primrec.eq.exists_mem_list.of_eq fun l b => ⟨fun ⟨_, ha, rfl⟩ => ha, fun h => ⟨b, h, rfl⟩⟩
  have hmem_seq : PrimrecRel (fun x k => x ∈ s k) :=
    hmem_list.comp (hs.comp Primrec.snd) Primrec.fst
  have hpartrec : Partrec₂ fun x k => Part.some (decide (x ∈ s k)) :=
    hmem_seq.decide.to₂.to_comp.partrec₂
  -- Nat.rfind (fun k => Part.some (decide (x ∈ s k))) has domain p1 x
  refine (Partrec.rfind hpartrec).dom_re.of_eq fun x => ?_
  simp only [Nat.rfind_dom, Part.mem_some_iff]
  constructor
  · rintro ⟨k, hk, -⟩; exact ⟨k, decide_eq_true_iff.mp hk.symm⟩
  · rintro ⟨k, hk⟩; exact ⟨k, by simp [hk], fun _ => trivial⟩

namespace REPred

/--
If `p : α → Prop` is an RE predicate and `f : β → α` is computable, then `p ∘ f : β → Prop` is an RE predicate.
-/
lemma comp_computable {p : α → Prop} (hp : REPred p) {f : β → α} (hf : Computable f) : REPred (p ∘ f) :=
  hp.comp (hf.partrec)

end REPred

end
