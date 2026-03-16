module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringDegree

/-!
# Gödel Numbering for Partial Recursive Functions with an Oracle.

This file is a "relativized" version of `Mathlib/Computability/PartrecCode.lean`.

It defines `OCode`, an inductive datatype describing codes for partial recursive functions on ℕ with an oracle. It defines an encoding for these codes, and proves that the constructors are primitive recursive with respect to the encoding.

Note that although `RecursiveIn` takes a set of oracles, `OCode` allows just a single oracle. Another option would have been to allow a family of oracles indexed by a `Primcodable` type (i.e., we would define a structure `OCode (α : Type*) [Primcodable α]`). But (1) such a family can be computably encoded as a single oracle anyway, and (2) the need to consider indexed families of oracles seems rare enough that it was not worth the extra complication.

It also defines the evaluation of an `OCode` as a partial function, and proves that a function `f` is Turing reducible to `g` if and only if it is the evaluation of some `OCode` using `g` as an oracle.

## Main Definitions

* `Nat.Partrec.OCode`: Inductive datatype for partial recursive functions with an oracle.
* `Nat.Partrec.OCode.encodeOCode`: A (computable) encoding of an `OCode` as a natural number.
* `Nat.Partrec.OCode.ofNatOCode`: The inverse of this encoding.
* `Nat.Partrec.OCode.eval`: The interpretation of an `OCode` as a partial function.

## Main Results

* `Nat.Partrec.OCode.rec_prim`: Recursion on `Nat.Partrec.OCode` is primitive recursive.
* `Nat.Partrec.OCode.rec_computable`: Recursion on `Nat.Partrec.OCode` is computable.
* `Nat.Partrec.OCode.smn`: The $S_n^m$ theorem.
* `Nat.Partrec.OCode.exists_code`: Partial recursiveness is equivalent to being the eval of a code.
* `Nat.Partrec.OCode.evaln_prim`: `evaln` is primitive recursive.
* `Nat.Partrec.OCode.fixed_point`: Roger's fixed point theorem.
* `Nat.Partrec.OCode.fixed_point₂`: Kleene's second recursion theorem.
-/

@[expose] public section

open Encodable Denumerable

namespace Nat.Partrec

/-- Code for partial recursive functions from ℕ to ℕ with an oracle.
See `Nat.Partrec.Code.eval` for the interpretation of these constructors.
-/
inductive OCode : Type
  | zero : OCode
  | succ : OCode
  | left : OCode
  | right : OCode
  | oracle : OCode
  | pair : OCode → OCode → OCode
  | comp : OCode → OCode → OCode
  | prec : OCode → OCode → OCode
  | rfind' : OCode → OCode

compile_inductive% OCode

end Nat.Partrec

namespace Nat.Partrec.OCode

open Nat.Partrec.Code

/-- A `Nat.Partrec.Code` can be converted to a `Nat.Partrec.OCode`. -/
def ofCode : Code → OCode
  | .zero => zero
  | .succ => succ
  | .left => left
  | .right => right
  | .pair cf cg => pair (ofCode cf) (ofCode cg)
  | .comp cf cg => comp (ofCode cf) (ofCode cg)
  | .prec cf cg => prec (ofCode cf) (ofCode cg)
  | .rfind' cf => rfind' (ofCode cf)

/-- The conversion from `Code` to `OCode` is injective. -/
theorem ofCode_inj : Function.Injective ofCode := by
  sorry

instance instInhabited : Inhabited OCode :=
  ⟨zero⟩

/-- An `OCode` for the constant function outputting `n`. -/
protected def const (n : ℕ) : OCode := ofCode (Code.const n)

/-- `OCode.const` is injective. -/
theorem const_inj : Function.Injective OCode.const := by
  sorry

/-- An `OCode` for the identity function. -/
protected def id : OCode := ofCode (Code.id)

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : OCode) (n : ℕ) : OCode :=
  comp c (pair (OCode.const n) OCode.id)

/-- An encoding of a `Nat.Partrec.OCode` as a ℕ. -/
def encodeOCode : OCode → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | oracle => 4
  | pair cf cg => 2 * (2 * Nat.pair (encodeOCode cf) (encodeOCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeOCode cf) (encodeOCode cg) + 1) + 5
  | prec cf cg => (2 * (2 * Nat.pair (encodeOCode cf) (encodeOCode cg)) + 1) + 5
  | rfind' cf => (2 * (2 * encodeOCode cf + 1) + 1) + 5

/--
A decoder for `Nat.Partrec.OCode.encodeOCode`, taking any ℕ to the `Nat.Partrec.OCode` it represents.
-/
def ofNatOCode : ℕ → OCode
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatOCode m.unpair.1) (ofNatOCode m.unpair.2)
    | false, true => comp (ofNatOCode m.unpair.1) (ofNatOCode m.unpair.2)
    | true, false => prec (ofNatOCode m.unpair.1) (ofNatOCode m.unpair.2)
    | true, true => rfind' (ofNatOCode m)

set_option backward.privateInPublic true in
/-- Proof that `Nat.Partrec.Code.ofNatOCode` is the inverse of `Nat.Partrec.Code.encodeOCode` -/
private theorem encode_ofNatOCode : ∀ n, encodeOCode (ofNatOCode n) = n
  | 0 => by simp [ofNatOCode, encodeOCode]
  | 1 => by simp [ofNatOCode, encodeOCode]
  | 2 => by simp [ofNatOCode, encodeOCode]
  | 3 => by simp [ofNatOCode, encodeOCode]
  | 4 => by simp [ofNatOCode, encodeOCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by
      simp only [m, div2_val]
      exact
        lt_of_le_of_lt (le_trans (Nat.div_le_self _ _) (Nat.div_le_self _ _))
          (Nat.succ_le_succ (Nat.le_add_right _ _))
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatOCode m
    have IH1 := encode_ofNatOCode m.unpair.1
    have IH2 := encode_ofNatOCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatOCode.eq_6]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeOCode, IH, IH1, IH2, Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instDenumerable : Denumerable OCode :=
  mk'
    ⟨encodeOCode, ofNatOCode, fun c => by
        induction c <;> simp [encodeOCode, ofNatOCode, Nat.div2_val, *],
      encode_ofNatOCode⟩

theorem encodeOCode_eq : encode = encodeOCode :=
  rfl

theorem ofNatOCode_eq : ofNat OCode = ofNatOCode :=
  rfl

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeOCode_eq, encodeOCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeOCode cg.encodeOCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeOCode_eq, encodeOCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeOCode_eq, encodeOCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeOCode_eq, encodeOCode]
  lia

end Nat.Partrec.OCode

section
open Primrec
namespace Nat.Partrec.OCode

theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OCode).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OCode).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat OCode).comp fst)
              (encode_iff.2 <| (Primrec.ofNat OCode).comp snd))
        (Primrec₂.const 5)

theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat OCode)
        (const 5)

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → OCode} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o) {pr : α → OCode × OCode × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → OCode × OCode × σ × σ → σ} (hco : Primrec₂ co) {pc : α → OCode × OCode × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → OCode × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : OCode) : σ :=
      Nat.Partrec.OCode.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  sorry -- TODO: Update this proof for OCode.
  -- intro _ _ _ _ F
  -- let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
  --   letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
  --   IH[m]?.bind fun s =>
  --   IH[m.unpair.1]?.bind fun s₁ =>
  --   IH[m.unpair.2]?.map fun s₂ =>
  --   cond n.bodd
  --     (cond n.div2.bodd (rf a (ofNat Code m, s))
  --       (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  --     (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
  --       (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  -- have : Primrec G₁ :=
  --   option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk <|
  --   option_bind ((list_getElem?.comp (snd.comp fst)
  --     (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
  --   option_map ((list_getElem?.comp (snd.comp fst)
  --     (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
  --   have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
  --   have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
  --   have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
  --   have m₁ := fst.comp (Primrec.unpair.comp m)
  --   have m₂ := snd.comp (Primrec.unpair.comp m)
  --   have s := snd.comp (fst.comp fst)
  --   have s₁ := snd.comp fst
  --   have s₂ := snd
  --   (nat_bodd.comp n).cond
  --     ((nat_bodd.comp <| nat_div2.comp n).cond
  --       (hrf.comp a (((Primrec.ofNat Code).comp m).pair s))
  --       (hpc.comp a (((Primrec.ofNat Code).comp m₁).pair <|
  --         ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  --     (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
  --       (hco.comp a (((Primrec.ofNat Code).comp m₁).pair <|
  --         ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂))
  --       (hpr.comp a (((Primrec.ofNat Code).comp m₁).pair <|
  --         ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  -- let G : α → List σ → Option σ := fun a IH =>
  --   IH.length.casesOn (some (z a)) fun n =>
  --   n.casesOn (some (s a)) fun n =>
  --   n.casesOn (some (l a)) fun n =>
  --   n.casesOn (some (r a)) fun n =>
  --   G₁ ((a, IH), n, n.div2.div2)
  -- have : Primrec₂ G := .mk <|
  --   nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
  --   this.comp <|
  --     ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
  --     snd.pair <| nat_div2.comp <| nat_div2.comp snd
  -- refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
  --   |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  -- iterate 4 rcases n with - | n; · simp [ofNatOCode_eq, ofNatOCode]; rfl
  -- simp only [G]; rw [List.length_map, List.length_range]
  -- let m := n.div2.div2
  -- change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
  --   = some (F a (ofNat Code (n + 4)))
  -- have hm : m < n + 4 := by
  --   simp only [m, div2_val]
  --   exact lt_of_le_of_lt
  --     (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
  --     (Nat.succ_le_succ (Nat.le_add_right ..))
  -- have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  -- have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  -- simp [G₁, m, hm, m1, m2]
  -- rw [show ofNat Code (n + 4) = ofNatOCode (n + 4) from rfl]
  -- simp [ofNatOCode]
  -- cases n.bodd <;> cases n.div2.bodd <;> rfl

/-- Recursion on `Nat.Partrec.OCode` is primitive recursive. -/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → OCode} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o) {pr : α → OCode → OCode → σ → σ → σ}
    (hpr : Primrec fun a : α × OCode × OCode × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → OCode → OCode → σ → σ → σ}
    (hco : Primrec fun a : α × OCode × OCode × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → OCode → OCode → σ → σ → σ}
    (hpc : Primrec fun a : α × OCode × OCode × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → OCode → σ → σ} (hrf : Primrec fun a : α × OCode × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : OCode) : σ :=
      Nat.Partrec.OCode.recOn c (z a) (s a) (l a) (r a) (o a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr ho
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

end Nat.Partrec.OCode
end

namespace Nat.Partrec.OCode
section

open Computable

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-- Recursion on `Nat.Partrec.OCode` is computable. -/
theorem computable_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α → OCode} (hc : Computable c)
    {z : α → σ} (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l)
    {r : α → σ} (hr : Computable r) {o : α → σ} (ho : Computable o) {pr : α → OCode × OCode × σ × σ → σ} (hpr : Computable₂ pr)
    {co : α → OCode × OCode × σ × σ → σ} (hco : Computable₂ co) {pc : α → OCode × OCode × σ × σ → σ}
    (hpc : Computable₂ pc) {rf : α → OCode × σ → σ} (hrf : Computable₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : OCode) : σ :=
      Nat.Partrec.OCode.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Computable fun a => F a (c a) := by
  sorry -- TODO: Update this proof for OCode.
  -- TODO(Mario): less copy-paste from previous proof
  -- intro _ _ _ _ F
  -- let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
  --   letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
  --   IH[m]?.bind fun s =>
  --   IH[m.unpair.1]?.bind fun s₁ =>
  --   IH[m.unpair.2]?.map fun s₂ =>
  --   cond n.bodd
  --     (cond n.div2.bodd (rf a (ofNat Code m, s))
  --       (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  --     (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
  --       (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  -- have : Computable G₁ := by
  --   refine option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk ?_
  --   refine option_bind ((list_getElem?.comp (snd.comp fst)
  --     (fst.comp <| Computable.unpair.comp (snd.comp snd))).comp fst) <| .mk ?_
  --   refine option_map ((list_getElem?.comp (snd.comp fst)
  --     (snd.comp <| Computable.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk ?_
  --   exact
  --     have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
  --     have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
  --     have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
  --     have m₁ := fst.comp (Computable.unpair.comp m)
  --     have m₂ := snd.comp (Computable.unpair.comp m)
  --     have s := snd.comp (fst.comp fst)
  --     have s₁ := snd.comp fst
  --     have s₂ := snd
  --     (nat_bodd.comp n).cond
  --       ((nat_bodd.comp <| nat_div2.comp n).cond
  --         (hrf.comp a (((Computable.ofNat Code).comp m).pair s))
  --         (hpc.comp a (((Computable.ofNat Code).comp m₁).pair <|
  --           ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  --       (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
  --         (hco.comp a (((Computable.ofNat Code).comp m₁).pair <|
  --           ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂))
  --         (hpr.comp a (((Computable.ofNat Code).comp m₁).pair <|
  --           ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  -- let G : α → List σ → Option σ := fun a IH =>
  --   IH.length.casesOn (some (z a)) fun n =>
  --   n.casesOn (some (s a)) fun n =>
  --   n.casesOn (some (l a)) fun n =>
  --   n.casesOn (some (r a)) fun n =>
  --   G₁ ((a, IH), n, n.div2.div2)
  -- have : Computable₂ G := .mk <|
  --   nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
  --   nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
  --   this.comp <|
  --     ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
  --     snd.pair <| nat_div2.comp <| nat_div2.comp snd
  -- refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
  --   |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  -- iterate 4 rcases n with - | n; · simp [ofNatOCode_eq, ofNatOCode]; rfl
  -- simp only [G]; rw [List.length_map, List.length_range]
  -- let m := n.div2.div2
  -- change G₁ ((a, (List.range (n + 4)).map fun n => F a (ofNat Code n)), n, m)
  --   = some (F a (ofNat Code (n + 4)))
  -- have hm : m < n + 4 := by
  --   simp only [m, div2_val]
  --   exact lt_of_le_of_lt
  --     (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
  --     (Nat.succ_le_succ (Nat.le_add_right ..))
  -- have m1 : m.unpair.1 < n + 4 := lt_of_le_of_lt m.unpair_left_le hm
  -- have m2 : m.unpair.2 < n + 4 := lt_of_le_of_lt m.unpair_right_le hm
  -- simp [G₁, m, hm, m1, m2]
  -- rw [show ofNat Code (n + 4) = ofNatOCode (n + 4) from rfl]
  -- simp [ofNatOCode]
  -- cases n.bodd <;> cases n.div2.bodd <;> rfl

end

/-- The interpretation of a `Nat.Partrec.OCode` as a partial function.
* `Nat.Partrec.OCode.zero`: The constant zero function.
* `Nat.Partrec.OCode.succ`: The successor function.
* `Nat.Partrec.OCode.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.OCode.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `Nat.Partrec.OCode.oracle`: The oracle function.
* `Nat.Partrec.OCode.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `Nat.Partrec.OCode.comp`: Composition of two argument codes.
* `Nat.Partrec.OCode.prec`: Primitive recursion. Given an argument of the form `Nat.pair a n`:
  * If `n = 0`, returns `eval cf a`.
  * If `n = succ k`, returns `eval cg (pair a (pair k (eval (prec cf cg) (pair a k))))`
* `Nat.Partrec.OCode.rfind'`: Minimization. For `f` an argument of the form `Nat.pair a m`,
  `rfind' f m` returns the least `a` such that `f a m = 0`, if one exists and `f b m` terminates
  for `b < a`
-/
def eval (c : OCode) (o : ℕ →. ℕ) : ℕ →. ℕ := match c with
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | oracle => o
  | pair cf cg => fun n => Nat.pair <$> eval cf o n <*> eval cg o n
  | comp cf cg => fun n => eval cg o n >>= eval cf o
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval cf o a) fun y IH => do
        let i ← IH
        eval cg o (Nat.pair a (Nat.pair y i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf o (Nat.pair a (n + m))).map (· + m)

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero (cf cg : OCode) (o : ℕ →. ℕ) (a : ℕ) : eval (prec cf cg) o (Nat.pair a 0) = eval cf o a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  simp (config := { Lean.Meta.Simp.neutralConfig with proj := true }) only []
  rw [Nat.rec_zero]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem eval_prec_succ (cf cg : OCode) (o : ℕ →. ℕ) (a k : ℕ) :
    eval (prec cf cg) o (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval (prec cf cg) o (Nat.pair a k); eval cg o (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp

/--
Evaluation of `ofCode` does not depend on the oracle.
-/
@[simp]
theorem eval_ofCode (c : Code) (o : ℕ →. ℕ) (n : ℕ) : (OCode.ofCode c).eval o n = c.eval n := by
  sorry

@[simp]
theorem eval_const : ∀ n m o, eval (OCode.const n) o m = Part.some n := by
  simp [OCode.const]

@[simp]
theorem eval_id (n) : ∀ o, eval OCode.id o n = Part.some n := by
  simp [OCode.id]

@[simp]
theorem eval_curry (c o n x) : eval (curry c n) o x = eval c o (Nat.pair n x) := by simp! [Seq.seq, curry]

theorem primrec_const : Primrec OCode.const :=
  (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Code.const, OCode.const, OCode.ofCode, Function.iterate_succ', -Function.iterate_succ]

theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const OCode.id)

theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

/--
The $S_n^m$ theorem: There is a computable function, namely `Nat.Partrec.OCode.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn :
    ∃ f : OCode → ℕ → OCode, Computable₂ f ∧ ∀ c o n x, eval (f c n) o x = eval c o (Nat.pair n x) :=
  ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

/-- A function `f` is Turing reducible to `g` if and only if there is an `OCode` which evaluates to `f`, given oracle `g`. -/
theorem exists_code {f g : ℕ →. ℕ} : TuringReducible f g ↔ ∃ c : OCode, eval c g = f := by
  refine ⟨fun h => ?_, ?_⟩
  · induction h with
    | zero => exact ⟨zero, rfl⟩
    | succ => exact ⟨succ, rfl⟩
    | left => exact ⟨left, rfl⟩
    | right => exact ⟨right, rfl⟩
    | oracle g h => subst h; exact ⟨oracle, rfl⟩
    | pair pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨pair cf cg, rfl⟩
    | comp pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨comp cf cg, rfl⟩
    | prec pf pg hf hg =>
      rcases hf with ⟨cf, rfl⟩; rcases hg with ⟨cg, rfl⟩
      exact ⟨prec cf cg, rfl⟩
    | rfind pf hf =>
      rcases hf with ⟨cf, rfl⟩
      refine ⟨comp (rfind' cf) (pair OCode.id zero), ?_⟩
      simp [eval, Seq.seq, pure, PFun.pure, Part.map_id']
  · rintro ⟨c, rfl⟩
    induction c with
    | zero => exact RecursiveIn.zero
    | succ => exact RecursiveIn.succ
    | left => exact RecursiveIn.left
    | right => exact RecursiveIn.right
    | oracle => exact TuringReducible.refl g
    | pair cf cg pf pg => exact pf.pair pg
    | comp cf cg pf pg => exact pf.comp pg
    | prec cf cg pf pg => exact pf.prec pg
    | rfind' cf pf => sorry -- exact pf.rfind' -- TODO: Fix this.

/-- A modified evaluation for an `OCode` which returns an `Option ℕ` instead of a `Part ℕ`. To avoid undecidability, `evaln` takes a parameter `k` and fails if it encounters a number ≥ k in the course of its execution. Moreover, the provided oracle must be a function `ℕ → Option ℕ` rather than a function `ℕ →. ℕ`. Other than this, the semantics are the same as in `Nat.Partrec.OCode.eval`.

TODO: Is using `ℕ → Option ℕ` as the oracle what we want here? Maybe we want to use `List ℕ` and `.get` instead. Then "`evaln k` is primitive recursive" makes sense.
-/
def evaln : ℕ → OCode → (ℕ → Option ℕ) → ℕ → Option ℕ
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
    o n
  | k + 1, pair cf cg => fun o n => do
    guard (n ≤ k)
    Nat.pair <$> evaln (k + 1) cf o n <*> evaln (k + 1) cg o n
  | k + 1, comp cf cg => fun o n => do
    guard (n ≤ k)
    let x ← evaln (k + 1) cg o n
    evaln (k + 1) cf o x
  | k + 1, prec cf cg => fun o n => do
    guard (n ≤ k)
    n.unpaired fun a n =>
      n.casesOn (evaln (k + 1) cf o a) fun y => do
        let i ← evaln k (prec cf cg) o (Nat.pair a y)
        evaln (k + 1) cg o (Nat.pair a (Nat.pair y i))
  | k + 1, rfind' cf => fun o n => do
    guard (n ≤ k)
    n.unpaired fun a m => do
      let x ← evaln (k + 1) cf o (Nat.pair a m)
      if x = 0 then
        pure m
      else
        evaln k (rfind' cf) o (Nat.pair a (m + 1))

theorem evaln_bound : ∀ {k c g n x}, x ∈ evaln k c g n → n < k
  | 0, c, g, n, x, h => by simp [evaln] at h
  | k + 1, c, g, n, x, h => by
    suffices ∀ {o : Option ℕ}, x ∈ do { guard (n ≤ k); o } → n < k + 1 by
      cases c <;> rw [evaln] at h <;> exact this h
    simpa [Option.bind_eq_some_iff] using Nat.lt_succ_of_le

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
theorem evaln_mono : ∀ {k₁ k₂ c g n x}, k₁ ≤ k₂ → x ∈ evaln k₁ c g n → x ∈ evaln k₂ c g n
  | 0, k₂, c, g, n, x, _, h => by simp [evaln] at h
  | k + 1, k₂ + 1, c, g, n, x, hl, h => by
    sorry
    -- TODO: update this proof for OCode.
    -- have hl' := Nat.le_of_succ_le_succ hl
    -- have :
    --   ∀ {k k₂ n x : ℕ} {o₁ o₂ : Option ℕ},
    --     k ≤ k₂ → (x ∈ o₁ → x ∈ o₂) →
    --       x ∈ do { guard (n ≤ k); o₁ } → x ∈ do { guard (n ≤ k₂); o₂ } := by
    --   simp only [Option.mem_def, bind, Option.bind_eq_some_iff, Option.guard_eq_some',
    --     exists_and_left, exists_const, and_imp]
    --   introv h h₁ h₂ h₃
    --   exact ⟨le_trans h₂ h, h₁ h₃⟩
    -- simp? at h ⊢ says simp only [Option.mem_def] at h ⊢
    -- induction c generalizing x n <;> rw [evaln] at h ⊢ <;> refine this hl' (fun h => ?_) h
    -- iterate 4 exact h
    -- case pair cf cg hf hg _ =>
    --   simp? [Seq.seq, Option.bind_eq_some_iff] at h ⊢ says
    --     simp only [Seq.seq, Option.map_eq_map, Option.mem_def, Option.bind_eq_some_iff,
    --       Option.map_eq_some_iff, exists_exists_and_eq_and] at h ⊢
    --   exact h.imp fun a => And.imp (hf _ _) <| Exists.imp fun b => And.imp_left (hg _ _)
    -- case comp cf cg hf hg _ =>
    --   simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
    --     simp only [bind, Option.mem_def, Option.bind_eq_some_iff] at h ⊢
    --   exact h.imp fun a => And.imp (hg _ _) (hf _ _)
    -- case prec cf cg hf hg _ =>
    --   revert h
    --   simp only [unpaired, bind, Option.mem_def]
    --   induction n.unpair.2 <;> simp [Option.bind_eq_some_iff]
    --   · apply hf
    --   · exact fun y h₁ h₂ => ⟨y, evaln_mono hl' h₁, hg _ _ h₂⟩
    -- case rfind' cf hf _ =>
    --   simp? [Bind.bind, Option.bind_eq_some_iff] at h ⊢ says
    --     simp only [unpaired, bind, pair_unpair, Option.pure_def, Option.mem_def,
    --       Option.bind_eq_some_iff] at h ⊢
    --   refine h.imp fun x => And.imp (hf _ _) ?_
    --   by_cases x0 : x = 0 <;> simp [x0]
    --   exact evaln_mono hl'

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
-- TODO: Figure out the correct statement of this theorem.
-- theorem evaln_sound : ∀ {k c g n x}, x ∈ evaln k c g n → x ∈ eval c g n
--   | 0, _, g, n, x, h => by simp [evaln] at h
--   | k + 1, c, g, n, x, h => by
--     induction c generalizing x n <;> simp [eval, evaln, Option.bind_eq_some_iff, Seq.seq] at h ⊢ <;>
--       obtain ⟨_, h⟩ := h
--     iterate 4 simpa [pure, PFun.pure, eq_comm] using h
--     case pair cf cg hf hg _ =>
--       rcases h with ⟨y, ef, z, eg, rfl⟩
--       exact ⟨_, hf _ _ ef, _, hg _ _ eg, rfl⟩
--     case comp cf cg hf hg _ =>
--       rcases h with ⟨y, eg, ef⟩
--       exact ⟨_, hg _ _ eg, hf _ _ ef⟩
--     case prec cf cg hf hg _ =>
--       revert h
--       induction n.unpair.2 generalizing x with simp [Option.bind_eq_some_iff]
--       | zero => apply hf
--       | succ m IH =>
--         refine fun y h₁ h₂ => ⟨y, IH _ ?_, ?_⟩
--         · have := evaln_mono k.le_succ h₁
--           simp [evaln, Option.bind_eq_some_iff] at this
--           exact this.2
--         · exact hg _ _ h₂
--     case rfind' cf hf _ =>
--       rcases h with ⟨m, h₁, h₂⟩
--       by_cases m0 : m = 0 <;> simp [m0] at h₂
--       · exact
--           ⟨0, ⟨by simpa [m0] using hf _ _ h₁, fun {m} => (Nat.not_lt_zero _).elim⟩, by simp [h₂]⟩
--       · have := evaln_sound h₂
--         simp [eval] at this
--         rcases this with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
--         refine
--           ⟨y + 1, ⟨by simpa [add_comm, add_left_comm] using hy₁, fun {i} im => ?_⟩, by
--             simp [add_comm, add_left_comm]⟩
--         rcases i with - | i
--         · exact ⟨m, by simpa using hf _ _ h₁, m0⟩
--         · rcases hy₂ (Nat.lt_of_succ_lt_succ im) with ⟨z, hz, z0⟩
--           exact ⟨z, by simpa [add_comm, add_left_comm] using hz, z0⟩

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
-- TODO: Figure out the correct statement of this theorem.
-- theorem evaln_complete {c g n x} : x ∈ eval c g n ↔ ∃ k, x ∈ evaln k c g n := by
--   refine ⟨fun h => ?_, fun ⟨k, h⟩ => evaln_sound h⟩
--   rsuffices ⟨k, h⟩ : ∃ k, x ∈ evaln (k + 1) c n
--   · exact ⟨k + 1, h⟩
--   induction c generalizing n x with
--       simp [eval, evaln, pure, PFun.pure, Seq.seq, Option.bind_eq_some_iff] at h ⊢
--   | pair cf cg hf hg =>
--     rcases h with ⟨x, hx, y, hy, rfl⟩
--     rcases hf hx with ⟨k₁, hk₁⟩; rcases hg hy with ⟨k₂, hk₂⟩
--     refine ⟨max k₁ k₂, ?_⟩
--     refine
--       ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
--         evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁, _,
--         evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂, rfl⟩
--   | comp cf cg hf hg =>
--     rcases h with ⟨y, hy, hx⟩
--     rcases hg hy with ⟨k₁, hk₁⟩; rcases hf hx with ⟨k₂, hk₂⟩
--     refine ⟨max k₁ k₂, ?_⟩
--     exact
--       ⟨le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁, _,
--         evaln_mono (Nat.succ_le_succ <| le_max_left _ _) hk₁,
--         evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂⟩
--   | prec cf cg hf hg =>
--     revert h
--     generalize n.unpair.1 = n₁; generalize n.unpair.2 = n₂
--     induction n₂ generalizing x n with simp [Option.bind_eq_some_iff]
--     | zero =>
--       intro h
--       rcases hf h with ⟨k, hk⟩
--       exact ⟨_, le_max_left _ _, evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk⟩
--     | succ m IH =>
--       intro y hy hx
--       rcases IH hy with ⟨k₁, nk₁, hk₁⟩
--       rcases hg hx with ⟨k₂, hk₂⟩
--       refine
--         ⟨(max k₁ k₂).succ,
--           Nat.le_succ_of_le <| le_max_of_le_left <|
--             le_trans (le_max_left _ (Nat.pair n₁ m)) nk₁, y,
--           evaln_mono (Nat.succ_le_succ <| le_max_left _ _) ?_,
--           evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_right _ _) hk₂⟩
--       simp only [evaln.eq_8, bind, unpaired, unpair_pair, Option.mem_def, Option.bind_eq_some_iff,
--         Option.guard_eq_some', exists_and_left, exists_const]
--       exact ⟨le_trans (le_max_right _ _) nk₁, hk₁⟩
--   | rfind' cf hf =>
--     rcases h with ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
--     suffices ∃ k, y + n.unpair.2 ∈ evaln (k + 1) (rfind' cf) (Nat.pair n.unpair.1 n.unpair.2) by
--       simpa [evaln, Option.bind_eq_some_iff]
--     revert hy₁ hy₂
--     generalize n.unpair.2 = m
--     intro hy₁ hy₂
--     induction y generalizing m with simp [evaln, Option.bind_eq_some_iff]
--     | zero =>
--       simp at hy₁
--       rcases hf hy₁ with ⟨k, hk⟩
--       exact ⟨_, Nat.le_of_lt_succ <| evaln_bound hk, _, hk, by simp⟩
--     | succ y IH =>
--       rcases hy₂ (Nat.succ_pos _) with ⟨a, ha, a0⟩
--       rcases hf ha with ⟨k₁, hk₁⟩
--       rcases IH m.succ (by simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using hy₁)
--           fun {i} hi => by
--           simpa [Nat.succ_eq_add_one, add_comm, add_left_comm] using
--             hy₂ (Nat.succ_lt_succ hi) with
--         ⟨k₂, hk₂⟩
--       use (max k₁ k₂).succ
--       rw [zero_add] at hk₁
--       use Nat.le_succ_of_le <| le_max_of_le_left <| Nat.le_of_lt_succ <| evaln_bound hk₁
--       use a
--       use evaln_mono (Nat.succ_le_succ <| Nat.le_succ_of_le <| le_max_left _ _) hk₁
--       simpa [a0, add_comm, add_left_comm] using
--         evaln_mono (Nat.succ_le_succ <| le_max_right _ _) hk₂
--   | _ => exact ⟨⟨_, le_rfl⟩, h.symm⟩

section

open Primrec

/-
TODO: Figure out what is going on in this section. What is `G` supposed to be? What are `lup` and `hlup` doing?
-/

private def lup (L : List (List (Option ℕ))) (p : ℕ × OCode) (n : ℕ) := do
  let l ← L[encode p]?
  let o ← l[n]?
  o

private theorem hlup : Primrec fun p : _ × (_ × _) × _ => lup p.1 p.2.1 p.2.2 :=
  Primrec.option_bind
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.encode.comp <| Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind (Primrec.list_getElem?.comp Primrec.snd <| Primrec.snd.comp <|
      Primrec.snd.comp Primrec.fst) Primrec.snd)

private def G (L : List (List (Option ℕ))) : Option (List (Option ℕ)) :=
  Option.some <|
    let a := ofNat (ℕ × OCode) L.length
    let k := a.1
    let c := a.2
    (List.range k).map fun n =>
      k.casesOn Option.none fun k' =>
        Nat.Partrec.OCode.recOn c
          (some 0) -- zero
          (some (Nat.succ n))
          (some n.unpair.1)
          (some n.unpair.2)
          (sorry) -- TODO: What should this be?
          (fun cf cg _ _ => do
            let x ← lup L (k, cf) n
            let y ← lup L (k, cg) n
            some (Nat.pair x y))
          (fun cf cg _ _ => do
            let x ← lup L (k, cg) n
            lup L (k, cf) x)
          (fun cf cg _ _ =>
            let z := n.unpair.1
            n.unpair.2.casesOn (lup L (k, cf) z) fun y => do
              let i ← lup L (k', c) (Nat.pair z y)
              lup L (k, cg) (Nat.pair z (Nat.pair y i)))
          (fun cf _ =>
            let z := n.unpair.1
            let m := n.unpair.2
            do
              let x ← lup L (k, cf) (Nat.pair z m)
              x.casesOn (some m) fun _ => lup L (k', c) (Nat.pair z (m + 1)))

private theorem hG : Primrec G := by
  sorry
  -- TODO: Update this proof? What is it doing?
  -- have a := (Primrec.ofNat (ℕ × Code)).comp (Primrec.list_length (α := List (Option ℕ)))
  -- have k := Primrec.fst.comp a
  -- refine Primrec.option_some.comp (Primrec.list_map (Primrec.list_range.comp k) (?_ : Primrec _))
  -- replace k := k.comp (Primrec.fst (β := ℕ))
  -- have n := Primrec.snd (α := List (List (Option ℕ))) (β := ℕ)
  -- refine Primrec.nat_casesOn k (_root_.Primrec.const Option.none) (?_ : Primrec _)
  -- have k := k.comp (Primrec.fst (β := ℕ))
  -- have n := n.comp (Primrec.fst (β := ℕ))
  -- have k' := Primrec.snd (α := List (List (Option ℕ)) × ℕ) (β := ℕ)
  -- have c := Primrec.snd.comp (a.comp <| (Primrec.fst (β := ℕ)).comp (Primrec.fst (β := ℕ)))
  -- apply
  --   Nat.Partrec.Code.primrec_recOn c
  --     (_root_.Primrec.const (some 0))
  --     (Primrec.option_some.comp (_root_.Primrec.succ.comp n))
  --     (Primrec.option_some.comp (Primrec.fst.comp <| Primrec.unpair.comp n))
  --     (Primrec.option_some.comp (Primrec.snd.comp <| Primrec.unpair.comp n))
  -- · have L := (Primrec.fst.comp Primrec.fst).comp
  --     (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have cg := (Primrec.fst.comp Primrec.snd).comp
  --     (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cf).pair n) ?_
  --   unfold Primrec₂
  --   conv =>
  --     congr
  --     · ext p
  --       dsimp only []
  --       erw [Option.bind_eq_bind, ← Option.map_eq_bind]
  --   refine Primrec.option_map ((hlup.comp <| L.pair <| (k.pair cg).pair n).comp Primrec.fst) ?_
  --   unfold Primrec₂
  --   exact Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  -- · have L := (Primrec.fst.comp Primrec.fst).comp
  --     (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have cg := (Primrec.fst.comp Primrec.snd).comp
  --     (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   refine Primrec.option_bind (hlup.comp <| L.pair <| (k.pair cg).pair n) ?_
  --   unfold Primrec₂
  --   have h :=
  --     hlup.comp ((L.comp Primrec.fst).pair <| ((k.pair cf).comp Primrec.fst).pair Primrec.snd)
  --   exact h
  -- · have L := (Primrec.fst.comp Primrec.fst).comp
  --     (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have k := k.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have n := n.comp (Primrec.fst (β := Code × Code × Option ℕ × Option ℕ))
  --   have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have cg := (Primrec.fst.comp Primrec.snd).comp
  --     (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Code × Option ℕ × Option ℕ))
  --   have z := Primrec.fst.comp (Primrec.unpair.comp n)
  --   refine
  --     Primrec.nat_casesOn (Primrec.snd.comp (Primrec.unpair.comp n))
  --       (hlup.comp <| L.pair <| (k.pair cf).pair z)
  --       (?_ : Primrec _)
  --   have L := L.comp (Primrec.fst (β := ℕ))
  --   have z := z.comp (Primrec.fst (β := ℕ))
  --   have y := Primrec.snd
  --     (α := ((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) (β := ℕ)
  --   have h₁ := hlup.comp <| L.pair <| (((k'.pair c).comp Primrec.fst).comp Primrec.fst).pair
  --     (Primrec₂.natPair.comp z y)
  --   refine Primrec.option_bind h₁ (?_ : Primrec _)
  --   have z := z.comp (Primrec.fst (β := ℕ))
  --   have y := y.comp (Primrec.fst (β := ℕ))
  --   have i := Primrec.snd
  --     (α := (((List (List (Option ℕ)) × ℕ) × ℕ) × Code × Code × Option ℕ × Option ℕ) × ℕ)
  --     (β := ℕ)
  --   have h₂ := hlup.comp ((L.comp Primrec.fst).pair <|
  --     ((k.pair cg).comp <| Primrec.fst.comp Primrec.fst).pair <|
  --       Primrec₂.natPair.comp z <| Primrec₂.natPair.comp y i)
  --   exact h₂
  -- · have L := (Primrec.fst.comp Primrec.fst).comp
  --     (Primrec.fst (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Option ℕ))
  --   have k := k.comp (Primrec.fst (β := Code × Option ℕ))
  --   have n := n.comp (Primrec.fst (β := Code × Option ℕ))
  --   have cf := Primrec.fst.comp (Primrec.snd (α := (List (List (Option ℕ)) × ℕ) × ℕ)
  --       (β := Code × Option ℕ))
  --   have z := Primrec.fst.comp (Primrec.unpair.comp n)
  --   have m := Primrec.snd.comp (Primrec.unpair.comp n)
  --   have h₁ := hlup.comp <| L.pair <| (k.pair cf).pair (Primrec₂.natPair.comp z m)
  --   refine Primrec.option_bind h₁ (?_ : Primrec _)
  --   have m := m.comp (Primrec.fst (β := ℕ))
  --   refine Primrec.nat_casesOn Primrec.snd (Primrec.option_some.comp m) ?_
  --   unfold Primrec₂
  --   exact (hlup.comp ((L.comp Primrec.fst).pair <|
  --     ((k'.pair c).comp <| Primrec.fst.comp Primrec.fst).pair
  --       (Primrec₂.natPair.comp (z.comp Primrec.fst) (_root_.Primrec.succ.comp m)))).comp
  --     Primrec.fst

-- TODO: What is the right statement of this theorem?
-- private theorem evaln_map (k c n) :
--     ((List.range k)[n]?.bind fun a ↦ evaln k c a) = evaln k c n := by
--   by_cases kn : n < k
--   · simp [List.getElem?_range kn]
--   · rw [List.getElem?_eq_none]
--     · cases e : evaln k c n
--       · rfl
--       exact kn.elim (evaln_bound e)
--     simpa using kn

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
-- /-- The `Nat.Partrec.Code.evaln` function is primitive recursive. -/
-- TODO: What is the correct way to state this theorem?
-- theorem primrec_evaln : Primrec fun a : (ℕ × Code) × ℕ => evaln a.1.1 a.1.2 a.2 :=
--   have :
--     Primrec₂ fun (_ : Unit) (n : ℕ) =>
--       let a := ofNat (ℕ × Code) n
--       (List.range a.1).map (evaln a.1 a.2) :=
--     Primrec.nat_strong_rec _ (hG.comp Primrec.snd).to₂ fun _ p => by
--       simp only [G, prod_ofNat_val, ofNat_nat, List.length_map, List.length_range,
--         Nat.pair_unpair, Option.some_inj]
--       refine List.map_congr_left fun n => ?_
--       have : List.range p = List.range (Nat.pair p.unpair.1 (encode (ofNat Code p.unpair.2))) := by
--         simp
--       rw [this]
--       generalize p.unpair.1 = k
--       generalize ofNat Code p.unpair.2 = c
--       intro nk
--       rcases k with - | k'
--       · simp [evaln]
--       let k := k' + 1
--       simp only
--       simp only [List.mem_range, Nat.lt_succ_iff] at nk
--       have hg :
--         ∀ {k' c' n},
--           Nat.pair k' (encode c') < Nat.pair k (encode c) →
--             lup ((List.range (Nat.pair k (encode c))).map fun n =>
--               (List.range n.unpair.1).map (evaln n.unpair.1 (ofNat Code n.unpair.2))) (k', c') n =
--             evaln k' c' n := by
--         intro k₁ c₁ n₁ hl
--         simp [lup, List.getElem?_range hl, evaln_map, Bind.bind, Option.bind_map]
--       obtain - | - | - | - | ⟨cf, cg⟩ | ⟨cf, cg⟩ | ⟨cf, cg⟩ | cf := c <;>
--         simp [evaln, nk, Bind.bind, Functor.map, Seq.seq, pure]
--       · obtain ⟨lf, lg⟩ := encode_lt_pair cf cg
--         rw [hg (Nat.pair_lt_pair_right _ lf), hg (Nat.pair_lt_pair_right _ lg)]
--         cases evaln k cf n
--         · rfl
--         cases evaln k cg n <;> rfl
--       · obtain ⟨lf, lg⟩ := encode_lt_comp cf cg
--         rw [hg (Nat.pair_lt_pair_right _ lg)]
--         cases evaln k cg n
--         · rfl
--         simp [k, hg (Nat.pair_lt_pair_right _ lf)]
--       · obtain ⟨lf, lg⟩ := encode_lt_prec cf cg
--         rw [hg (Nat.pair_lt_pair_right _ lf)]
--         cases n.unpair.2
--         · rfl
--         simp only
--         rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
--         cases evaln k' _ _
--         · rfl
--         simp [k, hg (Nat.pair_lt_pair_right _ lg)]
--       · have lf := encode_lt_rfind' cf
--         rw [hg (Nat.pair_lt_pair_right _ lf)]
--         rcases evaln k cf n with - | x
--         · rfl
--         simp only [Option.bind_some]
--         cases x <;> simp
--         rw [hg (Nat.pair_lt_pair_left _ k'.lt_succ_self)]
--   (Primrec.option_bind
--     (Primrec.list_getElem?.comp (this.comp (_root_.Primrec.const ())
--       (Primrec.encode_iff.2 Primrec.fst)) Primrec.snd) Primrec.snd.to₂).of_eq
--     fun ⟨⟨k, c⟩, n⟩ => by simp [evaln_map, Option.bind_map]

end

section

open Partrec Computable

-- TODO: do we need to update this?
-- theorem eval_eq_rfindOpt (c n) : eval c n = Nat.rfindOpt fun k => evaln k c n :=
--   Part.ext fun x => by
--     refine evaln_complete.trans (Nat.rfindOpt_mono ?_).symm
--     intro a m n hl; apply evaln_mono hl

-- TODO: do we need to update this?
-- theorem eval_part : Partrec₂ eval :=
--   (Partrec.rfindOpt
--     (primrec_evaln.to_comp.comp
--       ((Computable.snd.pair (fst.comp fst)).pair (snd.comp fst))).to₂).of_eq
--     fun a => by simp [eval_eq_rfindOpt]

-- /-- **Roger's fixed-point theorem**: any total, computable `f` has a fixed point.
-- That is, under the interpretation given by `Nat.Partrec.Code.eval`, there is a code `c`
-- such that `c` and `f c` have the same evaluation.
-- -/
-- TODO: What is the correct relativization of this theorem?
-- theorem fixed_point {f : OCode → OCode} (hf : Computable f) : ∃ c : OCode, eval (f c) = eval c :=
--   let g (x y : ℕ) : Part ℕ := eval (ofNat Code x) x >>= fun b => eval (ofNat Code b) y
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

-- /-- **Kleene's second recursion theorem** -/
-- TODO: What is the correct relativization of this theorem?
-- theorem fixed_point₂ {f : Code → ℕ →. ℕ} (hf : Partrec₂ f) : ∃ c : Code, eval c = f c :=
--   let ⟨cf, ef⟩ := exists_code.1 hf
--   (fixed_point (primrec₂_curry.comp (_root_.Primrec.const cf) Primrec.encode).to_comp).imp
--     fun c e => funext fun n => by simp [e.symm, ef, Part.map_id']

end

end Nat.Partrec.OCode
