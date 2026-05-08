/-
Copyright (c) 2026 Jacob Parish and Yvette Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Parish, Yvette Ren.
-/

module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.TuringDegree

/-!
# Gödel Numbering for Partial Recursive Functions with an Oracle.

This file is a "relativized" version of `Mathlib/Computability/PartrecCode.lean`.

It defines `RecursiveIn.Code`, an inductive datatype describing codes for partial recursive functions on ℕ with an oracle. It defines an encoding for these codes, and proves that the constructors are primitive recursive with respect to the encoding.

Note that although `RecursiveIn` takes a set of oracles, `RecursiveIn.Code` allows just a single oracle. Another option would have been to allow a family of oracles indexed by a `Primcodable` type (i.e., we would define a structure `RecursiveIn.Code (α : Type*) [Primcodable α]`). But (1) such a family can be computably encoded as a single oracle anyway, and (2) the need to consider indexed families of oracles seems rare enough that it was not worth the extra complication.

It also defines the evaluation of a `RecursiveIn.Code` as a partial function, and proves that a function `f` is Turing reducible to `g` if and only if it is the evaluation of some `RecursiveIn.Code` using `g` as an oracle.

## Main Definitions

* `RecursiveIn.Code`: Inductive datatype for partial recursive functions with an oracle.
* `RecursiveIn.Code.encodeCode`: A (computable) encoding of a `RecursiveIn.Code` as a natural number.
* `RecursiveIn.Code.ofNatCode`: The inverse of this encoding.
* `RecursiveIn.Code.eval`: The interpretation of a `RecursiveIn.Code` as a partial function.

## Main Results

* `RecursiveIn.Code.primrec_recOn`: Recursion on `RecursiveIn.Code` is primitive recursive.
* `RecursiveIn.Code.computable_recOn`: Recursion on `RecursiveIn.Code` is computable.
* `RecursiveIn.Code.smn`: The relative $S_n^m$ theorem.
* `RecursiveIn.Code.exists_code`: Being Turing reducible to `g` is equivalent to being the eval of a `RecursiveIn.Code` with oracle `g`.
-/

@[expose] public section

open Encodable Denumerable


namespace RecursiveIn

theorem rfind' {O f} (hf : RecursiveIn O f) :
    RecursiveIn O
      (Nat.unpaired fun a m =>
        (Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a (n + m))).map (· + m)) :=
  by
    have recIn_of_partrec : ∀ {g : ℕ →. ℕ}, Nat.Partrec g → RecursiveIn O g := by
      intro g hg
      induction hg with
      | zero => exact .zero
      | succ => exact .succ
      | left => exact .left
      | right => exact .right
      | pair hf hh ihf ihh => exact .pair ihf ihh
      | comp hf hh ihf ihh => exact .comp ihf ihh
      | prec hf hh ihf ihh => exact .prec ihf ihh
      | rfind hf ihf => exact .rfind ihf
    let shift : ℕ → ℕ := fun x =>
      Nat.pair (Nat.unpair (Nat.unpair x).1).1 ((Nat.unpair x).2 + (Nat.unpair (Nat.unpair x).1).2)
    have hshift_primrec : Primrec shift :=
      Primrec₂.natPair.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
          (Primrec.nat_add.comp
            (Primrec.snd.comp Primrec.unpair)
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
    have hshift : RecursiveIn O (fun x => shift x) :=
      recIn_of_partrec (Partrec.nat_iff.mp hshift_primrec.to_comp.partrec)
    have hcore : RecursiveIn O (fun x => f (shift x)) := by
      simpa [Part.bind_eq_bind, shift] using (RecursiveIn.comp hf hshift)
    have hrfind : RecursiveIn O (fun p =>
      Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair (Nat.unpair p).1 (n + (Nat.unpair p).2)))) := by
      simpa [shift, Nat.unpair_pair] using (RecursiveIn.rfind hcore)
    let addPair : ℕ → ℕ := fun z => (Nat.unpair z).1 + (Nat.unpair z).2
    have haddPair_primrec : Primrec addPair := by
      dsimp [addPair]
      exact Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)
    have haddPair : RecursiveIn O (fun z => addPair z) :=
      recIn_of_partrec (Partrec.nat_iff.mp haddPair_primrec.to_comp.partrec)
    have hpair :
        RecursiveIn O (fun p =>
          Nat.pair <$> (Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair (Nat.unpair p).1 (n + (Nat.unpair p).2))))
            <*> Part.some (Nat.unpair p).2) := by
      exact RecursiveIn.pair hrfind RecursiveIn.right
    have hfinal : RecursiveIn O (fun p =>
      (Nat.rfind (fun n => (fun m => m = 0) <$> f (Nat.pair (Nat.unpair p).1 (n + (Nat.unpair p).2)))).map
        (fun n => n + (Nat.unpair p).2)) := by
      convert (RecursiveIn.comp haddPair hpair) using 1
      funext n
      have hfg :
          (fun n_1 => n_1 + (Nat.unpair n).2) =
            ((fun y => (Nat.unpair y).1 + (Nat.unpair y).2) ∘ (fun y => y (Nat.unpair n).2) ∘ Nat.pair) := by
        funext x
        simp [Function.comp, Nat.unpair_pair]
      simp [addPair, Seq.seq, Part.bind_some_eq_map, Part.map_map, Part.map_eq_map, hfg]
    simpa [Nat.unpaired, Nat.unpair_pair, Nat.pair_unpair] using hfinal

/-- Code for partial recursive functions from ℕ to ℕ with an oracle.
See `RecursiveIn.Code.eval` for the interpretation of these constructors.
-/
inductive Code : Type
  | zero : Code
  | succ : Code
  | left : Code
  | right : Code
  | oracle : Code
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind' : Code → Code

compile_inductive% Code

end RecursiveIn

namespace RecursiveIn.Code

open Nat Nat.Partrec

/-- A `Nat.Partrec.Code` can be converted to a `RecursiveIn.Code`. -/
def ofPartrecCode : Nat.Partrec.Code → Code
  | .zero => zero
  | .succ => succ
  | .left => left
  | .right => right
  | .pair cf cg => pair (ofPartrecCode cf) (ofPartrecCode cg)
  | .comp cf cg => comp (ofPartrecCode cf) (ofPartrecCode cg)
  | .prec cf cg => prec (ofPartrecCode cf) (ofPartrecCode cg)
  | .rfind' cf => rfind' (ofPartrecCode cf)

/-- The conversion from `Nat.Partrec.Code` to `RecursiveIn.Code` is injective. -/
theorem ofPartrecCode_inj : Function.Injective ofPartrecCode := by
  intro a b
  induction a generalizing b with cases b <;> grind [ofPartrecCode]

instance instInhabited : Inhabited Code :=
  ⟨zero⟩

/-- a `Code` for the constant function outputting `n`. -/
protected def const (n : ℕ) : Code := ofPartrecCode (Nat.Partrec.Code.const n)

/-- `Code.const` is injective. -/
theorem const_inj : Function.Injective Code.const :=
  ofPartrecCode_inj.comp @Nat.Partrec.Code.const_inj

/-- a `Code` for the identity function. -/
protected def id : Code := ofPartrecCode Nat.Partrec.Code.id

/-- Given a code `c` taking a pair as input, returns a code using `n` as the first argument to `c`.
-/
def curry (c : Code) (n : ℕ) : Code :=
  comp c (pair (Code.const n) Code.id)

/-- An encoding of a `RecursiveIn.Code` as a ℕ. -/
def encodeCode : Code → ℕ
  | zero => 0
  | succ => 1
  | left => 2
  | right => 3
  | oracle => 4
  | pair cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 5
  | comp cf cg => 2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg) + 1) + 5
  | prec cf cg => (2 * (2 * Nat.pair (encodeCode cf) (encodeCode cg)) + 1) + 5
  | rfind' cf => (2 * (2 * encodeCode cf + 1) + 1) + 5

/--
A decoder for `RecursiveIn.Code.encodeCode`, taking any ℕ to the `RecursiveIn.Code` it represents.
-/
def ofNatCode : ℕ → Code
  | 0 => zero
  | 1 => succ
  | 2 => left
  | 3 => right
  | 4 => oracle
  | n + 5 =>
    let m := n.div2.div2
    have hm : m < n + 5 := by grind
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    match n.bodd, n.div2.bodd with
    | false, false => pair (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | false, true => comp (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, false => prec (ofNatCode m.unpair.1) (ofNatCode m.unpair.2)
    | true, true => rfind' (ofNatCode m)

set_option backward.privateInPublic true in
/-- Proof that `RecursiveIn.Code.ofNatCode` is the inverse of `RecursiveIn.Code.encodeCode` -/
private theorem encode_ofNatCode : ∀ n, encodeCode (ofNatCode n) = n
  | 0 => by simp [ofNatCode, encodeCode]
  | 1 => by simp [ofNatCode, encodeCode]
  | 2 => by simp [ofNatCode, encodeCode]
  | 3 => by simp [ofNatCode, encodeCode]
  | 4 => by simp [ofNatCode, encodeCode]
  | n + 5 => by
    let m := n.div2.div2
    have hm : m < n + 5 := by grind
    have _m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
    have _m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
    have IH := encode_ofNatCode m
    have IH1 := encode_ofNatCode m.unpair.1
    have IH2 := encode_ofNatCode m.unpair.2
    conv_rhs => rw [← Nat.bit_bodd_div2 n, ← Nat.bit_bodd_div2 n.div2]
    simp only [ofNatCode]
    cases n.bodd <;> cases n.div2.bodd <;>
      simp [m, encodeCode, IH, IH1, IH2, Nat.bit_val]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
instance instDenumerable : Denumerable Code :=
  mk'
    ⟨encodeCode, ofNatCode, fun c => by
        induction c <;> simp [encodeCode, ofNatCode, Nat.div2_val, *],
      encode_ofNatCode⟩

theorem encodeCode_eq : encode = encodeCode :=
  rfl

theorem ofNatCode_eq : ofNat Code = ofNatCode :=
  rfl

theorem encode_lt_pair (cf cg) :
    encode cf < encode (pair cf cg) ∧ encode cg < encode (pair cf cg) := by
  simp only [encodeCode_eq, encodeCode]
  have := Nat.mul_le_mul_right (Nat.pair cf.encodeCode cg.encodeCode) (by decide : 1 ≤ 2 * 2)
  rw [one_mul, mul_assoc] at this
  have := lt_of_le_of_lt this (lt_add_of_pos_right _ (by decide : 0 < 5))
  exact ⟨lt_of_le_of_lt (Nat.left_le_pair _ _) this, lt_of_le_of_lt (Nat.right_le_pair _ _) this⟩

theorem encode_lt_comp (cf cg) :
    encode cf < encode (comp cf cg) ∧ encode cg < encode (comp cf cg) := by
  have : encode (pair cf cg) < encode (comp cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_prec (cf cg) :
    encode cf < encode (prec cf cg) ∧ encode cg < encode (prec cf cg) := by
  have : encode (pair cf cg) < encode (prec cf cg) := by simp [encodeCode_eq, encodeCode]
  exact (encode_lt_pair cf cg).imp (fun h => lt_trans h this) fun h => lt_trans h this

theorem encode_lt_rfind' (cf) : encode cf < encode (rfind' cf) := by
  simp only [encodeCode_eq, encodeCode]
  lia

end RecursiveIn.Code

section
open Nat Primrec
namespace RecursiveIn.Code

theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double.comp <|
          nat_double_succ.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.ofNat_iff.2 <|
    Primrec₂.encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <|
          nat_double.comp <|
            Primrec₂.natPair.comp (encode_iff.2 <| (Primrec.ofNat Code).comp fst)
              (encode_iff.2 <| (Primrec.ofNat Code).comp snd))
        (Primrec₂.const 5)

theorem primrec_rfind' : Primrec rfind' :=
  ofNat_iff.2 <|
    encode_iff.1 <|
      nat_add.comp
        (nat_double_succ.comp <| nat_double_succ.comp <|
          encode_iff.2 <| Primrec.ofNat Code)
        (const 5)

theorem primrec_recOn' {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o) {pr : α → Code × Code × σ × σ → σ} (hpr : Primrec₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Primrec₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Primrec₂ pc) {rf : α → Code × σ → σ} (hrf : Primrec₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      RecursiveIn.Code.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Primrec (fun a => F a (c a) : α → σ) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Primrec G₁ :=
    option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk <|
    option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Primrec.unpair.comp (snd.comp snd))).comp fst) <| .mk <|
    option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Primrec.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk <|
    have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
    have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
    have m₁ := fst.comp (Primrec.unpair.comp m)
    have m₂ := snd.comp (Primrec.unpair.comp m)
    have s := snd.comp (fst.comp fst)
    have s₁ := snd.comp fst
    have s₂ := snd
    (nat_bodd.comp n).cond
      ((nat_bodd.comp <| nat_div2.comp n).cond
        (hrf.comp a (((Primrec.ofNat Code).comp m).pair s))
        (hpc.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
      (Primrec.cond (nat_bodd.comp <| nat_div2.comp n)
        (hco.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂))
        (hpr.comp a (((Primrec.ofNat Code).comp m₁).pair <|
          ((Primrec.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    n.casesOn (some (o a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Primrec₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (ho.comp (fst.comp <| fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 5 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 5)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 5)))
  have hm : m < n + 5 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 5) = ofNatCode (n + 5) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

/-- Recursion on `RecursiveIn.Code` is primitive recursive. -/
theorem primrec_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Primrec c) {z : α → σ}
    (hz : Primrec z) {s : α → σ} (hs : Primrec s) {l : α → σ} (hl : Primrec l) {r : α → σ}
    (hr : Primrec r) {o : α → σ} (ho : Primrec o) {pr : α → Code → Code → σ → σ → σ}
    (hpr : Primrec fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Primrec fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Primrec fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ} (hrf : Primrec fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    let F (a : α) (c : Code) : σ :=
      RecursiveIn.Code.recOn c (z a) (s a) (l a) (r a) (o a) (pr a) (co a) (pc a) (rf a)
    Primrec fun a => F a (c a) :=
  primrec_recOn' hc hz hs hl hr ho
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

end RecursiveIn.Code
end

namespace RecursiveIn.Code
section

open Nat Computable

/-- Recursion on `RecursiveIn.Code` is computable. -/
theorem computable_recOn {α σ} [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Computable c)
    {z : α → σ} (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l)
    {r : α → σ} (hr : Computable r) {o : α → σ} (ho : Computable o) {pr : α → Code × Code × σ × σ → σ} (hpr : Computable₂ pr)
    {co : α → Code × Code × σ × σ → σ} (hco : Computable₂ co) {pc : α → Code × Code × σ × σ → σ}
    (hpc : Computable₂ pc) {rf : α → Code × σ → σ} (hrf : Computable₂ rf) :
    let PR (a) cf cg hf hg := pr a (cf, cg, hf, hg)
    let CO (a) cf cg hf hg := co a (cf, cg, hf, hg)
    let PC (a) cf cg hf hg := pc a (cf, cg, hf, hg)
    let RF (a) cf hf := rf a (cf, hf)
    let F (a : α) (c : Code) : σ :=
      RecursiveIn.Code.recOn c (z a) (s a) (l a) (r a) (o a) (PR a) (CO a) (PC a) (RF a)
    Computable fun a => F a (c a) := by
  intro _ _ _ _ F
  let G₁ : (α × List σ) × ℕ × ℕ → Option σ := fun p =>
    letI a := p.1.1; letI IH := p.1.2; letI n := p.2.1; letI m := p.2.2
    IH[m]?.bind fun s =>
    IH[m.unpair.1]?.bind fun s₁ =>
    IH[m.unpair.2]?.map fun s₂ =>
    cond n.bodd
      (cond n.div2.bodd (rf a (ofNat Code m, s))
        (pc a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
      (cond n.div2.bodd (co a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂))
        (pr a (ofNat Code m.unpair.1, ofNat Code m.unpair.2, s₁, s₂)))
  have : Computable G₁ := by
    refine option_bind (list_getElem?.comp (snd.comp fst) (snd.comp snd)) <| .mk ?_
    refine option_bind ((list_getElem?.comp (snd.comp fst)
      (fst.comp <| Computable.unpair.comp (snd.comp snd))).comp fst) <| .mk ?_
    refine option_map ((list_getElem?.comp (snd.comp fst)
      (snd.comp <| Computable.unpair.comp (snd.comp snd))).comp <| fst.comp fst) <| .mk ?_
    exact
      have a := fst.comp (fst.comp <| fst.comp <| fst.comp fst)
      have n := fst.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m := snd.comp (snd.comp <| fst.comp <| fst.comp fst)
      have m₁ := fst.comp (Computable.unpair.comp m)
      have m₂ := snd.comp (Computable.unpair.comp m)
      have s := snd.comp (fst.comp fst)
      have s₁ := snd.comp fst
      have s₂ := snd
      (nat_bodd.comp n).cond
        ((nat_bodd.comp <| nat_div2.comp n).cond
          (hrf.comp a (((Computable.ofNat Code).comp m).pair s))
          (hpc.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
        (Computable.cond (nat_bodd.comp <| nat_div2.comp n)
          (hco.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂))
          (hpr.comp a (((Computable.ofNat Code).comp m₁).pair <|
            ((Computable.ofNat Code).comp m₂).pair <| s₁.pair s₂)))
  let G : α → List σ → Option σ := fun a IH =>
    IH.length.casesOn (some (z a)) fun n =>
    n.casesOn (some (s a)) fun n =>
    n.casesOn (some (l a)) fun n =>
    n.casesOn (some (r a)) fun n =>
    n.casesOn (some (o a)) fun n =>
    G₁ ((a, IH), n, n.div2.div2)
  have : Computable₂ G := .mk <|
    nat_casesOn (list_length.comp snd) (option_some_iff.2 (hz.comp fst)) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hs.comp (fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hl.comp (fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (hr.comp (fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    nat_casesOn snd (option_some_iff.2 (ho.comp (fst.comp <| fst.comp <| fst.comp <| fst.comp fst))) <| .mk <|
    this.comp <|
      ((fst.pair snd).comp <| fst.comp <| fst.comp <| fst.comp <| fst.comp <| fst).pair <|
      snd.pair <| nat_div2.comp <| nat_div2.comp snd
  refine (nat_strong_rec (fun a n => F a (ofNat Code n)) this.to₂ fun a n => ?_)
    |>.comp .id (encode_iff.2 hc) |>.of_eq fun a => by simp
  iterate 5 rcases n with - | n; · simp [ofNatCode_eq, ofNatCode]; rfl
  simp only [G]; rw [List.length_map, List.length_range]
  let m := n.div2.div2
  change G₁ ((a, (List.range (n + 5)).map fun n => F a (ofNat Code n)), n, m)
    = some (F a (ofNat Code (n + 5)))
  have hm : m < n + 5 := by
    simp only [m, div2_val]
    exact lt_of_le_of_lt
      (le_trans (Nat.div_le_self ..) (Nat.div_le_self ..))
      (Nat.succ_le_succ (Nat.le_add_right ..))
  have m1 : m.unpair.1 < n + 5 := lt_of_le_of_lt m.unpair_left_le hm
  have m2 : m.unpair.2 < n + 5 := lt_of_le_of_lt m.unpair_right_le hm
  simp [G₁, m, hm, m1, m2]
  rw [show ofNat Code (n + 5) = ofNatCode (n + 5) from rfl]
  simp [ofNatCode]
  cases n.bodd <;> cases n.div2.bodd <;> rfl

end

/-- The interpretation of a `RecursiveIn.Code` as a partial function.
* `RecursiveIn.Code.zero`: The constant zero function.
* `RecursiveIn.Code.succ`: The successor function.
* `RecursiveIn.Code.left`: Left unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `RecursiveIn.Code.right`: Right unpairing of a pair of ℕ (encoded by `Nat.pair`)
* `RecursiveIn.Code.oracle`: The oracle function.
* `RecursiveIn.Code.pair`: Pairs the outputs of argument codes using `Nat.pair`.
* `RecursiveIn.Code.comp`: Composition of two argument codes.
* `RecursiveIn.Code.prec`: Primitive recursion. Given an argument of the form `Nat.pair a n`:
  * If `n = 0`, returns `eval cf o a`.
  * If `n = succ k`, returns `eval cg o (pair a (pair k (eval o (prec cf cg) (pair a k))))`
* `RecursiveIn.Code.rfind'`: Minimization starting at a provided value. Given an argument of the
  form `Nat.pair a m`, returns the least `n ≥ m` such that `eval cf o (pair a n) = 0`, if such an `n`
  exists and if `eval cf o (pair a k)` terminates for all `m ≤ k ≤ n`.
-/
def eval (c : Code) (o : ℕ →. ℕ) : ℕ →. ℕ := match c with
  | zero => pure 0
  | succ => Nat.succ
  | left => ↑fun n : ℕ => n.unpair.1
  | right => ↑fun n : ℕ => n.unpair.2
  | oracle => o
  | pair cf cg => fun n => Nat.pair <$> eval cf o n <*> eval cg o n
  | comp cf cg => fun n => eval cg o n >>= eval cf o
  | prec cf cg =>
    Nat.unpaired fun a n =>
      n.rec (eval cf o a) fun k IH => do
        let i ← IH
        eval cg o (Nat.pair a (Nat.pair k i))
  | rfind' cf =>
    Nat.unpaired fun a m =>
      (Nat.rfind fun n => (fun m => m = 0) <$> eval cf o (Nat.pair a (n + m))).map (· + m)

/-- Helper lemma for the evaluation of `prec` in the base case. -/
@[simp]
theorem eval_prec_zero (cf cg : Code) (o : ℕ →. ℕ) (a : ℕ) : eval (prec cf cg) o (Nat.pair a 0) = eval cf o a := by
  rw [eval, Nat.unpaired, Nat.unpair_pair]
  simp (config := { Lean.Meta.Simp.neutralConfig with proj := true }) only []
  rw [Nat.rec_zero]

/-- Helper lemma for the evaluation of `prec` in the recursive case. -/
theorem eval_prec_succ (cf cg : Code) (o : ℕ →. ℕ) (a k : ℕ) :
    eval (prec cf cg) o (Nat.pair a (Nat.succ k)) =
      do {let ih ← eval (prec cf cg) o (Nat.pair a k); eval cg o (Nat.pair a (Nat.pair k ih))} := by
  rw [eval, Nat.unpaired, Part.bind_eq_bind, Nat.unpair_pair]
  simp

/--
Evaluation of `ofPartrecCode` does not depend on the oracle.
-/
@[simp]
theorem eval_ofPartrecCode (c : Nat.Partrec.Code) (o : ℕ →. ℕ) : (Code.ofPartrecCode c).eval o = c.eval := by
  induction c with simp [ofPartrecCode, eval, Nat.Partrec.Code.eval, *]

@[simp]
theorem eval_const : ∀ n m o, eval (Code.const n) o m = Part.some n := by
  simp [Code.const]

@[simp]
theorem eval_id (n) : ∀ o, eval Code.id o n = Part.some n := by
  simp [Code.id]

@[simp]
theorem eval_curry (c o n x) : eval (curry c n) o x = eval c o (Nat.pair n x) := by
  simp! [Seq.seq, curry]

theorem primrec_const : Primrec Code.const :=
  (_root_.Primrec.id.nat_iterate (_root_.Primrec.const zero)
    (primrec₂_comp.comp (_root_.Primrec.const succ) Primrec.snd).to₂).of_eq
    fun n => by simp; induction n <;>
      simp [*, Nat.Partrec.Code.const, Code.const, Code.ofPartrecCode, Function.iterate_succ', -Function.iterate_succ]

theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp (primrec_const.comp Primrec.snd)
    (_root_.Primrec.const Code.id)

theorem curry_inj {c₁ c₂ n₁ n₂} (h : curry c₁ n₁ = curry c₂ n₂) : c₁ = c₂ ∧ n₁ = n₂ :=
  ⟨by injection h, by
    injection h with h₁ h₂
    injection h₂ with h₃ h₄
    exact const_inj h₃⟩

/--
The relative $S_n^m$ theorem: There is a computable function, namely `RecursiveIn.Code.curry`, that takes a
program and a ℕ `n`, and returns a new program using `n` as the first argument.
-/
theorem smn :
    ∃ f : Code → ℕ → Code, Computable₂ f ∧ ∀ c o n x, eval (f c n) o x = eval c o (Nat.pair n x) :=
  ⟨curry, Primrec₂.to_comp primrec₂_curry, eval_curry⟩

/-- A function `f` is Turing reducible to `g` if and only if there is a `Code` which evaluates to `f`, given oracle `g`. -/
theorem exists_code {f g : ℕ →. ℕ} : TuringReducible f g ↔ ∃ c : Code, eval c g = f := by
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
      refine ⟨comp (rfind' cf) (pair Code.id zero), ?_⟩
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
    | rfind' cf pf => exact pf.rfind'

end RecursiveIn.Code
