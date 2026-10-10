import OAI.RepresentationTheory.RowColumn.Basic

namespace OAI

noncomputable section

open scoped BigOperators Classical

namespace RowColumn.Signed
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
variable (odd : C → Prop) [DecidablePred odd]

/-- Words with exactly k odd entries. This is the k-parity sector of the
literal signed slot space, not a formal unknown representation. -/
abbrev Words (k : ℕ) := {w : S → C // Fintype.card {x : S // odd (w x)} = k}


variable {odd} {k : ℕ}

/-- Odd slots of a word, genuinely a subset of the board slots. -/
abbrev OddSlots (w : Words (S := S) odd k) := {x : S // odd (w.1 x)}

def relabelOddEquiv (g : Equiv.Perm S) (w : S → C) :
    {x : S // odd (w x)} ≃ {x : S // odd (w (g⁻¹ x))} where
  toFun x := ⟨g x.1, by simpa using x.2⟩
  invFun x := ⟨g⁻¹ x.1, x.2⟩
  left_inv := by intro x; ext; simp
  right_inv := by intro x; ext; simp

def actWord (g : Equiv.Perm S) (w : Words (S := S) odd k) : Words (S := S) odd k :=
  ⟨fun x => w.1 (g⁻¹ x), (Fintype.card_congr (relabelOddEquiv g w.1)).symm.trans w.2⟩

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma actWord_apply (g : Equiv.Perm S) (w : Words (S := S) odd k) (x : S) :
    (actWord g w).1 x = w.1 (g⁻¹ x) := rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma actWord_one (w : Words (S := S) odd k) : actWord 1 w = w := by
  apply Subtype.ext
  funext x
  rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma actWord_mul (g h : Equiv.Perm S) (w : Words (S := S) odd k) :
    actWord (g * h) w = actWord g (actWord h w) := by
  apply Subtype.ext
  funext x
  simp [actWord, mul_inv_rev]

/-- Canonical frames choose the odd-slot orientation. Different choices conjugate
by a diagonal sign; the signed action is exactly reordering the odd slots. -/
def oddFrame (w : Words (S := S) odd k) : OddSlots w ≃ Fin k :=
  Fintype.equivFinOfCardEq w.2

def oddPerm (g : Equiv.Perm S) (w : Words (S := S) odd k) : Equiv.Perm (Fin k) :=
  (oddFrame w).symm |>.trans ((relabelOddEquiv g w.1).trans (oddFrame (actWord g w)))

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddFrame_congr {w v : Words (S := S) odd k} (he : w = v)
    (x : S) (hx : odd (w.1 x)) (hv : odd (v.1 x)) :
    oddFrame w ⟨x, hx⟩ = oddFrame v ⟨x, hv⟩ := by
  subst v
  rfl

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma oddPerm_one (w : Words (S := S) odd k) : oddPerm 1 w = 1 := by
  apply Equiv.ext
  intro i
  change oddFrame (actWord 1 w) ⟨(oddFrame w).symm i, _⟩ = i
  have h := oddFrame_congr (actWord_one w) ((oddFrame w).symm i).1
    (show odd ((actWord 1 w).1 ((oddFrame w).symm i)) from ((oddFrame w).symm i).2)
    ((oddFrame w).symm i).2
  exact h.trans ((oddFrame w).apply_symm_apply i)

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_mul (g h : Equiv.Perm S) (w : Words (S := S) odd k) :
    oddPerm (g * h) w = oddPerm g (actWord h w) * oddPerm h w := by
  apply Equiv.ext
  intro i
  change oddFrame (actWord (g * h) w)
    ((relabelOddEquiv (g * h) w.1) ((oddFrame w).symm i)) =
    oddFrame (actWord g (actWord h w))
      ((relabelOddEquiv g (actWord h w).1)
        ((oddFrame (actWord h w)).symm
          (oddFrame (actWord h w) ((relabelOddEquiv h w.1) ((oddFrame w).symm i)))))
  erw [Equiv.symm_apply_apply]
  exact oddFrame_congr (actWord_mul g h w) _ _ _

def wordsEquiv (g : Equiv.Perm S) : Equiv.Perm (Words (S := S) odd k) where
  toFun := actWord g
  invFun := actWord g⁻¹
  left_inv := by intro w; rw [← actWord_mul, inv_mul_cancel, actWord_one]
  right_inv := by intro w; rw [← actWord_mul, mul_inv_cancel, actWord_one]

/-- Signed slot action in the orthonormal word basis. It reorders the odd
subsequence, and does not introduce a sign for even slots. -/
def signedMap (g : Equiv.Perm S) :
    EuclideanSpace ℂ (Words (S := S) odd k) →ₗ[ℂ] EuclideanSpace ℂ (Words (S := S) odd k) where
  toFun v := WithLp.toLp 2 (fun w => permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
  map_add' := by intro v z; ext w; simp [mul_add]
  map_smul' := by intro a v; ext w; simp [mul_left_comm]

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
@[simp] lemma signedMap_apply (g : Equiv.Perm S)
    (v : EuclideanSpace ℂ (Words (S := S) odd k)) (w : Words (S := S) odd k) :
    signedMap g v w = permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w) := rfl

/-- The signs genuinely compose; no group-action relation is assumed. -/
def representation : Representation ℂ (Equiv.Perm S) (EuclideanSpace ℂ (Words (S := S) odd k)) where
  toFun := signedMap
  map_one' := by ext v w; simp
  map_mul' g h := by
    ext v w
    simp only [signedMap_apply, Module.End.mul_apply, mul_inv_rev, oddPerm_mul,
      permSign_mul, actWord_mul, mul_assoc]
    ring

omit [DecidableEq C] in
lemma representation_unitary : CubeShuffle.UnitaryFinite.IsUnitary
    (representation (S := S) (odd := odd) (k := k)) := by
  intro g v z
  rw [PiLp.inner_apply, PiLp.inner_apply]
  change (∑ w, inner ℂ (permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
      (permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w))) = _
  have hh (w : Words (S := S) odd k) :
      inner ℂ (permSign (oddPerm g⁻¹ w) * v (actWord g⁻¹ w))
        (permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w)) =
      inner ℂ (v (actWord g⁻¹ w)) (z (actWord g⁻¹ w)) := by
    simp only [RCLike.inner_apply, map_mul, conj_permSign]
    rw [show permSign (oddPerm g⁻¹ w) * z (actWord g⁻¹ w) *
        (permSign (oddPerm g⁻¹ w) * (starRingEnd ℂ) (v (actWord g⁻¹ w))) =
      (permSign (oddPerm g⁻¹ w) * permSign (oddPerm g⁻¹ w)) *
        (z (actWord g⁻¹ w) * (starRingEnd ℂ) (v (actWord g⁻¹ w))) by ring,
      permSign_sq, one_mul]
  simp_rw [hh]
  exact Equiv.sum_comp (wordsEquiv g⁻¹) (fun w => inner ℂ (v w) (z w))

end RowColumn.Signed

namespace RowColumn.Signed
open scoped BigOperators Classical
open CubeShuffle.Specht

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma word_stabilizer_eq (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (x : S) : w.1 (g x) = w.1 x := by
  have he := congrArg (fun z : Words (S := S) odd k => z.1 (g x)) hw
  simpa using he.symm

omit [Fintype C] [DecidableEq C] in
lemma oddPerm_sign_of_stabilizes (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, ¬ odd (w.1 x) → g x = x) :
    permSign (oddPerm g w) = permSign g := by
  have hs : ∀ x, odd (w.1 (g x)) ↔ odd (w.1 x) := fun x => by
    rw [word_stabilizer_eq g w hw x]
  have he := Equiv.Perm.sign_eq_sign_of_equiv (g.subtypePerm hs)
    (oddPerm g w) (oddFrame w) (by
      intro x
      change oddFrame w ⟨g x.1, _⟩ =
        oddFrame (actWord g w)
          ((relabelOddEquiv g w.1) ((oddFrame w).symm (oddFrame w x)))
      erw [Equiv.symm_apply_apply]
      exact (oddFrame_congr hw (g x.1) _ _).symm)
  have hf : ∀ x, g x ≠ x → odd (w.1 x) := by
    intro x hn
    by_contra h
    exact hn (hfix x h)
  rw [Equiv.Perm.sign_subtypePerm g hs hf] at he
  exact congrArg (fun z : ℤˣ => ((z : ℤ) : ℂ)) he.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_of_odd_fixed (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) (hfix : ∀ x, odd (w.1 x) → g x = x) :
    oddPerm g w = 1 := by
  apply Equiv.ext
  intro i
  let x := (oddFrame w).symm i
  change oddFrame (actWord g w) ⟨g x.1, _⟩ = i
  have he := oddFrame_congr hw (g x.1)
    (show odd ((actWord g w).1 (g x.1)) by simpa using x.2)
    (by rw [hfix x.1 x.2]; exact x.2)
  refine he.trans ?_
  have hh : (⟨g x.1, by rw [hfix x.1 x.2]; exact x.2⟩ : OddSlots w) = x :=
    Subtype.ext (hfix x.1 x.2)
  rw [hh]
  exact (oddFrame w).apply_symm_apply i

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma actWord_inv_eq_iff (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    actWord g⁻¹ w = w ↔ actWord g w = w := by
  constructor
  · intro he
    have hh := congrArg (actWord g) he
    rw [← actWord_mul, mul_inv_cancel, actWord_one] at hh
    exact hh.symm
  · intro he
    have hh := congrArg (actWord g⁻¹) he
    rw [← actWord_mul, inv_mul_cancel, actWord_one] at hh
    exact hh.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_inv_stabilizer (g : Equiv.Perm S) (w : Words (S := S) odd k)
    (hw : actWord g w = w) : oddPerm g⁻¹ w = (oddPerm g w)⁻¹ := by
  have hh := oddPerm_mul g⁻¹ g w
  rw [inv_mul_cancel, oddPerm_one, hw] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

def wordVector (w : Words (S := S) odd k) : EuclideanSpace ℂ (Words (S := S) odd k) :=
  WithLp.toLp 2 (fun z => if z = w then 1 else 0)

omit [DecidableEq S] [Fintype C] in
lemma wordVector_coefficient (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    Signed.representation g (wordVector w) w =
      if actWord g w = w then permSign (oddPerm g w) else 0 := by
  change permSign (oddPerm g⁻¹ w) * (if actWord g⁻¹ w = w then (1 : ℂ) else 0) = _
  simp only [actWord_inv_eq_iff]
  split_ifs with he
  · rw [oddPerm_inv_stabilizer g w he, permSign_inv, mul_one]
  · exact mul_zero _

end RowColumn.Signed

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  {odd : C → Prop} [DecidablePred odd] {k : ℕ}

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma oddPerm_inv (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    oddPerm g⁻¹ (actWord g w) = (oddPerm g w)⁻¹ := by
  have hh := oddPerm_mul g⁻¹ g w
  rw [inv_mul_cancel, oddPerm_one] at hh
  exact eq_inv_of_mul_eq_one_left hh.symm

omit [DecidableEq S] [Fintype C] [DecidableEq C] in
lemma signedMap_transport_apply (g : Equiv.Perm S)
    (x : EuclideanSpace ℂ (Words (S := S) odd k)) (w : Words (S := S) odd k) :
    representation g x (actWord g w) = permSign (oddPerm g w) * x w := by
  change permSign (oddPerm g⁻¹ (actWord g w)) * x (actWord g⁻¹ (actWord g w)) = _
  rw [oddPerm_inv, permSign_inv, ← actWord_mul, inv_mul_cancel, actWord_one]

omit [DecidableEq S] [Fintype C] in
lemma signedMap_wordVector (g : Equiv.Perm S) (w : Words (S := S) odd k) :
    representation g (wordVector w) = permSign (oddPerm g w) • wordVector (actWord g w) := by
  ext z
  obtain ⟨v, rfl⟩ := (wordsEquiv g).surjective z
  change representation g (wordVector w) (actWord g v) = _
  rw [signedMap_transport_apply]
  change permSign (oddPerm g v) * (if v = w then (1 : ℂ) else 0) =
    permSign (oddPerm g w) * (if actWord g v = actWord g w then (1 : ℂ) else 0)
  have he : actWord g v = actWord g w ↔ v = w := (wordsEquiv g).apply_eq_iff_eq
  simp only [he]
  by_cases hv : v = w
  · subst v; rfl
  · simp [hv]

lemma permSign_ne_zero (g : Equiv.Perm S) : permSign g ≠ 0 := by
  intro he
  have H := permSign_sq g
  rw [he, zero_mul] at H
  exact zero_ne_one H

lemma sum_wordVectors (x : EuclideanSpace ℂ (Words (S := S) odd k)) :
    (∑ w, x w • wordVector w) = x := by
  ext z
  simp [WithLp.ofLp_sum, wordVector, WithLp.ofLp_smul]

variable {L : Type*} [Fintype L] [DecidableEq L] (line : S → L)

abbrev lineRepresentation :=
  (representation (S := S) (odd := odd) (k := k)).comp (RowColumn.lineGroup line).subtype

omit [Fintype L] [DecidableEq L] [DecidableEq S] [Fintype C] in
lemma commuting_coefficient_relation
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (g : RowColumn.lineGroup line) (w v : Words (S := S) odd k) :
    permSign (oddPerm g.1 v) * T (wordVector (actWord g.1 v)) (actWord g.1 w) =
    permSign (oddPerm g.1 w) * T (wordVector v) w := by
  have he := congrArg (fun x : EuclideanSpace ℂ (Words (S := S) odd k) => x (actWord g.1 w))
    (Representation.IntertwiningMap.isIntertwining _ _ T g (wordVector v))
  change T (representation g.1 (wordVector v)) (actWord g.1 w) =
    representation g.1 (T (wordVector v)) (actWord g.1 w) at he
  rw [signedMap_wordVector, map_smul, signedMap_transport_apply] at he
  exact he

end RowColumn.Signed

namespace RowColumn.WordOrbits

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- A complete invariant of the simultaneous permutation orbit of finitely
many words: the counts of their joint symbols. -/
def counts (f : S → A) : A → Fin (Fintype.card S + 1) := fun a =>
  ⟨Fintype.card {x : S // f x = a},
    Nat.lt_succ_of_le (Fintype.card_subtype_le (fun x => f x = a))⟩

omit [Fintype A] in
lemma same_counts_permutation (f g : S → A) (he : counts f = counts g) :
    ∃ p : Equiv.Perm S, ∀ x, g (p x) = f x := by
  have hc (a : A) : Fintype.card {x : S // f x = a} = Fintype.card {x : S // g x = a} :=
    congrArg (fun z : A → Fin (Fintype.card S + 1) => (z a).1) he
  let e (a : A) : {x : S // f x = a} ≃ {x : S // g x = a} := Fintype.equivOfCardEq (hc a)
  let p : Equiv.Perm S := (Equiv.sigmaFiberEquiv f).symm |>.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv g))
  refine ⟨p, ?_⟩
  intro x
  change g ((e (f x) ⟨x, rfl⟩).1) = f x
  exact (e (f x) ⟨x, rfl⟩).2

/-- The label can record a row or a column. Joint counts then give a
word transporter inside the actual line subgroup, not an abstract action. -/
lemma line_pair_transporter {L C : Type*} [Fintype L] [Fintype C]
    [DecidableEq L] [DecidableEq C]
    (line : S → L) (w v w' v' : S → C)
    (he : counts (fun x => (line x, w x, v x)) = counts (fun x => (line x, w' x, v' x))) :
    ∃ p : Equiv.Perm S, (∀ x, line (p x) = line x) ∧
      (∀ x, w' (p x) = w x) ∧ (∀ x, v' (p x) = v x) := by
  obtain ⟨p, hp⟩ := same_counts_permutation _ _ he
  refine ⟨p, (fun x => congrArg Prod.fst (hp x)), ?_⟩
  exact ⟨(fun x => congrArg (fun z => z.2.1) (hp x)),
    (fun x => congrArg (fun z => z.2.2) (hp x))⟩

end RowColumn.WordOrbits

namespace RowColumn.Signed
open CubeShuffle.Specht
open scoped BigOperators Classical

variable {S C L : Type*} [Fintype S] [DecidableEq S] [Fintype C] [DecidableEq C]
  [Fintype L] [DecidableEq L] {odd : C → Prop} [DecidablePred odd] {k : ℕ}
  (line : S → L)

abbrev PairCountIndex := (L × C × C) → Fin (Fintype.card S + 1)

def pairCounts (wv : Words (S := S) odd k × Words (S := S) odd k) :
    PairCountIndex (S := S) (C := C) (L := L) :=
  RowColumn.WordOrbits.counts (fun x => (line x, wv.1.1 x, wv.2.1 x))

/-- Record one matrix coefficient per joint-symbol contingency table. Zero
coefficients in these representatives force every coefficient to be zero. -/
def commutantData :
    Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line) →ₗ[ℂ]
        (PairCountIndex (S := S) (C := C) (L := L) → ℂ) where
  toFun T a := if ha : ∃ wv, pairCounts (odd := odd) (k := k) line wv = a then
      T (wordVector (Classical.choose ha).2) (Classical.choose ha).1 else 0
  map_add' T U := by
    funext a
    dsimp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' z T := by
    funext a
    dsimp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

lemma commutantData_zero
    (T : Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
      (lineRepresentation (odd := odd) (k := k) line))
    (hz : commutantData line T = 0) : T = 0 := by
  have hT (v : Words (S := S) odd k) : T (wordVector v) = 0 := by
    ext w
    let a := pairCounts line (w, v)
    have ha : ∃ wv, pairCounts (odd := odd) (k := k) line wv = a := ⟨(w, v), rfl⟩
    let p := Classical.choose ha
    have hp : pairCounts line p = a := Classical.choose_spec ha
    have hrep : T (wordVector p.2) p.1 = 0 := by
      have hh := congrArg (fun z : PairCountIndex (S := S) (C := C) (L := L) → ℂ => z a) hz
      simpa only [commutantData, LinearMap.coe_mk, AddHom.coe_mk, dite_eq_left ha, Pi.zero_apply]
        using hh
    obtain ⟨g, hl, hw, hv⟩ := RowColumn.WordOrbits.line_pair_transporter line
      w.1 v.1 p.1.1 p.2.1 hp.symm
    have hgw : actWord g w = p.1 := by
      apply Subtype.ext
      funext x
      have hh := hw (g⁻¹ x)
      simpa using hh.symm
    have hgv : actWord g v = p.2 := by
      apply Subtype.ext
      funext x
      have hh := hv (g⁻¹ x)
      simpa using hh.symm
    have hre := commuting_coefficient_relation line T ⟨g, hl⟩ w v
    rw [hgw, hgv, hrep, mul_zero] at hre
    exact (mul_eq_zero.mp hre.symm).resolve_left (permSign_ne_zero _)
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change T x = 0
  rw [← sum_wordVectors x, map_sum]
  simp only [map_smul, hT, smul_zero, Finset.sum_const_zero]

lemma commutantData_injective : Function.Injective
    (commutantData (odd := odd) (k := k) line) := by
  intro T U he
  apply sub_eq_zero.mp
  apply commutantData_zero line
  rw [map_sub, he, sub_self]

/-- Polynomial local multiplicity infrastructure, proved directly from
simultaneous signed-word orbits. This avoids assuming any LR-count estimate.
For the occupied board C has 2h colors, giving exponent 4*|lines|*h². -/
theorem commutant_dimension_bound :
    Module.finrank ℂ
      (Representation.IntertwiningMap (lineRepresentation (odd := odd) (k := k) line)
        (lineRepresentation (odd := odd) (k := k) line)) ≤
      (Fintype.card S + 1) ^ (Fintype.card L * Fintype.card C ^ 2) := by
  have hf := LinearMap.finrank_le_finrank_of_injective
    (f := commutantData (odd := odd) (k := k) line) (commutantData_injective line)
  simpa only [Module.finrank_fintype_fun_eq_card, PairCountIndex, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_prod, pow_two] using hf

end RowColumn.Signed

end

end OAI
