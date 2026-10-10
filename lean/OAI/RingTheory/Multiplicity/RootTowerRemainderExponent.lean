import Mathlib
import OAI.RingTheory.Multiplicity.StandardFactorChartsL

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
namespace Lech.RootTower
variable {σ R : Type*} [Fintype σ] [CommRing R] (q : ℕ) [NeZero q]

def remainderExponent (r : σ → Fin q) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i : ℕ))

omit [NeZero q] in
@[simp] lemma remainderExponent_apply (r : σ → Fin q) (i : σ) :
    remainderExponent q r i = (r i : ℕ) := by
  simp [remainderExponent]

def exponentRemainder (d : σ →₀ ℕ) : σ → Fin q :=
  fun i => ⟨d i % q, Nat.mod_lt _ (NeZero.pos q)⟩

def exponentQuotient (d : σ →₀ ℕ) : σ →₀ ℕ :=
  d.mapRange (fun n => n / q) (Nat.zero_div q)

lemma exponent_split (d : σ →₀ ℕ) :
    q • exponentQuotient q d + remainderExponent q (exponentRemainder q d) = d := by
  ext i
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    exponentQuotient, Finsupp.mapRange_apply, remainderExponent_apply, exponentRemainder]
  exact Nat.div_add_mod (d i) q

@[simp] lemma exponentRemainder_split (d : σ →₀ ℕ) (r : σ → Fin q) :
    exponentRemainder q (q • d + remainderExponent q r) = r := by
  funext i
  apply Fin.ext
  simp [exponentRemainder, Nat.add_mod, Nat.mod_eq_of_lt (r i).isLt]

@[simp] lemma exponentQuotient_split (d : σ →₀ ℕ) (r : σ → Fin q) :
    exponentQuotient q (q • d + remainderExponent q r) = d := by
  ext i
  simp [exponentQuotient, Nat.mul_add_div (NeZero.pos q),
    Nat.div_eq_of_lt (r i).isLt]

lemma coeff_expansion_monomial_eq_zero (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) (hr : r ≠ exponentRemainder q d) :
    coeff d (expand q (NeZero.ne q) f * monomial (remainderExponent q r) 1) = 0 := by
  rw [coeff_mul_monomial]
  split_ifs with hle
  · rw [mul_one]
    by_contra hf
    have hs : d - remainderExponent q r ∈ (expand q (NeZero.ne q) f).support := hf
    rw [support_expand] at hs
    obtain ⟨a, _, ha⟩ := hs
    change q • a = d - remainderExponent q r at ha
    have hd : d = q • a + remainderExponent q r := by
      rw [ha, tsub_add_cancel_of_le hle]
    exact hr (by rw [hd, exponentRemainder_split])
  · rfl

lemma coeff_expansion_monomial_split (f : MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    coeff (q • d + remainderExponent q r)
      (expand q (NeZero.ne q) f * monomial (remainderExponent q r) 1) = coeff d f := by
  rw [coeff_add_mul_monomial, coeff_expand_smul, mul_one]

 
def extract (r : σ → Fin q) (f : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun d => coeff (q • d + remainderExponent q r) f

lemma sum_expansion_extract (f : MvPowerSeries σ R) :
    (∑ r : σ → Fin q, expand q (NeZero.ne q) (extract q r f) *
      monomial (remainderExponent q r) 1) = f := by
  ext d
  simp only [map_sum]
  rw [Finset.sum_eq_single (exponentRemainder q d)]
  · conv_lhs => arg 1; rw [← exponent_split q d]
    rw [coeff_expansion_monomial_split]
    change coeff (q • exponentQuotient q d + remainderExponent q (exponentRemainder q d)) f = _
    rw [exponent_split]
  · intro r _ hr
    exact coeff_expansion_monomial_eq_zero q (extract q r f) d r hr
  · simp

lemma coeff_sum_expansion (f : (σ → Fin q) → MvPowerSeries σ R)
    (d : σ →₀ ℕ) (r : σ → Fin q) :
    coeff (q • d + remainderExponent q r)
      (∑ t, expand q (NeZero.ne q) (f t) * monomial (remainderExponent q t) 1) =
      coeff d (f r) := by
  simp only [map_sum]
  rw [Finset.sum_eq_single r]
  · exact coeff_expansion_monomial_split q (f r) d r
  · intro t _ ht
    apply coeff_expansion_monomial_eq_zero
    simpa using ht
  · simp

 
def Expanded (_q : ℕ) := MvPowerSeries σ R

instance expandedCommRing : CommRing (Expanded (σ := σ) (R := R) q) :=
  inferInstanceAs (CommRing (MvPowerSeries σ R))

noncomputable instance expandedAlgebra :
    Algebra (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q) :=
  (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom.toAlgebra

noncomputable def expansionMap :
    ((σ → Fin q) → MvPowerSeries σ R) →ₗ[MvPowerSeries σ R]
      Expanded (σ := σ) (R := R) q where
  toFun f := ∑ r, expand q (NeZero.ne q) (f r) * monomial (remainderExponent q r) 1
  map_add' f g := by
    change (∑ r, expand q (NeZero.ne q) (f r + g r) * _) = _
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    rfl
  map_smul' a f := by
    change (∑ r, expand q (NeZero.ne q) (a * f r) * _) =
      expand q (NeZero.ne q) a *
        (∑ r, expand q (NeZero.ne q) (f r) * monomial (remainderExponent q r) 1)
    simp only [map_mul, mul_assoc, Finset.mul_sum]

lemma expansionMap_bijective : Function.Bijective (expansionMap (σ := σ) (R := R) q) := by
  constructor
  · intro f g hfg
    funext r
    ext d
    have hh := congrArg (coeff (q • d + remainderExponent q r)) hfg
    exact (coeff_sum_expansion q f d r).symm.trans
      (hh.trans (coeff_sum_expansion q g d r))
  · intro f
    exact ⟨fun r => extract q r f, sum_expansion_extract q f⟩

noncomputable def expansionEquiv :
    ((σ → Fin q) → MvPowerSeries σ R) ≃ₗ[MvPowerSeries σ R]
      Expanded (σ := σ) (R := R) q :=
  LinearEquiv.ofBijective (expansionMap q) (expansionMap_bijective q)

noncomputable def expansionBasis : Module.Basis (σ → Fin q) (MvPowerSeries σ R)
    (Expanded (σ := σ) (R := R) q) :=
  (Pi.basisFun (MvPowerSeries σ R) (σ → Fin q)).map (expansionEquiv q)

lemma expanded_free : Module.Free (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q) :=
  Module.Free.of_basis (expansionBasis q)

lemma expansion_flat : (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom.Flat := by
  let := expanded_free (σ := σ) (R := R) q
  exact inferInstanceAs (Module.Flat (MvPowerSeries σ R) (Expanded (σ := σ) (R := R) q))

omit [Fintype σ] in
lemma expansion_local : IsLocalHom (expand (σ := σ) (R := R) q (NeZero.ne q)).toRingHom := by
  constructor
  intro f hf
  rw [isUnit_iff_constantCoeff] at hf ⊢
  change IsUnit (constantCoeff (expand q (NeZero.ne q) f)) at hf
  simpa only [constantCoeff_expand] using hf

omit [Fintype σ] in
lemma map_bijective_of_bijective {S : Type*} [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f) :
    Function.Bijective (MvPowerSeries.map (σ := σ) f) := by
  constructor
  · intro x y h
    ext d
    apply hf.1
    exact congrArg (coeff d) h
  · intro x
    choose y hy using fun d => hf.2 (coeff d x)
    refine ⟨y, ?_⟩
    ext d
    exact hy d

instance powerSeriesCharP (p : ℕ) [CharP R p] : CharP (MvPowerSeries σ R) p :=
  charP_of_injective_ringHom (C_injective (σ := σ) (R := R)) p

omit [NeZero q] in
lemma iterateFrobenius_flat (p n : ℕ) [Fact p.Prime] [CharP R p]
    [PerfectRing R p] : (iterateFrobenius (MvPowerSeries σ R) p n).Flat := by
  let : NeZero (p^n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  have hm : (MvPowerSeries.map (σ := σ) (iterateFrobenius R p n)).Flat :=
    RingHom.Flat.of_bijective (map_bijective_of_bijective _ (bijective_iterateFrobenius R p n))
  have he := (expansion_flat (σ := σ) (R := R) (p^n)).comp hm
  have hp : (MvPowerSeries.map (σ := σ) (iterateFrobenius R p n)).comp
      (expand (p^n) (NeZero.ne (p^n))).toRingHom =
      iterateFrobenius (MvPowerSeries σ R) p n := by
    ext f d
    exact congrArg (coeff d) (map_iterateFrobenius_expand p (Nat.Prime.ne_zero Fact.out) f n)
  exact hp ▸ he

end Lech.RootTower

open scoped TensorProduct
open IsLocalRing
namespace Lech.RootTower

variable {R S ι : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  [Algebra R S] [IsLocalHom (algebraMap R S)] [Fintype ι]

lemma fiber_length_of_basis (b : Module.Basis ι R S)
    (hres : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Module.length S (S ⧸ (maximalIdeal R).map (algebraMap R S)) = Fintype.card ι := by
  let Q := S ⧸ (maximalIdeal R).map (algebraMap R S)
  have hr : Module.length (ResidueField R) (ResidueField S) = 1 := by
    rw [Module.length_eq_of_surjective (R := ResidueField S) (M := ResidueField S) hres]
    simp
  have hlen := IsLocalRing.length_restrictScalars R S Q
  rw [hr, mul_one] at hlen
  rw [← hlen]
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (maximalIdeal R)).toLinearEquiv
  rw [(e.restrictScalars R).length_eq]
  change Module.length R (S ⊗[R] ResidueField R) = _
  rw [(TensorProduct.comm R S (ResidueField R)).length_eq]
  let b' := b.baseChange (ResidueField R)
  have he := b'.repr.length_eq
  rw [Module.length_eq_of_surjective (R := ResidueField R) (M := ResidueField R ⊗[R] S)
    (residue_surjective (R := R)), he]
  simp [Module.length_finsupp, ENat.card]

end Lech.RootTower

open MvPowerSeries IsLocalRing
namespace Lech.RootTower
variable {σ k : Type*} [Fintype σ] [Field k]

omit [Fintype σ] in
lemma residue_eq_constant (f : MvPowerSeries σ k) :
    residue (MvPowerSeries σ k) f = residue (MvPowerSeries σ k) (C (constantCoeff f)) := by
  apply Ideal.Quotient.eq.mpr
  rw [mem_maximalIdeal]
  change ¬ IsUnit (f - C (constantCoeff f))
  rw [isUnit_iff_constantCoeff]
  simp

variable (p n : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

def FrobeniusExpanded (_p _n : ℕ) := MvPowerSeries σ k
instance frobeniusExpandedRing : CommRing (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  inferInstanceAs (CommRing (MvPowerSeries σ k))
instance frobeniusExpandedLocal : IsLocalRing (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  inferInstanceAs (IsLocalRing (MvPowerSeries σ k))
instance frobeniusExpandedAlgebra :
    Algebra (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  (iterateFrobenius (MvPowerSeries σ k) p n).toAlgebra

def expansionToFrobeniusMap [NeZero (p^n)] :
    Expanded (σ := σ) (R := k) (p^n) →ₗ[MvPowerSeries σ k]
      FrobeniusExpanded (σ := σ) (k := k) p n where
  toFun x := MvPowerSeries.map (iterateFrobenius k p n) x
  map_add' := map_add _
  map_smul' a x := by
    refine (map_mul (MvPowerSeries.map (iterateFrobenius k p n))
      (expand (p^n) (NeZero.ne (p^n)) a) (show MvPowerSeries σ k from x)).trans ?_
    exact congrArg (fun f : MvPowerSeries σ k =>
      @Mul.mul (MvPowerSeries σ k) _ f (MvPowerSeries.map (iterateFrobenius k p n) x))
      (map_iterateFrobenius_expand p (Nat.Prime.ne_zero Fact.out) a n)

def expansionToFrobenius [NeZero (p^n)] :
    Expanded (σ := σ) (R := k) (p^n) ≃ₗ[MvPowerSeries σ k]
      FrobeniusExpanded (σ := σ) (k := k) p n :=
  LinearEquiv.ofBijective (expansionToFrobeniusMap (σ := σ) (k := k) p n)
    (map_bijective_of_bijective _ (bijective_iterateFrobenius k p n))

def frobeniusBasis [NeZero (p^n)] :
    Module.Basis (σ → Fin (p^n)) (MvPowerSeries σ k)
      (FrobeniusExpanded (σ := σ) (k := k) p n) :=
  (expansionBasis (p^n)).map (expansionToFrobenius (σ := σ) (k := k) p n)

instance frobeniusExpandedLocalHom :
    IsLocalHom (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n)) where
  map_nonunit x hx := by
    change IsUnit (iterateFrobenius (MvPowerSeries σ k) p n x) at hx
    rw [iterateFrobenius_def] at hx
    exact (isUnit_pow_iff (pow_ne_zero n (Nat.Prime.ne_zero Fact.out))).mp hx

omit [Fintype σ] in
lemma frobenius_residue_surjective : Function.Surjective
    (ResidueField.map (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n))) := by
  intro x
  obtain ⟨f,rfl⟩ := residue_surjective x
  obtain ⟨c,hc⟩ := (bijective_iterateFrobenius k p n).2 (constantCoeff f)
  refine ⟨residue (MvPowerSeries σ k) (C c), ?_⟩
  rw [ResidueField.map_residue]
  change residue (MvPowerSeries σ k) (iterateFrobenius (MvPowerSeries σ k) p n (C c)) =
    residue (MvPowerSeries σ k) f
  rw [← RingHom.map_iterateFrobenius, hc]
  exact (residue_eq_constant f).symm

lemma frobenius_fiber_length :
    Module.length (FrobeniusExpanded (σ := σ) (k := k) p n)
      (FrobeniusExpanded (σ := σ) (k := k) p n ⧸
        (maximalIdeal (MvPowerSeries σ k)).map
          (algebraMap (MvPowerSeries σ k) (FrobeniusExpanded (σ := σ) (k := k) p n))) =
        (p ^ (n * Fintype.card σ) : ℕ) := by
  let : NeZero (p^n) := ⟨pow_ne_zero n (Nat.Prime.ne_zero Fact.out)⟩
  rw [fiber_length_of_basis (frobeniusBasis (σ := σ) (k := k) p n)
    (frobenius_residue_surjective p n)]
  simp [← pow_mul]

end Lech.RootTower


namespace Lech.RootTower
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

 
def rootMap (n : ℕ) : A →+* PerfectClosure A p where
  toFun x := PerfectClosure.mk A p (n, x)
  map_one' := by simpa using (PerfectClosure.natCast A p n 1).symm
  map_zero' := PerfectClosure.mk_zero_right A p n
  map_mul' x y := by
    rw [PerfectClosure.mk_mul_mk, PerfectClosure.eq_iff]
    simp only [← coe_iterateFrobenius, map_mul]
    simp only [coe_iterateFrobenius, ← Function.iterate_add_apply]
  map_add' x y := by
    rw [PerfectClosure.mk_add_mk, PerfectClosure.eq_iff]
    simp only [← coe_iterateFrobenius, map_add]
    simp only [coe_iterateFrobenius, ← Function.iterate_add_apply]

lemma rootMap_injective (n : ℕ) : Function.Injective (rootMap A p n) := by
  intro x y h
  exact (frobenius_inj A p).iterate n ((PerfectClosure.eq_iff A p _ _).mp h)

lemma rootMap_transition (n m : ℕ) (h : n ≤ m) (x : A) :
    rootMap A p m (iterateFrobenius A p (m-n) x) = rootMap A p n x := by
  have hh := PerfectClosure.R.sound A p (m-n) n x
    (iterateFrobenius A p (m-n) x) (by rw [coe_iterateFrobenius])
  simpa only [Nat.sub_add_cancel h, rootMap, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk] using hh.symm

def rootRing (n : ℕ) : Subring (PerfectClosure A p) := (rootMap A p n).range

lemma rootRing_mono : Monotone (rootRing A p) := by
  intro n m h x hx
  obtain ⟨a, rfl⟩ := hx
  exact ⟨iterateFrobenius A p (m-n) a, rootMap_transition A p n m h a⟩

def rootEquiv (n : ℕ) : A ≃+* rootRing A p n :=
  RingEquiv.ofBijective (rootMap A p n).rangeRestrict
    ⟨fun _ _ h => rootMap_injective A p n (congrArg Subtype.val h),
      (rootMap A p n).rangeRestrict_surjective⟩

lemma rootEquiv_apply (n : ℕ) (a : A) :
    (rootEquiv A p n a : PerfectClosure A p) = rootMap A p n a := rfl

lemma rootRing_exhaustive (x : PerfectClosure A p) : ∃ n, x ∈ rootRing A p n := by
  obtain ⟨⟨n,a⟩, rfl⟩ := PerfectClosure.mk_surjective A p x
  exact ⟨n, a, rfl⟩

instance rootRing_local [IsLocalRing A] (n : ℕ) : IsLocalRing (rootRing A p n) :=
  (rootEquiv A p n).isLocalRing

instance rootRing_noetherian [IsNoetherianRing A] (n : ℕ) :
    IsNoetherianRing (rootRing A p n) :=
  isNoetherianRing_of_ringEquiv A (rootEquiv A p n)

lemma root_inclusion_eq (n m : ℕ) (h : n ≤ m) :
    Subring.inclusion (rootRing_mono A p h) =
      (rootEquiv A p m).toRingHom.comp
        ((iterateFrobenius A p (m-n)).comp (rootEquiv A p n).symm.toRingHom) := by
  ext x
  change (x : PerfectClosure A p) = rootMap A p m
    (iterateFrobenius A p (m-n) ((rootEquiv A p n).symm x))
  rw [rootMap_transition A p n m h]
  exact congrArg Subtype.val ((rootEquiv A p n).apply_symm_apply x).symm

lemma root_inclusion_flat (hflat : ∀ j, (iterateFrobenius A p j).Flat)
    (n m : ℕ) (h : n ≤ m) : (Subring.inclusion (rootRing_mono A p h)).Flat := by
  rw [root_inclusion_eq A p n m h]
  exact ((RingHom.Flat.of_bijective (rootEquiv A p n).symm.bijective).comp
    (hflat (m-n))).comp (RingHom.Flat.of_bijective (rootEquiv A p m).bijective)

omit [IsReduced A] in
lemma iterateFrobenius_local (n : ℕ) : IsLocalHom (iterateFrobenius A p n) where
  map_nonunit x hx := by
    rw [iterateFrobenius_def] at hx
    exact (isUnit_pow_iff (pow_ne_zero n (Nat.Prime.ne_zero Fact.out))).mp hx

lemma root_inclusion_local [IsLocalRing A] (n m : ℕ) (h : n ≤ m) :
    IsLocalHom (Subring.inclusion (rootRing_mono A p h)) := by
  rw [root_inclusion_eq A p n m h]
  let := iterateFrobenius_local A p (m-n)
  let : IsLocalHom (rootEquiv A p m).toRingHom :=
    ⟨fun x hx => by simpa using hx.map (rootEquiv A p m).symm.toMonoidHom⟩
  let : IsLocalHom (rootEquiv A p n).symm.toRingHom :=
    ⟨fun x hx => by simpa using hx.map (rootEquiv A p n).toMonoidHom⟩
  infer_instance

end Lech.RootTower


namespace Lech.RootTower

lemma self_length_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  let f : R →ₛₗ[e.toRingHom] S :=
    { toAddHom := e.toAddMonoidHom, map_smul' := fun r x => e.map_mul r x }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f e.bijective)

lemma quotient_length_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : J = I.map e) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  rw [Module.length_eq_of_surjective (R := R ⧸ I) (Ideal.Quotient.mk_surjective),
    Module.length_eq_of_surjective (R := S ⧸ J) (Ideal.Quotient.mk_surjective)]
  exact self_length_ringEquiv (Ideal.quotientEquiv I J e h)



open IsLocalRing
variable (A : Type*) [CommRing A] [IsReduced A] [IsLocalRing A]
  (p : ℕ) [Fact p.Prime] [CharP A p]

omit [IsLocalRing A] in
lemma root_inclusion_comp_equiv (n m : ℕ) (h : n ≤ m) :
    (Subring.inclusion (rootRing_mono A p h)).comp (rootEquiv A p n).toRingHom =
      (rootEquiv A p m).toRingHom.comp (iterateFrobenius A p (m-n)) := by
  rw [root_inclusion_eq A p n m h]
  ext a
  simp

lemma root_fiber_ideal (n m : ℕ) (h : n ≤ m) :
    (maximalIdeal (rootRing A p n)).map (Subring.inclusion (rootRing_mono A p h)) =
      ((maximalIdeal A).map (iterateFrobenius A p (m-n))).map (rootEquiv A p m) := by
  calc
    _ = ((maximalIdeal A).map (rootEquiv A p n).toRingHom).map
        (Subring.inclusion (rootRing_mono A p h)) :=
      congrArg (Ideal.map (Subring.inclusion (rootRing_mono A p h)))
        (map_ringEquiv_maximalIdeal (rootEquiv A p n)).symm
    _ = (maximalIdeal A).map ((Subring.inclusion (rootRing_mono A p h)).comp
        (rootEquiv A p n).toRingHom) :=
      (maximalIdeal A).map_map _ _
    _ = (maximalIdeal A).map ((rootEquiv A p m).toRingHom.comp
        (iterateFrobenius A p (m-n))) :=
      congrArg (fun f => (maximalIdeal A).map f) (root_inclusion_comp_equiv A p n m h)
    _ = _ := (Ideal.map_map (I := maximalIdeal A) (iterateFrobenius A p (m-n))
      (rootEquiv A p m).toRingHom).symm

lemma root_fiber_length (n m : ℕ) (h : n ≤ m) :
    Module.length (rootRing A p m) ((rootRing A p m) ⧸
      (maximalIdeal (rootRing A p n)).map (Subring.inclusion (rootRing_mono A p h))) =
      Module.length A (A ⧸ (maximalIdeal A).map (iterateFrobenius A p (m-n))) :=
  (quotient_length_ringEquiv (rootEquiv A p m) _ _ (root_fiber_ideal A p n m h)).symm

end Lech.RootTower
end

end OAI
