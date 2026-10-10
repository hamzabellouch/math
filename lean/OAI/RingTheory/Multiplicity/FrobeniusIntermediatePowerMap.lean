import Mathlib
import OAI.RingTheory.Multiplicity.LechFiniteFree
import OAI.RingTheory.Multiplicity.LechLengthLe

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct
namespace Lech.FrobeniusIntermediate
variable {D : Type*} [CommRing D] (p : ℕ) [Fact p.Prime] [CharP D p]
    (B : Subring D) (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)

def powerMap : D →+* B :=
  (iterateFrobenius D p e).codRestrict B (by intro x; simpa only [iterateFrobenius_def] using he x)

lemma powerMap_val (x : D) : (powerMap p B e he x : D) = x^(p^e) := rfl

lemma inclusion_comp_powerMap : (B.subtype).comp (powerMap p B e he) = iterateFrobenius D p e := rfl

instance [IsLocalRing D] [IsLocalRing B] : IsLocalHom (powerMap p B e he) where
  map_nonunit x hx := by
    have hu := hx.map B.subtype
    change IsUnit (x^(p^e)) at hu
    exact (isUnit_pow_iff (pow_ne_zero e (Fact.out : p.Prime).ne_zero)).mp hu

lemma map_radical_primary [IsLocalRing D] [IsLocalRing B] [IsLocalHom B.subtype]
    (H : Ideal D) (hH : H.radical = IsLocalRing.maximalIdeal D) :
    (H.map (powerMap p B e he)).radical = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · apply (IsLocalRing.maximalIdeal.isMaximal B).isPrime.isRadical.radical_le_iff.mpr
    apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    exact IsLocalRing.mem_maximalIdeal (powerMap p B e he x) |>.mpr
      (fun hunit => (IsLocalRing.mem_maximalIdeal x).mp
        (hH ▸ Ideal.le_radical hx) (isUnit_of_map_unit (powerMap p B e he) _ hunit))
  · intro b hb
    have hd : (b : D) ∈ H.radical := by
      rw [hH]
      exact show (b : D) ∈ IsLocalRing.maximalIdeal D from
        (show b ∈ (IsLocalRing.maximalIdeal D).comap B.subtype from
          (IsLocalRing.maximalIdeal_comap B.subtype).symm ▸ hb)
    obtain ⟨n,hn⟩ := hd
    refine ⟨n*(p^e),?_⟩
    have hg := Ideal.mem_map_of_mem (powerMap p B e he) hn
    convert hg using 1
    apply Subtype.ext
    simp only [powerMap_val,Subring.coe_pow,pow_mul]

lemma mapped_ideal (H : Ideal D) :
    (H.map (powerMap p B e he)).map B.subtype = H.map (iterateFrobenius D p e) := by
  rw [Ideal.map_map]
  rfl

instance : CharP B p := B.subtype.charP Subtype.val_injective p

lemma inclusion_comp_iterateFrobenius (n : ℕ) :
    B.subtype.comp (iterateFrobenius B p n) =
      (iterateFrobenius D p n).comp B.subtype := by
  ext x
  simp only [RingHom.comp_apply,iterateFrobenius_def,map_pow]

lemma map_frobenius_ideal (H : Ideal D) (n : ℕ) :
    ((H.map (powerMap p B e he)).map (iterateFrobenius B p n)).map B.subtype =
      H.map (iterateFrobenius D p (e+n)) := by
  rw [Ideal.map_map,inclusion_comp_iterateFrobenius,← Ideal.map_map,mapped_ideal,Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply,iterateFrobenius_def,← pow_mul,← pow_add]

end Lech.FrobeniusIntermediate


namespace Lech.FrobeniusIntermediate
open Filter
open scoped ENNReal Topology nonZeroDivisors
variable {D : Type*} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
    [Module.Finite B D]

omit [IsNoetherianRing D] [IsNoetherianRing B] [IsLocalHom B.subtype] in
lemma quotient_length_eq (I : Ideal B)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D))) :
    Module.length B (D ⧸ I • (⊤ : Submodule B D)) = Module.length D (D ⧸ I.map B.subtype) := by
  rw [Ideal.smul_top_eq_map]
  rw [(Submodule.Quotient.restrictScalarsEquiv B (I.map (algebraMap B D))).length_eq]
  rw [IsLocalRing.length_restrictScalars B D _,
    Module.length_eq_of_surjective (R := IsLocalRing.ResidueField D) hres]
  simp
  rfl

omit [IsNoetherianRing D] in
 

theorem exists_positive_rank_transfer :
    ∃ r : ℕ, 0 < r ∧ ∀ (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
      (_hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
      (H : Ideal D) (_hH : H.radical = IsLocalRing.maximalIdeal D) (a : ℝ≥0∞),
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (B ⧸ (H.map (powerMap p B e he)).map (iterateFrobenius B p n))).toENNReal)
        atTop (𝓝 a) →
      Tendsto (fun n : ℕ => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length D (D ⧸ H.map (iterateFrobenius D p n))).toENNReal)
        atTop (𝓝 (((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ * ((r : ℝ≥0∞)*a))) := by
  obtain ⟨r,hr,h⟩ := Lech.finite_module_asymptoticENN B D (by
    intro g hg hz
    have hc := LinearMap.congr_fun hz (1 : D)
    change (g : D) * 1 = 0 at hc
    simp only [mul_one] at hc
    exact hg (Subtype.val_injective hc))
  refine ⟨r,hr,?_⟩
  intro e he hres H hH a ha
  let G := H.map (powerMap p B e he)
  have hG : G.radical = IsLocalRing.maximalIdeal B := map_radical_primary p B e he H hH
  have ht := h (fun n => G.map (iterateFrobenius B p n))
    (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹) a ?_ ha ?_
  · have hp0 : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hwfin : ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (pow_ne_zero _ hp0)
    have ht' := ENNReal.Tendsto.const_mul (a := ((p : ℝ≥0∞)^(e*Lech.dimension B))⁻¹)
      ht (Or.inr hwfin)
    apply (tendsto_add_atTop_iff_nat e).mp
    apply ht'.congr
    intro n
    rw [quotient_length_eq B _ hres,map_frobenius_ideal p B e he]
    rw [Nat.add_comm n e,Nat.add_mul,pow_add,
      ENNReal.mul_inv (Or.inl (pow_ne_zero _ hp0)) (Or.inl (by simp)),mul_assoc]
  · apply Filter.Eventually.of_forall
    intro n
    obtain ⟨c,hc⟩ := Lech.FrobeniusGrowth.linear_power_containment G hG
    have hl := Lech.length_quotient_le B
      (hc (p^n) (Nat.one_le_pow n p (Fact.out : p.Prime).pos))
    rw [Lech.FrobeniusGrowth.powerIdeal_eq_map G p n] at hl
    exact ne_top_of_le_ne_top (Lech.quotient_length_ne_top B _) hl
  · intro g hg
    exact Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal G hG
      (mem_nonZeroDivisors_iff_ne_zero.mpr hg) p
end Lech.FrobeniusIntermediate


namespace Lech.SeparableOrder
variable (A D K L : Type*) [CommRing A] [CommRing D] [IsDomain D]
  [Field K] [Field L] [Algebra A D] [Algebra A K] [Algebra A L]
  [Algebra K L] [Algebra D L] [IsScalarTower A K L] [IsScalarTower A D L]

 

def order : Subalgebra A D :=
  ((separableClosure K L).toSubalgebra.restrictScalars A).comap
    (IsScalarTower.toAlgHom A D L)

omit [IsDomain D] in
lemma mem_order (x : D) : x ∈ order A D K L ↔ IsSeparable K (algebraMap D L x) := Iff.rfl

instance orderFinite [IsNoetherianRing A] [Module.Finite A D] :
    Module.Finite A (order A D K L) := by
  change Module.Finite A (order A D K L).toSubmodule
  infer_instance

 
def toField : order A D K L →ₐ[A] separableClosure K L where
  toFun x := ⟨algebraMap D L x, x.2⟩
  map_one' := by apply Subtype.ext; exact map_one _
  map_zero' := by apply Subtype.ext; exact map_zero _
  map_mul' x y := by apply Subtype.ext; exact map_mul _ _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  commutes' a := by
    apply Subtype.ext
    exact (IsScalarTower.algebraMap_apply A D L a).symm

omit [IsDomain D] in
lemma toField_injective [IsFractionRing D L] : Function.Injective (toField A D K L) := by
  intro x y h
  apply Subtype.ext
  exact IsFractionRing.injective D L (congrArg Subtype.val h)

instance orderFieldAlgebra : Algebra (order A D K L) (separableClosure K L) :=
  (toField A D K L).toRingHom.toAlgebra

instance orderFieldTower : IsScalarTower A (order A D K L) (separableClosure K L) :=
  IsScalarTower.of_algebraMap_eq' (toField A D K L).comp_algebraMap.symm

instance orderFieldAmbientTower :
    IsScalarTower (order A D K L) (separableClosure K L) L :=
  IsScalarTower.of_algebraMap_eq' rfl

instance orderFieldFaithful [IsFractionRing D L] :
    FaithfulSMul (order A D K L) (separableClosure K L) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (toField_injective A D K L)

 
lemma order_inherits_units [IsFractionRing D L] {x : D} (hx : x ∈ order A D K L)
    (hu : IsUnit x) : IsUnit (⟨x,hx⟩ : order A D K L) := by
  obtain ⟨u,rfl⟩ := hu
  have hm : (↑(u⁻¹) : D) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (↑(u⁻¹) : D))
    have hi : algebraMap D L (↑(u⁻¹) : D) = (algebraMap D L (↑u : D))⁻¹ := by
      apply mul_left_cancel₀ (show algebraMap D L (↑u : D) ≠ 0 from
        (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u))
      rw [← map_mul, Units.mul_inv, map_one, mul_inv_cancel₀]
      exact (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr (Units.ne_zero u)
    rw [hi]
    exact Field.isSeparable_inv hx
  exact ⟨⟨⟨↑u,hx⟩,⟨↑(u⁻¹),hm⟩,by ext; exact Units.mul_inv u,
      by ext; exact Units.inv_mul u⟩,rfl⟩

instance orderLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalRing (order A D K L) :=
  (order A D K L).toSubring.isLocalRing_of_unit (fun _ hx hu =>
    order_inherits_units A D K L hx hu)

instance orderInclusionLocal [IsFractionRing D L] [IsLocalRing D] :
    IsLocalHom (algebraMap (order A D K L) D) :=
  ⟨fun x hu => order_inherits_units A D K L x.2 hu⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] [FiniteDimensional K L]

omit [IsDomain D] in
 

lemma uniform_power : ∃ n : ℕ, ∀ x : D, x^(p^n) ∈ order A D K L := by
  let E := separableClosure K L
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsPurelyInseparable E L := separableClosure.isPurelyInseparable K L
  let : CharP E p := (Algebra.charP_iff K E p).mp inferInstance
  refine ⟨IsPurelyInseparable.exponent E L,fun x => ?_⟩
  change IsSeparable K (algebraMap D L (x^_))
  rw [map_pow]
  obtain ⟨y,hy⟩ := IsPurelyInseparable.exponent_def' E p (algebraMap D L x)
  rw [← hy]
  exact y.2

 

instance orderFraction [IsFractionRing D L] :
    IsFractionRing (order A D K L) (separableClosure K L) := by
  obtain ⟨n,hn⟩ := uniform_power A D K L p
  have hq : 0 < p^n := pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,hb,hab⟩ := IsFractionRing.div_surjective D (z : L)
  have hb0 : algebraMap D L b ≠ 0 :=
    (map_ne_zero_iff (algebraMap D L) (IsFractionRing.injective D L)).mpr
      (nonZeroDivisors.coe_ne_zero ⟨b,hb⟩)
  have hid : algebraMap D L (a*b^(p^n-1)) = (z : L) * algebraMap D L (b^(p^n)) := by
    rw [← hab, map_mul, map_pow, map_pow]
    rw [← Nat.sub_add_cancel hq, pow_succ]
    field_simp
    simp only [Nat.sub_add_cancel hq]
  have ha : a*b^(p^n-1) ∈ order A D K L := by
    change IsSeparable K (algebraMap D L (a*b^(p^n-1)))
    rw [hid]
    exact Field.isSeparable_mul z.2 (hn b)
  refine ⟨⟨a*b^(p^n-1),ha⟩, ⟨b^(p^n),hn b⟩, ?_⟩
  apply Subtype.ext
  change (z : L) = algebraMap D L (a*b^(p^n-1)) / algebraMap D L (b^(p^n))
  rw [hid, mul_div_cancel_right₀]
  rw [map_pow]
  exact pow_ne_zero _ hb0

end Lech.SeparableOrder


namespace Lech
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
lemma length_eq_of_semilinearEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (E : LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) M N) :
    Module.length R M = Module.length S N := by
  apply WithBot.coe_injective
  rw [Module.coe_length,Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective E.toLinearMap E.bijective)

lemma length_span_eq_of_semilinearEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (E : LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) M N) (s : Finset M) :
    Module.length R (Submodule.span R (s : Set M)) =
      Module.length S (Submodule.span S ((s.image E : Finset N) : Set N)) := by
  classical
  exact length_eq_of_semilinearEquiv e
    (E.ofSubmodules _ _ (by rw [Submodule.map_span]; simp only [Finset.coe_image]; rfl))
end Lech


namespace Lech.NormalizedLength.Tower
open scoped ENNReal Classical
variable {L : Type*} [CommRing L] (T : Tower L)
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]

lemma finiteLength_eq_iInf_shift (s : Finset M) (d : ℕ) :
    T.finiteLength s = ⨅ n, T.stage s (n+d) := by
  apply le_antisymm
  · exact le_iInf fun n => T.finiteLength_le_stage s (n+d)
  · apply le_iInf
    intro n
    exact (iInf_le _ n).trans (T.stage_antitone s (Nat.le_add_right n d))

 

lemma length_eq_mul_of_stage_shift (E : M ≃ N) (d : ℕ) (c : ℝ≥0∞)
    (hc : c ≠ ⊤)
    (h : ∀ (s : Finset M) (n : ℕ), T.stage (s.image E) (n+d) = c * T.stage s n) :
    T.length N = c * T.length M := by
  have hf (s : Finset M) : T.finiteLength (s.image E) = c * T.finiteLength s := by
    rw [T.finiteLength_eq_iInf_shift _ d]
    simp_rw [h]
    exact (ENNReal.mul_iInf (fun hh => (hc hh).elim)).symm
  apply le_antisymm
  · apply iSup_le
    intro t
    have he : (t.image E.symm).image E = t := by simp only [Finset.image_image]; simp
    rw [← he,hf]
    exact mul_le_mul_right (T.finiteLength_le_length (t.image E.symm)) c
  · rw [length,ENNReal.mul_iSup]
    exact iSup_le fun s => (hf s).symm ▸ T.finiteLength_le_length (s.image E)
end Lech.NormalizedLength.Tower


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable (A : Type*) [CommRing A] [IsReduced A] (p : ℕ) [Fact p.Prime] [CharP A p]

lemma rootMap_shift (n d : ℕ) (a : A) :
    rootMap A p (n+d) a =
      (iterateFrobeniusEquiv (PerfectClosure A p) p d).symm (rootMap A p n a) := by
  apply (iterateFrobeniusEquiv (PerfectClosure A p) p d).injective
  rw [RingEquiv.apply_symm_apply,iterateFrobeniusEquiv_def,← map_pow]
  have ht := rootMap_transition A p n (n+d) (Nat.le_add_right n d) a
  simpa only [Nat.add_sub_cancel_left,iterateFrobenius_def] using ht

noncomputable def rootShiftEquiv (n d : ℕ) : rootRing A p n ≃+* rootRing A p (n+d) :=
  (rootEquiv A p n).symm.trans (rootEquiv A p (n+d))

lemma rootShiftEquiv_val (n d : ℕ) (x : rootRing A p n) :
    (rootShiftEquiv A p n d x : PerfectClosure A p) =
      (iterateFrobeniusEquiv (PerfectClosure A p) p d).symm (x : PerfectClosure A p) := by
  obtain ⟨a,rfl⟩ := (rootEquiv A p n).surjective x
  change rootMap A p (n+d) ((rootEquiv A p n).symm (rootEquiv A p n a)) = _
  rw [RingEquiv.symm_apply_apply,rootMap_shift,rootEquiv_apply]

variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (PerfectClosure A p) M] [Module (PerfectClosure A p) N]
noncomputable def restrictRootShift (d : ℕ)
    (E : LinearEquiv (σ' := ((iterateFrobeniusEquiv (PerfectClosure A p) p d) : PerfectClosure A p →+* PerfectClosure A p))
      ((iterateFrobeniusEquiv (PerfectClosure A p) p d).symm : PerfectClosure A p →+* PerfectClosure A p) M N) (n : ℕ) :
    LinearEquiv (σ' := ((rootShiftEquiv A p n d).symm : rootRing A p (n+d) →+* rootRing A p n))
      (rootShiftEquiv A p n d : rootRing A p n →+* rootRing A p (n+d)) M N where
  toAddEquiv := E.toAddEquiv
  map_smul' a x := by
    change E ((a : PerfectClosure A p) • x) =
      (rootShiftEquiv A p n d a : PerfectClosure A p) • E x
    rw [E.map_smulₛₗ,rootShiftEquiv_val]
    rfl

end Lech.RootTower


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (PerfectClosure (MvPowerSeries σ k) p) M]
  [Module (PerfectClosure (MvPowerSeries σ k) p) N]

lemma regular_weight_shift (n d : ℕ) :
    (regularTower σ k p).weight (n+d) =
      ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * (regularTower σ k p).weight n := by
  change ((p : ℝ≥0∞)^((n+d)*Fintype.card σ))⁻¹ = _ * ((p : ℝ≥0∞)^(n*Fintype.card σ))⁻¹
  have hz : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Nat.add_mul,pow_add,ENNReal.mul_inv (Or.inl (pow_ne_zero _ hz)) (Or.inl (by simp))]
  exact mul_comm _ _

 

theorem normalizedLength_root_equiv (d : ℕ)
    (E : LinearEquiv (σ' := ((iterateFrobeniusEquiv (PerfectClosure (MvPowerSeries σ k) p) p d) : PerfectClosure (MvPowerSeries σ k) p →+* PerfectClosure (MvPowerSeries σ k) p))
      ((iterateFrobeniusEquiv (PerfectClosure (MvPowerSeries σ k) p) p d).symm : PerfectClosure (MvPowerSeries σ k) p →+* PerfectClosure (MvPowerSeries σ k) p) M N) :
    normalizedLength σ k p N = ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * normalizedLength σ k p M := by
  apply (regularTower σ k p).length_eq_mul_of_stage_shift E.toEquiv d
  · apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  · intro s n
    unfold Lech.NormalizedLength.Tower.stage
    rw [regular_weight_shift]
    rw [mul_assoc]
    congr 1
    congr 1
    exact congrArg ENat.toENNReal (Lech.length_span_eq_of_semilinearEquiv
      (rootShiftEquiv (MvPowerSeries σ k) p n d)
      (restrictRootShift (MvPowerSeries σ k) p d E n) s).symm
end Lech.RootTower


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable {P C : Type*} [CommRing P] [CommRing C] [Algebra P C]
  (p : ℕ) [Fact p.Prime] [CharP P p] [CharP C p] [PerfectRing P p] [PerfectRing C p]

omit [Algebra P C] in
lemma map_inverse_frobenius (f : P →+* C) (d : ℕ) (x : P) :
    f ((iterateFrobeniusEquiv P p d).symm x) =
      (iterateFrobeniusEquiv C p d).symm (f x) := by
  apply (iterateFrobeniusEquiv C p d).injective
  rw [RingEquiv.apply_symm_apply,iterateFrobeniusEquiv_def,← map_pow]
  change f (iterateFrobeniusEquiv P p d ((iterateFrobeniusEquiv P p d).symm x)) = _
  rw [RingEquiv.apply_symm_apply]

noncomputable def quotientRootEquiv (d : ℕ) (I : Ideal C) :
    LinearEquiv (σ' := (iterateFrobeniusEquiv P p d : P →+* P))
      ((iterateFrobeniusEquiv P p d).symm : P →+* P)
      (C ⧸ I) (C ⧸ I.map (iterateFrobeniusEquiv C p d).symm) where
  toAddEquiv := (Ideal.quotientEquiv I _ (iterateFrobeniusEquiv C p d).symm rfl).toAddEquiv
  map_smul' a x := by
    obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective x
    change (Ideal.quotientEquiv I _ (iterateFrobeniusEquiv C p d).symm rfl)
      (a • Ideal.Quotient.mk I x) = _ •
        (Ideal.quotientEquiv I _ (iterateFrobeniusEquiv C p d).symm rfl) (Ideal.Quotient.mk I x)
    have hm (J : Ideal C) (a : P) (x : C) :
        a • Ideal.Quotient.mk J x = Ideal.Quotient.mk J (algebraMap P C a * x) := by
      rw [Algebra.smul_def,IsScalarTower.algebraMap_apply P C (C ⧸ J),map_mul]
      rfl
    have he : (iterateFrobeniusEquiv C p d).symm (algebraMap P C a * x) =
        algebraMap P C ((iterateFrobeniusEquiv P p d).symm a) *
          (iterateFrobeniusEquiv C p d).symm x := by
      rw [map_mul, ← map_inverse_frobenius]
    rw [hm, Ideal.quotientEquiv_mk, Ideal.quotientEquiv_mk]
    exact (congrArg (Ideal.Quotient.mk (I.map (iterateFrobeniusEquiv C p d).symm)) he).trans
      (hm (I.map (iterateFrobeniusEquiv C p d).symm)
        ((iterateFrobeniusEquiv P p d).symm a) ((iterateFrobeniusEquiv C p d).symm x)).symm

end Lech.RootTower
end
end

end OAI
