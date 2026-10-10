import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.StressCutoffNormalized

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
open MeasureTheory Set
open MeasureTheory Set Filter
open scoped Topology Interval
open Set Filter
open UniformSpace Set
open UniformSpace Filter
open UniformSpace Filter Set
open UniformSpace Filter Set MeasureTheory
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressCutoff_normalized_limit (hc : A.toVertexAlgebra.C2Cofinite) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    Tendsto (fun n => U.stressCutoff hc n hf*U.inverseSobolev 2) atTop
      (𝓝 (Complex.I • U.stressNormalized hc hf 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n => U.stressCutoff_error hc n hf)
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  simpa only [one_div,add_comm,zero_mul] using
    h.mul_const ((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re))

 def stressPropagatorDerivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) : Completion V :=
  Complex.I • U.stressNormalized hc (f.rapid t) 2
    (U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x))

lemma stressPropagatorDerivative_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (x : U.smoothEnergySpace) : Continuous (fun t => U.stressPropagatorDerivative hc f t x) := by
  exact (continuous_const (y := Complex.I)).smul ((U.stressNormalized_continuous hc f.rapid f.continuous
    (by norm_num : 1 ≤ 2)).clm_apply (U.stressPropagatorSmooth_continuous_power hc f 2 x))

lemma stressCutoff_derivative_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) atTop
      (𝓝 (U.stressPropagatorDerivative hc f t x)) := by
  have h := (isBoundedBilinearMap_apply (𝕜 := ℂ)).continuous.tendsto
    (Complex.I • U.stressNormalized hc (f.rapid t) 2,
      U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x)) |>.comp
      ((U.stressCutoff_normalized_limit hc (f.rapid t)).prodMk_nhds
        (U.stressCutoffEvolutionSmooth_limit hc f 2 t x))
  convert h using 1
  · ext n
    change _ = U.stressCutoff hc n (f.rapid t)
      (U.inverseSobolev 2 (U.smoothEnergyPower 2 (U.stressCutoffEvolutionSmooth hc f n t x)))
    rw [U.inverseSobolev_smoothEnergyPower]
    rfl
  · rfl

lemma stressCutoff_evolution_derivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) (x : Completion V) :
    HasDerivAt (fun s => TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) s x)
      (U.stressCutoff hc n (f.rapid t)
        (TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x)) t := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  exact TimeOrdered.evolution_apply_derivative (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) t x

lemma stressCutoff_evolution_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (x : Completion V) :
    Continuous (fun t => TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x) :=
  continuous_iff_continuousAt.mpr (fun t => (U.stressCutoff_evolution_derivative hc f n t x).continuousAt)

lemma stressCutoff_integral_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (a b : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => ∫ t in a..b, U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) atTop
      (𝓝 (∫ t in a..b, U.stressPropagatorDerivative hc f t x)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*(|a|+|b|))*
      ‖U.smoothEnergyPower 1 x‖)
  · exact Eventually.of_forall (fun n => ((U.stressCutoff_continuous hc n f.rapid f.continuous).clm_apply
      (U.stressCutoff_evolution_continuous hc f n x)).aestronglyMeasurable)
  · apply Eventually.of_forall
    intro n
    apply Eventually.of_forall
    intro t ht
    have htab := uIoc_subset_uIcc ht
    have hr : |t| ≤ |a|+|b| := by
      rcases le_total a b with hab | hba
      · rw [uIcc_of_le hab] at htab
        exact (abs_le_max_abs_abs htab.1 htab.2).trans (max_le
          (le_add_of_nonneg_right (abs_nonneg b)) (le_add_of_nonneg_left (abs_nonneg a)))
      · rw [uIcc_of_ge hba] at htab
        exact (abs_le_max_abs_abs htab.1 htab.2).trans (max_le
          (le_add_of_nonneg_left (abs_nonneg a)) (le_add_of_nonneg_right (abs_nonneg b)))
    exact U.stressCutoff_derivative_bound hc f n hr x
  · exact intervalIntegrable_const
  · exact Eventually.of_forall (fun t _ => U.stressCutoff_derivative_limit hc f t x)

lemma stressPropagator_integral (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (a b : ℝ) (x : U.smoothEnergySpace) :
    (∫ t in a..b, U.stressPropagatorDerivative hc f t x)=
      U.stressPropagator hc f b x-U.stressPropagator hc f a x := by
  have hi := U.stressCutoff_integral_limit hc f a b x
  have he : ∀ n, (∫ t in a..b, U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)) =
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) b x-
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) a x := by
    intro n
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => U.stressCutoff_evolution_derivative hc f n t x)
      (((U.stressCutoff_continuous hc n f.rapid f.continuous).clm_apply
        (U.stressCutoff_evolution_continuous hc f n x)).intervalIntegrable a b)
  simp_rw [he] at hi
  exact tendsto_nhds_unique hi ((U.stressPropagator_limit hc f b x).sub (U.stressPropagator_limit hc f a x))

 

lemma stressPropagator_derivative (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    HasDerivAt (fun s => U.stressPropagator hc f s x) (U.stressPropagatorDerivative hc f t x) t := by
  have h := U.stressPropagatorDerivative_continuous hc f x
  have hd := intervalIntegral.integral_hasDerivAt_right (h.intervalIntegrable 0 t)
    h.stronglyMeasurable.stronglyMeasurableAtFilter h.continuousAt
  have he : (fun s => U.stressPropagator hc f s x)=
      (fun s => (∫ q in (0:ℝ)..s, U.stressPropagatorDerivative hc f q x)+U.stressPropagator hc f 0 x) := by
    funext s
    rw [U.stressPropagator_integral hc f 0 s x,sub_add_cancel]
  rw [he]
  exact hd.add_const _

lemma stressPropagatorDerivative_graph (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) (x : U.smoothEnergySpace) :
    (U.stressPropagator hc f t x,(-Complex.I) • U.stressPropagatorDerivative hc f t x) ∈
      (U.closedSmearedOperator hc A.conformalVector 2 (f.coefficients t) (f.rapid t)).graph := by
  have hg := U.stressNormalized_graph hc (f.rapid t) (by norm_num : 1 ≤ 2)
    (U.smoothEnergyPower 2 (U.stressPropagatorSmooth hc f t x))
  rw [U.inverseSobolev_smoothEnergyPower] at hg
  simpa only [stressPropagatorDerivative,stressPropagatorSmooth,LinearMap.codRestrict_apply,
    LinearMap.comp_apply,Submodule.subtype_apply,ContinuousLinearMap.coe_coe,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul] using hg
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

lemma form_pairing_derivative (D : Submodule ℂ H) (P : ℝ → D →ₗ[ℂ] H)
    (x y : ℝ → D) (t : ℝ) (dx dy z : H)
    (hs : ∀ a b : D, inner ℂ (P t a) (b : H)=inner ℂ (a : H) (P t b))
    (hx : HasDerivAt (fun s => (x s : H)) dx t)
    (hy : HasDerivAt (fun s => (y s : H)) dy t)
    (hPy : ContinuousAt (fun s => P s (y s)) t)
    (hP : Tendsto (fun s => (s-t)⁻¹ • (P s (y s)-P t (y s))) (𝓝[≠] t) (𝓝 z)) :
    HasDerivAt (fun s => inner ℂ (x s : H) (P s (y s)))
      (inner ℂ dx (P t (y t))+inner ℂ (P t (x t)) dy+inner ℂ (x t : H) z) t := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h := ((hx.tendsto_slope.inner (𝕜 := ℂ) (hPy.mono_left nhdsWithin_le_nhds)).add
    ((tendsto_const_nhds (x := P t (x t))).inner (𝕜 := ℂ) hy.tendsto_slope)).add ((tendsto_const_nhds (x := (x t : H))).inner (𝕜 := ℂ) hP)
  convert h using 1
  ext s
  simp only [slope,vsub_eq_sub,inner_sub_left,inner_sub_right,inner_smul_left_eq_star_smul,
    inner_smul_right_eq_smul,starRingEnd_apply,star_trivial,hs,smul_sub]
  abel
end StronglyRationalVOA.SymmetricOperator

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_smul {a : V} (he : A.PolynomialEnergyBound a) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    A.smearedMap a d he (fun n => c*f n) (hf.smul c)=c • A.smearedMap a d he f hf := by
  ext v
  simp only [smearedMap_apply,LinearMap.smul_apply,mul_smul,tsum_const_smul'']
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma sobolevExtension_smul (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (c : ℂ) :
    U.sobolevExtension r (c • M)=c • U.sobolevExtension r M := by
  have hcM (v : V) : ‖(c • M) v‖ ≤ (‖c‖*C)*‖(A.energyShift^r) v‖ := by
    simpa only [LinearMap.smul_apply,norm_smul,mul_assoc] using mul_le_mul_of_nonneg_left (hM v) (norm_nonneg c)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (c • M) x=(c • U.sobolevExtension r M) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [smul_apply,U.sobolevExtension_coe r _ hcM,
    U.sobolevExtension_coe r _ hM,LinearMap.smul_apply]

lemma sobolevExtension_sub (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) :
    U.sobolevExtension r (M-N)=U.sobolevExtension r M-U.sobolevExtension r N := by
  have hMN (v : V) : ‖(M-N) v‖ ≤ (C+D)*‖(A.energyShift^r) v‖ := by
    exact (norm_sub_le (M v) (N v)).trans ((add_le_add (hM v) (hN v)).trans_eq (add_mul ..).symm)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (M-N) x=(U.sobolevExtension r M-U.sobolevExtension r N) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [sub_apply,U.sobolevExtension_coe r _ hMN,
    U.sobolevExtension_coe r _ hM,U.sobolevExtension_coe r _ hN,LinearMap.sub_apply]

 def normalizedField (hc : A.toVertexAlgebra.C2Cofinite) (a : V) (d k : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) : Completion V →L[ℂ] Completion V :=
  U.sobolevExtension k (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)

lemma normalizedField_norm (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    ‖U.normalizedField hc a d k hf‖ ≤ coefficientSeminorm f p*C := by
  exact U.sobolevExtension_norm k _ (mul_nonneg (coefficientSeminorm_nonneg _ _) hC)
    (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb)

lemma normalizedField_sub (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) :
    U.normalizedField hc a d k (hf.sub hg)=U.normalizedField hc a d k hf-U.normalizedField hc a d k hg := by
  unfold normalizedField
  rw [← A.smearedMap_sub]
  exact U.sobolevExtension_sub k _ _ (A.smearedMap_bound _ hf hb) (A.smearedMap_bound _ hg hb)

lemma normalizedField_smul (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (c : ℂ) :
    U.normalizedField hc a d k (hf.smul c)=c • U.normalizedField hc a d k hf := by
  unfold normalizedField
  rw [A.smearedMap_smul]
  exact U.sobolevExtension_smul k _ (A.smearedMap_bound _ hf hb) c

lemma smoothSmear_eq_normalized (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (x : U.smoothEnergySpace) :
    (U.smoothSmear hc ha hf x : Completion V)=U.normalizedField hc a d k hf (U.smoothEnergyPower k x) :=
  U.smoothSmear_eq_extension hc ha hf (A.smearedMap_bound _ hf hb) x (U.smoothEnergyPower_graph k x)

lemma normalizedField_continuous (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun n => f s n-f t n) p) (𝓝 t) (𝓝 0)) :
    Continuous (fun t => U.normalizedField hc a d k (hf t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun s => (U.normalizedField_sub hc hb (hf s) (hf t)) ▸ U.normalizedField_norm hc hC hb ((hf s).sub (hf t)))
  simpa only [zero_mul] using (hl t).mul_const C

 

lemma normalizedField_derivative (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d p k : ℕ}
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t)) {g : ℤ → ℂ} (hg : RapidCoefficients g)
    (t : ℝ) (hl : Tendsto (fun s => coefficientSeminorm
      (fun n => (((s-t)⁻¹ : ℝ):ℂ)*(f s n-f t n)-g n) p) (𝓝[≠] t) (𝓝 0)) :
    HasDerivAt (fun s => U.normalizedField hc a d k (hf s)) (U.normalizedField hc a d k hg) t := by
  rw [hasDerivAt_iff_tendsto_slope,tendsto_iff_norm_sub_tendsto_zero]
  have he (s : ℝ) : slope (fun q => U.normalizedField hc a d k (hf q)) t s-U.normalizedField hc a d k hg =
      U.normalizedField hc a d k ((((hf s).sub (hf t)).smul (((s-t)⁻¹ : ℝ):ℂ)).sub hg) := by
    rw [U.normalizedField_sub hc hb (((hf s).sub (hf t)).smul (((s-t)⁻¹ : ℝ):ℂ)) hg,
      U.normalizedField_smul hc hb ((hf s).sub (hf t)),U.normalizedField_sub hc hb (hf s) (hf t)]
    simp only [slope]
    rfl
  apply squeeze_zero (fun _ => norm_nonneg _) (fun s => he s ▸ U.normalizedField_norm hc hC hb _)
  simpa only [zero_mul] using hl.mul_const C
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
lemma physicalMode_inner_orthogonal {a x y : V} {d D E : ℕ}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) (n : ℤ)
    (hne : n ≠ (E:ℤ)-D) : inner ℂ x (A.physicalMode a d n y)=0 := by
  have h := U.virasoro_adjoint 0 x (A.physicalMode a d n y)
  simp only [neg_zero,A.virasoro_zero_on_grade hx,A.physicalMode_energy_eigenvalue ha hy,
    inner_smul_left,inner_smul_right,map_natCast] at h
  have hc : (D:ℂ)-((E:ℂ)-n) ≠ 0 := by
    intro hz
    apply hne
    have heq : (n:ℂ)=(E:ℂ)-D := by linear_combination hz
    exact_mod_cast heq
  apply (mul_eq_zero.mp (show ((D:ℂ)-((E:ℂ)-n))*inner ℂ x (A.physicalMode a d n y)=0 from ?_)).resolve_left hc
  rw [sub_mul,h,sub_self]

include U in
lemma inner_smearedMap_homogeneous {a x y : V} {d D E : ℕ}
    (ha : a ∈ A.grade d) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    inner ℂ (x : Completion V) (A.smearedMap a d he f hf y)=
      f ((E:ℤ)-D)*inner ℂ x (A.physicalMode a d ((E:ℤ)-D) y) := by
  rw [smearedMap_apply,inner_tsum_right (A.summable_norm_physicalSmear he d hf y).of_norm]
  simp only [inner_smul_right,Completion.inner_coe]
  exact tsum_eq_single ((E:ℤ)-D) (fun n hn => by rw [U.physicalMode_inner_orthogonal ha hx hy n hn,mul_zero])

 

lemma primary_stress_weakCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hhc : RapidCoefficients h)
    (hfr : ∀ n, star (f n)=f (-n)) (hgr : ∀ n, star (g n)=g (-n))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f m*g (r-m)) (-Complex.I*h r))
    (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf x)
      (A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg y)-
    inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf y)=
    -Complex.I*inner ℂ (x:Completion V) (A.smearedMap a d (U.polynomialEnergyBounds hc a) h hhc y) := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  let M := A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector) f hf
  let N := A.smearedMap a d (U.polynomialEnergyBounds hc a) g hg
  let Q := A.smearedMap a d (U.polynomialEnergyBounds hc a) h hhc
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (M x) (N y)-inner ℂ (N x) (M y) = -Complex.I*inner ℂ (x:Completion V) (Q y) := by
    let r : ℤ := (E:ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous A.conformal_mem ha hx hy
      A.conformal_quasiPrimary hν (U.polynomialEnergyBounds hc A.conformalVector)
      (U.polynomialEnergyBounds hc a) hf hg hfr
    have H2 := U.hasSum_smeared_inner_homogeneous ha A.conformal_mem hx hy
      (hp 1 (by norm_num)) hh (U.polynomialEnergyBounds hc a)
      (U.polynomialEnergyBounds hc A.conformalVector) hg hf hgr
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have Hdiff := H1.sub (R.hasSum_iff.mpr H2)
    have Hz := (hconv r).mul_right (inner ℂ x (A.physicalMode a d r y))
    have He : HasSum (fun m : ℤ => f m*g (r-m)*inner ℂ x
        (A.virasoroMode m (A.physicalMode a d (r-m) y)-
          A.physicalMode a d (r-m) (A.virasoroMode m y)))
        (-Complex.I*inner ℂ (x:Completion V) (Q y)) := by
      rw [U.inner_smearedMap_homogeneous ha hx hy]
      rw [mul_assoc] at Hz
      apply Hz.congr_fun
      intro m
      rw [A.virasoro_primary_physical_commutator ha hp,inner_smul_right,
        show m+(r-m)=r by omega]
      push_cast
      ring
    apply Hdiff.unique
    convert He using 1
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E:ℤ)-D-(r-m)=m by dsimp [r]; omega]
    rw [show A.physicalMode A.conformalVector 2 m=A.virasoroMode m by
      unfold physicalMode virasoroMode; congr 1; omega]
    simp only [inner_sub_right]
    ring
  change inner ℂ (M x) (N y)-inner ℂ (N x) (M y) = -Complex.I*inner ℂ (x:Completion V) (Q y)
  apply A.homogeneous_induction (P := fun x => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
    -Complex.I*inner ℂ (x:Completion V) (Q y))
  · simp only [map_zero,inner_zero_left,sub_self,Completion.coe_zero,mul_zero]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y => inner ℂ (M x) (N y)-inner ℂ (N x) (M y) =
      -Complex.I*inner ℂ (x:Completion V) (Q y))
    · simp
    · intro E y hy; exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right]
      linear_combination hy+hz
  · intro x z hx hz
    simp only [map_add,inner_add_left,Completion.coe_add]
    linear_combination hx+hz

 

lemma sobolevExtension_weakCommutator (r : ℕ) (M N Q : V →ₗ[ℂ] Completion V) {C D E : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hQ : ∀ v, ‖Q v‖ ≤ E*‖(A.energyShift^r) v‖) (c : ℂ)
    (hw : ∀ x y, inner ℂ (M x) (N y)-inner ℂ (N x) (M y)=c*inner ℂ (x:Completion V) (Q y))
    (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y)-
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y)=
      c*inner ℂ (U.inverseSobolev r x) (U.sobolevExtension r Q y) := by
  have hd : DenseRange (fun v : V => (v:Completion V)) := Completion.denseRange_coe
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      ((((U.sobolevExtension r M).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r N).continuous.comp continuous_snd)).sub
        (((U.sobolevExtension r N).continuous.comp continuous_fst).inner
          ((U.sobolevExtension r M).continuous.comp continuous_snd)))
      (continuous_const.mul (((U.inverseSobolev r).continuous.comp continuous_fst).inner
        ((U.sobolevExtension r Q).continuous.comp continuous_snd)))
  · intro v w
    simpa only [U.sobolevExtension_coe r M hM,U.sobolevExtension_coe r N hN,
      U.sobolevExtension_coe r Q hQ,← U.inverseCoreEnergy_coe] using
        hw (U.inverseCoreEnergy r v) (U.inverseCoreEnergy r w)

lemma smoothSmear_weakCommutator_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite)
    {a b c : V} {d e j : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e) (hcj : c ∈ A.grade j)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hh : RapidCoefficients h)
    (z : ℂ)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg y)-
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf y)=
      z*inner ℂ (x:Completion V) (A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh y))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (U.smoothSmear hc hb hg y : Completion V)-
      inner ℂ (U.smoothSmear hc hb hg x : Completion V) (U.smoothSmear hc ha hf y : Completion V)=
      z*inner ℂ (x:Completion V) (U.smoothSmear hc hcj hh y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  obtain ⟨E,hE,o,m,hQ⟩ := (U.polynomialEnergyBounds hc c).physical A j
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g hg
  let Q := A.smearedMap c j (U.polynomialEnergyBounds hc c) h hh
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm g q*D)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hg hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hq (v : V) : ‖Q v‖ ≤ (coefficientSeminorm h o*E)*‖(A.energyShift^(k+l+m)) v‖ :=
    (A.smearedMap_bound _ hh hQ v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : m ≤ k+l+m) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hE.le))
  rw [U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc hb hg hn y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hb hg hn x (U.smoothEnergyPower_graph (k+l+m) x),
    U.smoothSmear_eq_extension hc ha hf hm y (U.smoothEnergyPower_graph (k+l+m) y),
    U.smoothSmear_eq_extension hc hcj hh hq y (U.smoothEnergyPower_graph (k+l+m) y),
    U.sobolevExtension_weakCommutator (k+l+m) M N Q hm hn hq z hweak,
    U.inverseSobolev_smoothEnergyPower]

lemma primary_stress_smoothCommutator (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hh : U.IsHermitian d a)
    {f g h : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (hhc : RapidCoefficients h)
    (hfr : ∀ n, star (f n)=f (-n)) (hgr : ∀ n, star (g n)=g (-n))
    (hconv : ∀ r : ℤ, HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f m*g (r-m)) (-Complex.I*h r))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc A.conformal_mem hf x : Completion V)
      (U.smoothSmear hc ha hg y : Completion V)-
    inner ℂ (U.smoothSmear hc ha hg x : Completion V)
      (U.smoothSmear hc A.conformal_mem hf y : Completion V)=
    -Complex.I*inner ℂ (x:Completion V) (U.smoothSmear hc ha hhc y : Completion V) :=
  U.smoothSmear_weakCommutator_of_algebraic hc A.conformal_mem ha ha hf hg hhc (-Complex.I)
    (U.primary_stress_weakCommutator hc ha hp hh hf hg hhc hfr hgr hconv) x y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

def add (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ⟨fun t => f t+g t,fun t => by dsimp only; rw [f.periodic,g.periodic],f.smooth.add g.smooth⟩
def scale (f : SmoothCircleFunction) (c : ℂ) : SmoothCircleFunction :=
  ⟨fun t => c*f t,fun t => by dsimp only; rw [f.periodic],contDiff_const.mul f.smooth⟩
@[simp] lemma add_apply (f g : SmoothCircleFunction) (t : ℝ) : f.add g t=f t+g t := rfl
@[simp] lemma scale_apply (f : SmoothCircleFunction) (c : ℂ) (t : ℝ) : f.scale c t=c*f t := rfl
lemma coefficient_add (f g : SmoothCircleFunction) (n : ℤ) :
    (f.add g).coefficient n=f.coefficient n+g.coefficient n := by
  have he : (f.add g).toContinuousMap=f.toContinuousMap+g.toContinuousMap := by
    ext t
    induction t using QuotientAddGroup.induction_on
    rfl
  rw [← fourierCoeff_toContinuousMap,he]
  change fourierCoeff ((f.toContinuousMap : AddCircle (2*Real.pi) → ℂ)+(g.toContinuousMap : AddCircle (2*Real.pi) → ℂ)) n=_
  rw [fourierCoeff.add (f.toContinuousMap.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (g.toContinuousMap.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  simp only [Pi.add_apply,fourierCoeff_toContinuousMap]
lemma coefficient_scale (f : SmoothCircleFunction) (c : ℂ) (n : ℤ) :
    (f.scale c).coefficient n=c*f.coefficient n := by
  exact fourierCoeffOn.const_mul f c n period_pos

 

def primaryTransport (f g : SmoothCircleFunction) (d : ℕ) : SmoothCircleFunction :=
  (((f.differentiated 1).mul g).scale ((d:ℂ)-1)).add
    ((f.mul (g.differentiated 1)).scale (-1))
lemma primaryTransport_apply (f g : SmoothCircleFunction) (d : ℕ) (t : ℝ) :
    f.primaryTransport g d t=((d:ℂ)-1)*deriv f t*g t-f t*deriv g t := by
  simp only [primaryTransport,add_apply,scale_apply,mul_apply,differentiated_apply,iteratedDeriv_one]
  ring

lemma hasSum_primaryTransport (f g : SmoothCircleFunction) (d : ℕ) (r : ℤ) :
    HasSum (fun m : ℤ => (((d:ℂ)-1)*m-(r-m))*f.coefficient m*g.coefficient (r-m))
      (-Complex.I*(f.primaryTransport g d).coefficient r) := by
  have h1 := ((f.differentiated 1).coefficient_mul g r).mul_left ((d:ℂ)-1)
  have h2 := f.coefficient_mul (g.differentiated 1) r
  have h := (h1.sub h2).mul_left (-Complex.I)
  rw [primaryTransport,coefficient_add,coefficient_scale,coefficient_scale]
  rw [show ((d:ℂ)-1)*((f.differentiated 1).mul g).coefficient r +
    (-1)*(f.mul (g.differentiated 1)).coefficient r =
    ((d:ℂ)-1)*((f.differentiated 1).mul g).coefficient r -
    (f.mul (g.differentiated 1)).coefficient r by ring]
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,pow_one]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
