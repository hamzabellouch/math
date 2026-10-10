import OAI.RepresentationTheory.VertexAlgebra.ModuleEnergyMain

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule
open UniformSpace
universe u v
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} {U : A.UnitaryStructure}
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  (M : A.GradingRestrictedModule W)
theorem PolynomialEnergyBound.physical {a : V} (ha : M.PolynomialEnergyBound a) (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ m v,
      ‖M.physicalMode a d m v‖ ≤ C*(1+|(m : ℝ)|)^p*‖(M.energyShift^k) v‖ := by
  obtain ⟨C, hC, p, k, H⟩ := ha
  refine ⟨C*(1+|((d : ℝ)-1)|)^p, by positivity, p, k, ?_⟩
  intro m v
  have Hm := H (m+d-1) v
  simp only [Int.cast_abs] at Hm
  apply Hm.trans
  have he : 1+|((m+(d : ℤ)-1 : ℤ) : ℝ)| ≤ (1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|) := by
    have ht := abs_add_le (m : ℝ) ((d : ℝ)-1)
    have hn := mul_nonneg (abs_nonneg ((d : ℝ)-1)) (abs_nonneg (m : ℝ))
    push_cast
    rw [add_sub_assoc]
    nlinarith
  calc
    _ ≤ C*((1+|((d : ℝ)-1)|)*(1+|(m : ℝ)|))^p*‖(M.energyShift^k) v‖ := by gcongr
    _ = _ := by rw [mul_pow]; ring

 
theorem summable_norm_physicalSmear {a : V} (ha : M.PolynomialEnergyBound a)
    (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : W) :
    Summable (fun m : ℤ => ‖f m • (M.physicalMode a d m v : Completion W)‖) := by
  obtain ⟨C, _, p, k, H⟩ := ha.physical M d
  apply hf.summable_norm_smul
    (fun m => (Completion.toComplₗᵢ : W →ₗᵢ[ℂ] Completion W).toLinearMap.comp (M.physicalMode a d m))
    v (C := C) (K := ‖(M.energyShift^k) v‖) (p := p)
  intro m
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap, LinearIsometry.norm_map] using H m v

 
def smearedMap (a : V) (d : ℕ) (ha : M.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) : W →ₗ[ℂ] Completion W :=
  SummableLinearFamily.tsumMap
    (fun m => f m • (Completion.toComplₗᵢ : W →ₗᵢ[ℂ] Completion W).toLinearMap.comp
      (M.physicalMode a d m))
    (fun v => (M.summable_norm_physicalSmear ha d hf v).of_norm)

@[simp] theorem smearedMap_apply (a : V) (d : ℕ) (ha : M.PolynomialEnergyBound a)
    (f : ℤ → ℂ) (hf : RapidCoefficients f) (v : W) :
    M.smearedMap a d ha f hf v = ∑' m : ℤ, f m • (M.physicalMode a d m v : Completion W) := rfl

namespace UnitaryStructure
variable {M} (R : M.UnitaryStructure U)
include R
 

theorem summable_adjointPhysicalSmear (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : W) :
    Summable (fun m : ℤ => star (f m) • (R.adjointPhysicalMode a d m v : Completion W)) := by
  have hs (j : ℕ) : Summable (fun m : ℤ =>
      star (f m) • (M.physicalMode ((A.virasoroMode 1^j) (U.pct a)) (d-j) (-m) v : Completion W)) := by
    have h := (M.summable_norm_physicalSmear
      (R.polynomialEnergyBounds hc ((A.virasoroMode 1^j) (U.pct a))) (d-j)
      hf.conj.neg_index v).of_norm
    simpa only [Function.comp_def, Equiv.neg_apply, neg_neg] using
      (Equiv.neg ℤ).summable_iff.mpr h
  have hs' (j : ℕ) := (hs j).const_smul ((-1 : ℂ)^d * (j.factorial : ℂ)⁻¹)
  have H := summable_sum (s := Finset.range (d+1)) (fun j _ => hs' j)
  convert H using 1
  ext m
  change star (f m) • (Completion.toComplₗᵢ : W →ₗᵢ[ℂ] Completion W) (R.adjointPhysicalMode a d m v) = _
  simp only [adjointPhysicalMode, LinearMap.smul_apply, LinearMap.sum_apply,
    map_smul, map_sum, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  ring

 
theorem smearedCore_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (HilbertCore.operator (M.smearedMap a d (R.polynomialEnergyBounds hc a) f hf)).IsClosable := by
  let j : W →ₗ[ℂ] Completion W := (Completion.toComplₗᵢ : W →ₗᵢ[ℂ] Completion W).toLinearMap
  let T (m : ℤ) : W →ₗ[ℂ] Completion W := f m • j.comp (M.physicalMode a d m)
  let S (m : ℤ) : W →ₗ[ℂ] Completion W := star (f m) • j.comp (R.adjointPhysicalMode a d m)
  have hT : ∀ v, Summable (fun m => T m v) := fun v =>
    (M.summable_norm_physicalSmear (R.polynomialEnergyBounds hc a) d hf v).of_norm
  have hS : ∀ v, Summable (fun m => S m v) := fun v => R.summable_adjointPhysicalSmear hc a d hf v
  have Hadj (m : ℤ) (x y : W) : inner ℂ (T m x) (j y) = inner ℂ (j x) (S m y) := by
    change inner ℂ (f m • (M.physicalMode a d m x : Completion W)) (y : Completion W) =
      inner ℂ (x : Completion W) (star (f m) • (R.adjointPhysicalMode a d m y : Completion W))
    simp only [inner_smul_left, inner_smul_right, Completion.inner_coe]
    rw [R.adjointPhysicalMode_inner ha]
    rfl
  exact HilbertCore.closable (SummableLinearFamily.adjoint_tsum hT hS j Hadj)

 

def closedSmearedOperator (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : ℤ → ℂ) (hf : RapidCoefficients f) :
    Completion W →ₗ.[ℂ] Completion W :=
  (HilbertCore.operator (M.smearedMap a d (R.polynomialEnergyBounds hc a) f hf)).closure

theorem closedSmearedOperator_isClosed (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (R.closedSmearedOperator hc a d f hf).IsClosed :=
  (R.smearedCore_closable hc ha hf).closure_isClosed

 

def smoothSmearedField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion W →ₗ.[ℂ] Completion W :=
  HilbertCore.operator (M.smearedMap a d (R.polynomialEnergyBounds hc a)
    f.coefficient f.rapid_coefficients)

theorem smoothSmearedField_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (R.smoothSmearedField hc a d f).IsClosable :=
  R.smearedCore_closable hc ha f.rapid_coefficients

 
def closedSmoothField (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) : Completion W →ₗ.[ℂ] Completion W :=
  (R.smoothSmearedField hc a d f).closure

theorem closedSmoothField_isClosed (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) :
    (R.closedSmoothField hc a d f).IsClosed :=
  (R.smoothSmearedField_closable hc ha f).closure_isClosed

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA.GradingRestrictedModule

end

end OAI
