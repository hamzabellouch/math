import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.ApproximatingFlowDerivative
import OAI.RepresentationTheory.VertexAlgebra.CoefficientDifferentiated

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma regularizer_factor_add (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hSi : Function.Injective S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    (s t : ℝ) : B (s+t) = B s * B t := by
  have he (r : ℝ) (v : H) : S (B r v) = flow T hs r (S v) :=
    (congrArg (fun Q : H →L[ℂ] H => Q v) (hB r)).symm
  ext x
  apply hSi
  rw [he,mul_apply_eq_comp,he,he,flow_add,mul_apply_eq_comp]

lemma regularizer_factor_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|)) (x : H) :
    Continuous (fun t => B t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  have h := (B s).continuous.tendsto x |>.comp
    ((regularizer_factor_continuous_zero T hs S hS hSd B hB hK hb x).comp
      (by simpa only [sub_self] using ((tendsto_id : Tendsto (fun t : ℝ => t) (𝓝 s) (𝓝 s)).sub_const s)))
  change Tendsto (fun t : ℝ => B t x) (𝓝 s) (𝓝 (B s x))
  change Tendsto (fun t : ℝ => B s (B (t-s) x)) _ _ at h
  have he (t : ℝ) : s+(t-s)=t := by ring
  simpa only [← mul_apply_eq_comp,← regularizer_factor_add T hs S
    (selfAdjoint_injective_of_denseRange S hS hSd) B hB,he] using h

lemma regularizer_factor_integral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y : H} (hxy : (S x,S y) ∈ T.graph) (t : ℝ) :
    (∫ s in 0..t, B s (Complex.I • y)) = B t x-x := by
  apply selfAdjoint_injective_of_denseRange S hS hSd
  have he (r : ℝ) (v : H) : S (B r v) = flow T hs r (S v) :=
    (congrArg (fun Q : H →L[ℂ] H => Q v) (hB r)).symm
  rw [← S.intervalIntegral_comp_comm ((regularizer_factor_continuous T hs S hS hSd B hB hK hb _).intervalIntegrable 0 t),
    map_sub,he]
  simp_rw [he,map_smul]
  simpa only [map_smul] using flow_integral T hs hxy t

lemma regularizer_factor_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y : H} (hxy : (S x,S y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s => B s x) (B t (Complex.I • y)) t := by
  have hc := regularizer_factor_continuous T hs S hS hSd B hB hK hb (Complex.I • y)
  have he : (fun s : ℝ => B s x) = (fun s : ℝ => x+∫ r in 0..s, B r (Complex.I • y)) := by
    funext s
    rw [regularizer_factor_integral T hs S hS hSd B hB hK hb hxy s]
    abel
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt).const_add x

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance regularizerFactorGradeFiniteDimensional :
    ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

 
def inverseSobolev (r : ℕ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.conjStarAlgEquiv
    (HilbertScale.inverseEnergy (fun d : ℕ => (1+(d : ℝ))^r)
      (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)))

lemma inverseSobolev_apply (r : ℕ) (x : Completion V) :
    U.inverseSobolev r x = U.energyCoordinates.symm
      (HilbertScale.inverseEnergy (fun d : ℕ => (1+(d : ℝ))^r)
        (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
        (U.energyCoordinates x)) := rfl

lemma inverseSobolev_selfAdjoint (r : ℕ) : IsSelfAdjoint (U.inverseSobolev r) := by
  have h := HilbertScale.inverseEnergy_selfAdjoint (G := fun d => A.grade d)
    (fun d : ℕ => (1+(d : ℝ))^r)
    (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
  change star (U.inverseSobolev r) = U.inverseSobolev r
  unfold inverseSobolev
  exact (U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _).symm.trans
    (congrArg U.energyCoordinates.symm.conjStarAlgEquiv h)

lemma inverseSobolev_graph (r : ℕ) (x : Completion V) :
    (U.inverseSobolev r x,x) ∈ (U.energyPower r).graph := by
  change (_,_) ∈ (OperatorTransport.transport U.energyCoordinates
    (HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)))).graph
  rw [OperatorTransport.mem_graph_iff,inverseSobolev_apply,U.energyCoordinates.apply_symm_apply]
  exact HilbertScale.inverseEnergy_graph _ _ _

lemma inverseSobolev_on_graph (r : ℕ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) : U.inverseSobolev r y = x := by
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mp hxy
  rw [U.inverseSobolev_apply,HilbertScale.inverseEnergy_on_graph _ _ h,U.energyCoordinates.symm_apply_apply]

lemma inverseSobolev_dense (r : ℕ) : DenseRange (U.inverseSobolev r) := by
  apply (HilbertCore.dense (V := V)).mono
  rintro x ⟨v,rfl⟩
  refine ⟨((A.energyShift^r) v : Completion V),U.inverseSobolev_on_graph r ?_⟩
  exact (U.energyPower r).mem_graph_iff.mpr
    ⟨⟨_,U.coe_mem_energyOperator _ v⟩,rfl,U.energyPower_coe r v⟩

lemma sobolevExtension_eq_conj (r : ℕ) (M : V →ₗ[ℂ] Completion V) :
    U.sobolevExtension r M = U.energyCoordinates.symm.conjStarAlgEquiv
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M)) := by
  ext x
  rfl

lemma sobolevExtension_inverse_graph (r : ℕ) (M : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖) (hc : (HilbertCore.operator M).IsClosable)
    (x : Completion V) :
    (U.inverseSobolev r x,U.sobolevExtension r M x) ∈ (HilbertCore.operator M).closure.graph := by
  obtain ⟨v,hv,hy⟩ := (U.energyPower r).mem_graph_iff.mp (U.inverseSobolev_graph r x)
  dsimp only [Prod.fst,Prod.snd] at hv hy
  have h := U.sobolevExtension_energyGraph r M hM hc v
  rwa [hv,hy] at h

lemma sobolevExtension_defect (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V)) :
    U.sobolevExtension r M-(U.sobolevExtension r M).adjoint =
      (U.inverseSobolev r).comp (U.sobolevExtension r K) := by
  have hk' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap M x)
          (HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)) y)-
        inner ℂ (HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^r : ℝ) : ℂ)) x)
          (U.spectralCoreMap M y) = inner ℂ (U.spectralCoreMap K x) y := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.coreEnergyCoordinates_energyPower,U.energyCoordinates.inner_map_map] using hk v w
  have hb := HilbertScale.energyExtension_defect
    (fun d : ℕ => (1+(d : ℝ))^r)
    (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
    (U.spectralCoreMap M) (U.spectralCoreMap K)
    (U.spectralCoreMap_bound r M hM) (U.spectralCoreMap_bound r K hK) hk'
  change HilbertScale.energyExtension _ (U.spectralCoreMap M)-
    star (HilbertScale.energyExtension _ (U.spectralCoreMap M)) =
    HilbertScale.inverseEnergy _ _ * HilbertScale.energyExtension _ (U.spectralCoreMap K) at hb
  have h := congrArg U.energyCoordinates.symm.conjStarAlgEquiv hb
  change U.sobolevExtension r M-star (U.sobolevExtension r M) =
    U.inverseSobolev r*U.sobolevExtension r K
  have he : U.energyCoordinates.symm.conjStarAlgEquiv
      (star (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M))) =
    star (U.energyCoordinates.symm.conjStarAlgEquiv
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^r) (U.spectralCoreMap M))) :=
    U.energyCoordinates.symm.conjStarAlgEquiv.map_star' _
  rw [map_sub,he,map_mul] at h
  simpa only [U.sobolevExtension_eq_conj,inverseSobolev] using h

 

lemma core_flow_energyGraph (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V))
    (hc : (HilbertCore.operator M).IsClosable) (hs : IsSelfAdjoint (HilbertCore.operator M).closure)
    (t : ℝ) {x y : Completion V} (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.flow (HilbertCore.operator M).closure hs t x,z) ∈ (U.energyPower r).graph ∧
      ‖z‖ ≤ Real.exp (‖U.sobolevExtension r K‖*|t|)*‖y‖ := by
  obtain ⟨B,hB,hbound⟩ := SymmetricOperator.flow_regularizer_factor _ hs
    (U.inverseSobolev r) (U.sobolevExtension r M) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r M hM hc) (U.sobolevExtension_defect r M K hM hK hk) t
  refine ⟨B y,?_,B.le_of_opNorm_le hbound y⟩
  have he := congrArg (fun Q : Completion V →L[ℂ] Completion V => Q y) hB
  change SymmetricOperator.flow _ hs t (U.inverseSobolev r y) = U.inverseSobolev r (B y) at he
  rw [U.inverseSobolev_on_graph r hxy] at he
  rw [he]
  exact U.inverseSobolev_graph r (B y)

lemma energyPower_zero_graph (x : Completion V) : (x,x) ∈ (U.energyPower 0).graph := by
  apply (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mpr
  apply (HilbertScale.mem_graph_iff _ _ _).mpr
  intro d
  simp only [pow_zero,Complex.ofReal_one,one_smul]

 

lemma firstOrderSmear_flow_energyGraph {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    {r : ℕ} (hrp : 1 ≤ r) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x,z) ∈ (U.energyPower r).graph ∧
      ‖z‖ ≤ Real.exp (‖U.sobolevExtension r (U.smearedPowerCommutator ha he hf r)‖*|t|)*‖y‖ := by
  have hM (v : V) : ‖A.smearedMap a d he f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hb
    exact (A.smearedMap_bound he hf hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hrp v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC))
  exact U.core_flow_energyGraph r (A.smearedMap a d he f hf)
    (U.smearedPowerCommutator ha he hf r) hM
    (U.smearedPowerCommutator_bound ha he hC hb hf r)
    (U.smearedPowerCommutator_pairing ha hq hh he hf hr r)
    (HilbertCore.closable (U.smearedMap_symmetric ha hq hh he hf hr))
    (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t hxy

lemma firstOrderSmear_flow_smoothEnergySpace {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨v,hv,_⟩ := (U.energyPower 0).mem_graph_iff.mp (U.energyPower_zero_graph
      (SymmetricOperator.flow (HilbertCore.operator (A.smearedMap a d he f hf)).closure
        (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x))
    dsimp only [Prod.fst] at hv
    rw [← hv]
    exact v.property
  · let v : (U.energyPower r).domain := ⟨x,hx r⟩
    obtain ⟨z,hz,_⟩ := U.firstOrderSmear_flow_energyGraph ha hq hh he hC hb hf hr
      (show 1 ≤ r by omega) t ((U.energyPower r).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
    obtain ⟨w,hw,_⟩ := (U.energyPower r).mem_graph_iff.mp hz
    dsimp only [Prod.fst] at hw
    rw [← hw]
    exact w.property

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance regularizerCommutationGradeFiniteDimensional :
    ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma sobolevExtension_weakCommutation (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (x y : Completion V) :
    inner ℂ (U.sobolevExtension r M x) (U.sobolevExtension r N y) =
      inner ℂ (U.sobolevExtension r N x) (U.sobolevExtension r M y) := by
  have hw' : ∀ x y, inner ℂ (U.spectralCoreMap M x) (U.spectralCoreMap N y) =
      inner ℂ (U.spectralCoreMap N x) (U.spectralCoreMap M y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.energyCoordinates.inner_map_map] using hw v w
  simpa only [sobolevExtension_apply,U.energyCoordinates.symm.inner_map_map] using
    HilbertScale.energyExtension_weakCommutation (fun d : ℕ => (1+(d : ℝ))^r)
      (fun d => one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
      _ _ (U.spectralCoreMap_bound r M hM) (U.spectralCoreMap_bound r N hN) hw'
      (U.energyCoordinates x) (U.energyCoordinates y)

 
def smoothSmear (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  { toFun := fun x => ⟨U.closedSmearedOperator hc a d f hf
      ⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩,
        U.closedSmearedOperator_preserves_smoothEnergySpace hc ha hf _ x.property⟩
    map_add' := by
      intro x y
      apply Subtype.ext
      change U.closedSmearedOperator hc a d f hf
        (⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩+
         ⟨y,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf y.property⟩) = _
      exact map_add (U.closedSmearedOperator hc a d f hf).toFun _ _
    map_smul' := by
      intro c x
      apply Subtype.ext
      change U.closedSmearedOperator hc a d f hf
        (c • ⟨x,U.smoothEnergySpace_le_closedSmearedDomain hc ha hf x.property⟩) = _
      exact map_smul (U.closedSmearedOperator hc a d f hf).toFun c _ }

lemma smoothSmear_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (x : U.smoothEnergySpace) :
    ((x : Completion V),(U.smoothSmear hc ha hf x : Completion V)) ∈
      (U.closedSmearedOperator hc a d f hf).graph := by
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_iff.mpr ⟨_,rfl,rfl⟩

lemma smoothSmear_eq_extension (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d r : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) {C : ℝ}
    (hM : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v‖ ≤ C*‖(A.energyShift^r) v‖)
    (x : U.smoothEnergySpace) {y : Completion V} (hxy : ((x : Completion V),y) ∈ (U.energyPower r).graph) :
    (U.smoothSmear hc ha hf x : Completion V) =
      U.sobolevExtension r (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf) y := by
  have hg := U.sobolevExtension_inverse_graph r _ hM (U.smearedCore_closable hc ha hf) y
  rw [U.inverseSobolev_on_graph r hxy] at hg
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_snd_inj (U.smoothSmear_graph hc ha hf x) hg rfl

lemma smoothSmear_symmetric (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha hf x : Completion V) (y : Completion V) =
      inner ℂ (x : Completion V) (U.smoothSmear hc ha hf y : Completion V) := by
  have hs := HilbertCore.formalAdjoint (U.smearedMap_symmetric ha hq hh (U.polynomialEnergyBounds hc a) hf hr)
  have hsc := SymmetricOperator.formalAdjoint_closure (U.smearedCore_closable hc ha hf)
    (U.smearedCore_closable hc ha hf) hs
  exact SymmetricOperator.formalAdjoint_graph_pairing hsc
    (U.smoothSmear_graph hc ha hf x) (U.smoothSmear_graph hc ha hf y)

lemma smoothSmear_weakCommutation (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc hb g.rapid_coefficients y : Completion V) =
    inner ℂ (U.smoothSmear hc hb g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc ha f.rapid_coefficients y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^q)*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ g.rapid_coefficients hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD.le))
  let xx : (U.energyPower (k+l)).domain := ⟨x,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) x.property⟩
  let yy : (U.energyPower (k+l)).domain := ⟨y,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) y.property⟩
  have hx : ((x : Completion V),U.energyPower (k+l) xx) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨xx,rfl,rfl⟩
  have hy : ((y : Completion V),U.energyPower (k+l) yy) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨yy,rfl,rfl⟩
  rw [U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm x hx,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn y hy,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn x hx,
    U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm y hy]
  exact U.sobolevExtension_weakCommutation (k+l) M N hm hn
    (U.smearedMap_weak_commutation ha hb hqa hqb hha hhb _ _ hf hg hfg) _ _
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

def smoothEnergyPower (r : ℕ) (x : U.smoothEnergySpace) : Completion V :=
  U.energyPower r ⟨x,(iInf_le (fun k => (U.energyPower k).domain) r) x.property⟩

lemma smoothEnergyPower_graph (r : ℕ) (x : U.smoothEnergySpace) :
    ((x : Completion V),U.smoothEnergyPower r x) ∈ (U.energyPower r).graph :=
  (U.energyPower r).mem_graph_iff.mpr ⟨_,rfl,rfl⟩

lemma inverseSobolev_smoothEnergyPower (r : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev r (U.smoothEnergyPower r x) = (x : Completion V) :=
  U.inverseSobolev_on_graph r (U.smoothEnergyPower_graph r x)

lemma smoothSmear_coe (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    (U.smoothSmear hc ha hf ⟨(v : Completion V),U.core_le_smoothEnergySpace
      (HilbertCore.equiv V v).property⟩ : Completion V) =
      A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v := by
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  have h : ((v : Completion V),M v) ∈ (HilbertCore.operator M).graph :=
    (HilbertCore.operator M).mem_graph_iff.mpr ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply M v⟩
  exact (U.closedSmearedOperator hc a d f hf).mem_graph_snd_inj
    (U.smoothSmear_graph hc ha hf _) (LinearPMap.le_graph_of_le (HilbertCore.operator M).le_closure h) rfl
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma regularized_heisenberg_pairing (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    {x y u v : H} (hxy : (S x,S y) ∈ T.graph) (huv : (u,v) ∈ T.graph)
    (hw : ∀ t, inner ℂ (E (B t y)) (flow T hs t u) =
      inner ℂ (E (B t x)) (flow T hs t v)) (t : ℝ) :
    inner ℂ (E (B t x)) (flow T hs t u) = inner ℂ (E x) u := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => inner ℂ (E (B r x)) (flow T hs r u)) 0 s := by
    have h1 := (E.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s
      (regularizer_factor_derivative T hs S hS hSd B hB hK hb hxy s)
    change HasDerivAt (fun r : ℝ => E (B r x)) (E (B s (Complex.I • y))) s at h1
    have h2 := flow_derivative T hs huv s
    have hd0 := HasDerivAt.inner ℂ h1 h2
    have hz : inner ℂ (E (B s x)) (flow T hs s (Complex.I • v)) +
        inner ℂ (E (B s (Complex.I • y))) (flow T hs s u) = 0 := by
      rw [map_smul (flow T hs s),map_smul (B s),map_smul E,
        inner_smul_right,inner_smul_left,starRingEnd_apply,Complex.star_def,Complex.conj_I,hw s]
      ring
    rwa [hz] at hd0
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  have hzero : B 0 = 1 := by
    ext z
    apply selfAdjoint_injective_of_denseRange S hS hSd
    have h := congrArg (fun Q : H →L[ℂ] H => Q z) (hB 0)
    simpa only [flow_zero,ContinuousLinearMap.comp_apply,one_apply_eq_self] using h.symm
  simpa only [flow_zero,one_apply_eq_self,hzero] using he

omit [CompleteSpace H] in
 

lemma graph_invariant_of_core (M : H →ₗ.[ℂ] H) (hc : M.IsClosable) (Q : H →L[ℂ] H)
    (hcore : ∀ x y, (x,y) ∈ M.graph → (Q x,Q y) ∈ M.closure.graph)
    {x y : H} (hxy : (x,y) ∈ M.closure.graph) : (Q x,Q y) ∈ M.closure.graph := by
  rw [← hc.graph_closure_eq_closure_graph] at hxy
  have hclosed : IsClosed {p : H × H | (Q p.1,Q p.2) ∈ M.closure.graph} :=
    hc.closure_isClosed.preimage ((Q.continuous.comp continuous_fst).prodMk
      (Q.continuous.comp continuous_snd))
  exact (closure_minimal (fun p hp => hcore p.1 p.2 hp) hclosed) hxy
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma flow_inner (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x y : H) :
    inner ℂ (flow T hs t x) (flow T hs t y) = inner ℂ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
  change inner ℂ x ((flow T hs (-t)*flow T hs t) y) = _
  rw [← flow_add,neg_add_cancel,flow_zero,one_apply_eq_self]

lemma flow_inverse (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) (x : H) :
    flow T hs t (flow T hs (-t) x) = x := by
  change (flow T hs t*flow T hs (-t)) x=x
  rw [← flow_add,add_neg_cancel,flow_zero,one_apply_eq_self]
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma regularized_commutation_on_dense_core
    (A T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (D : Submodule ℂ H) (hDd : Dense (D : Set H)) (a b : D →ₗ[ℂ] D)
    (ha : ∀ x : D, ((x : H),(a x : H)) ∈ A.graph)
    (hb : ∀ x : D, ((x : H),(b x : H)) ∈ T.graph)
    (hasym : ∀ x y : D, inner ℂ (a x : H) (y : H) = inner ℂ (x : H) (a y : H))
    (hw : ∀ x y : D, inner ℂ (a x : H) (b y : H) = inner ℂ (b x : H) (a y : H))
    (S E : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hDS : ∀ x : D, ∃ y, S y = (x : H)) (hE : ∀ x, (S x,E x) ∈ A.graph)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    (hFD : ∀ t (x : D), flow T hs t x ∈ D) (t : ℝ) (x : D) :
    (flow T hs t x,flow T hs t (a x : H)) ∈ A.graph := by
  classical
  choose R hR using hDS
  let F (s : ℝ) (z : D) : D := ⟨flow T hs s z,hFD s z⟩
  have hF (s : ℝ) (z : D) : (b (F s z) : H) = flow T hs s (b z : H) :=
    T.mem_graph_snd_inj (hb (F s z)) (flow_graph T hs s (hb z)) rfl
  have hEB (s : ℝ) (z : D) : E (B s (R z)) = (a (F s z) : H) := by
    have he := congrArg (fun Q : H →L[ℂ] H => Q (R z)) (hB s)
    change flow T hs s (S (R z)) = S (B s (R z)) at he
    rw [hR] at he
    exact A.mem_graph_snd_inj (hE (B s (R z))) (ha (F s z)) he.symm
  have hp (s : ℝ) (y : D) :
      inner ℂ (a (F s x) : H) (F s y : H) = inner ℂ (a x : H) (y : H) := by
    have hxy : (S (R x),S (R (b x))) ∈ T.graph := by rw [hR,hR]; exact hb x
    have hweak (r : ℝ) : inner ℂ (E (B r (R (b x)))) (flow T hs r y) =
        inner ℂ (E (B r (R x))) (flow T hs r (b y : H)) := by
      rw [hEB,hEB,← hF r y]
      change inner ℂ (a (F r (b x)) : H) (F r y : H) =
        inner ℂ (a (F r x) : H) (b (F r y) : H)
      rw [hasym]
      change inner ℂ (flow T hs r (b x : H)) (a (F r y) : H) = _
      rw [← hF r x]
      exact (hw (F r x) (F r y)).symm
    have hc := regularized_heisenberg_pairing T hs S E hS hSd B hB hK hbound
      hxy (hb y) hweak s
    rw [hEB] at hc
    have he0 : E (R x) = (a x : H) := A.mem_graph_snd_inj (hE (R x)) (ha x) (hR x)
    rwa [he0] at hc
  have heq : (a (F t x) : H) = flow T hs t (a x : H) := by
    apply ext_inner_right ℂ
    intro z
    have hd : DenseRange D.subtype := by simpa [DenseRange] using hDd
    apply hd.induction_on (p := fun z => inner ℂ (a (F t x) : H) z = inner ℂ (flow T hs t (a x : H)) z)
    · exact isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner continuous_id)
    · intro y
      have hi : (F t (F (-t) y) : H) = (y : H) := flow_inverse T hs t y
      have hm := hp t (F (-t) y)
      rw [hi] at hm
      have hu := flow_inner T hs t (a x : H) (F (-t) y : H)
      rw [show flow T hs t (F (-t) y : H) = (y : H) from hi] at hu
      exact hm.trans hu.symm
  rw [← heq]
  exact ha (F t x)
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
