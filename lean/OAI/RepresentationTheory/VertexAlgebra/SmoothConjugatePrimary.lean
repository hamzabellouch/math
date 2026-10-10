import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SmoothConjugateInner

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
open scoped Topology ContDiff
open Filter MeasureTheory Set
open Filter Set
open Filter UniformSpace
open Set MeasureTheory
open Set
open MeasureTheory Filter
open Set MeasureTheory Filter UniformSpace
open Set UniformSpace
open Set UniformSpace Filter
open Set MeasureTheory Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_primary_real_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  exact U.primary_real_graph_invariant hc ha hp hh hd (f.translate (-t))
    (SmoothCircleFunction.translate_real hf (-t)) hO
    (hs (-t) (by simpa only [abs_neg] using ht')) hQ huv
 

lemma primary_complex_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨ε,hε,hεF⟩ := f.rePart.exists_translation_radius hO (f.rePart_support.trans hs)
  obtain ⟨δ,hδ,hδG⟩ := f.imPart.exists_translation_radius hO (f.imPart_support.trans hs)
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_of_lt (lt_min hε hδ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    apply U.field_graph_invariant_add_smul hc ha f f.rePart f.imPart Complex.I f.rePart_add_imPart (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro u v huv
      exact U.smoothConjugate_primary_real_graph hc ha hp hh hd f.rePart f.rePart_real hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      exact U.smoothConjugate_primary_real_graph hc ha hp hh hd f.imPart f.imPart_real hO Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma primary_complex_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.primary_complex_graph_invariant hc ha hp hh hd f hO hs Q hQ hxy
  · intro x y hxy
    exact U.primary_complex_graph_invariant hc ha hp hh hd f hO hs Q.adjoint (star_mem hQ) hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)
lemma smearedMap_add_state {a b : V} (ha : A.PolynomialEnergyBound a)
    (hb : A.PolynomialEnergyBound b) (hab : A.PolynomialEnergyBound (a+b))
    (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    A.smearedMap (a+b) d hab f hf=A.smearedMap a d ha f hf+A.smearedMap b d hb f hf := by
  ext v
  simp only [smearedMap_apply,physicalMode,mode_add,LinearMap.add_apply,Completion.coe_add,smul_add]
  exact (A.summable_norm_physicalSmear ha d hf v).of_norm.tsum_add
    (A.summable_norm_physicalSmear hb d hf v).of_norm
lemma smearedMap_smul_state {a : V} (ha : A.PolynomialEnergyBound a) (c : ℂ)
    (hca : A.PolynomialEnergyBound (c • a)) (d : ℕ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    A.smearedMap (c • a) d hca f hf=c • A.smearedMap a d ha f hf := by
  ext v
  simp only [smearedMap_apply,physicalMode,mode_smul,LinearMap.smul_apply,Completion.coe_smul,
    smul_comm (f _) c,tsum_const_smul'']
namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
lemma sobolevExtension_add (r : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^r) v‖) :
    U.sobolevExtension r (M+N)=U.sobolevExtension r M+U.sobolevExtension r N := by
  have hMN (v : V) : ‖(M+N) v‖ ≤ (C+D)*‖(A.energyShift^r) v‖ := by
    exact (norm_add_le (M v) (N v)).trans ((add_le_add (hM v) (hN v)).trans_eq (add_mul ..).symm)
  ext x
  have hd : DenseRange (fun v : V => (v : Completion V)) := Completion.denseRange_coe
  apply hd.induction_on (p := fun x => U.sobolevExtension r (M+N) x=(U.sobolevExtension r M+U.sobolevExtension r N) x) x
    (isClosed_eq (U.sobolevExtension r _).continuous (ContinuousLinearMap.continuous _))
  intro v
  simp only [add_apply,U.sobolevExtension_coe r _ hMN,
    U.sobolevExtension_coe r _ hM,U.sobolevExtension_coe r _ hN,LinearMap.add_apply]
lemma smoothSmear_add_state (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).add_mem ha hb) hf=
      U.smoothSmear hc ha hf+U.smoothSmear hc hb hf := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let N := A.smearedMap b d (U.polynomialEnergyBounds hc b) f hf
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ hf hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hC.le))
  have hn (v : V) : ‖N v‖ ≤ (coefficientSeminorm f q*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ hf hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (coefficientSeminorm_nonneg _ _) hD.le))
  have hmn (v : V) : ‖A.smearedMap (a+b) d (U.polynomialEnergyBounds hc (a+b)) f hf v‖ ≤
      (coefficientSeminorm f p*C+coefficientSeminorm f q*D)*‖(A.energyShift^(k+l)) v‖ := by
    rw [A.smearedMap_add_state (U.polynomialEnergyBounds hc a) (U.polynomialEnergyBounds hc b)]
    exact (norm_add_le (M v) (N v)).trans ((add_le_add (hm v) (hn v)).trans_eq (add_mul ..).symm)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc _ hf x:Completion V)=
    (U.smoothSmear hc ha hf x:Completion V)+(U.smoothSmear hc hb hf x:Completion V)
  rw [U.smoothSmear_eq_extension hc _ hf hmn x (U.smoothEnergyPower_graph (k+l) x),
    U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph (k+l) x),
    U.smoothSmear_eq_extension hc hb hf hn x (U.smoothEnergyPower_graph (k+l) x),
    A.smearedMap_add_state (U.polynomialEnergyBounds hc a) (U.polynomialEnergyBounds hc b),U.sobolevExtension_add (k+l) M N hm hn]
  rfl
lemma smoothSmear_smul_state (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (c : ℂ) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).smul_mem c ha) hf=c • U.smoothSmear hc ha hf := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  have hm (v : V) : ‖M v‖ ≤ (coefficientSeminorm f p*C)*‖(A.energyShift^k) v‖ := A.smearedMap_bound _ hf hM v
  have hcm (v : V) : ‖A.smearedMap (c • a) d (U.polynomialEnergyBounds hc (c • a)) f hf v‖ ≤
      (‖c‖*(coefficientSeminorm f p*C))*‖(A.energyShift^k) v‖ := by
    rw [A.smearedMap_smul_state (U.polynomialEnergyBounds hc a)]
    simpa only [LinearMap.smul_apply,norm_smul,mul_assoc] using mul_le_mul_of_nonneg_left (hm v) (norm_nonneg c)
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (U.smoothSmear hc _ hf x:Completion V)=c • (U.smoothSmear hc ha hf x:Completion V)
  rw [U.smoothSmear_eq_extension hc _ hf hcm x (U.smoothEnergyPower_graph k x),
    U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph k x),
    A.smearedMap_smul_state (U.polynomialEnergyBounds hc a),U.sobolevExtension_smul k M hm c]
  rfl
end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_zero_state (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothSmear hc ((A.grade d).zero_mem) hf=0 := by
  simpa only [zero_smul] using U.smoothSmear_smul_state hc ((A.grade d).zero_mem) (0:ℂ) hf
 
def stateCommutant (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R : Module.End ℂ U.smoothEnergySpace) : Submodule ℂ V where
  carrier := {a | ∃ ha : a ∈ A.grade d, U.smoothSmear hc ha hf*R=R*U.smoothSmear hc ha hf}
  zero_mem' := ⟨(A.grade d).zero_mem,by rw [U.smoothSmear_zero_state,zero_mul,mul_zero]⟩
  add_mem' := by
    rintro a b ⟨ha,hac⟩ ⟨hb,hbc⟩
    refine ⟨(A.grade d).add_mem ha hb,?_⟩
    rw [U.smoothSmear_add_state,add_mul,mul_add,hac,hbc]
  smul_mem' := by
    rintro c a ⟨ha,hac⟩
    refine ⟨(A.grade d).smul_mem c ha,?_⟩
    rw [U.smoothSmear_smul_state,smul_mul_assoc,mul_smul_comm,hac]
lemma primary_graph_invariant_of_hermitian (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (f : SmoothCircleFunction)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hH : ∀ b : V, b ∈ A.grade d → A.IsPrimary b → U.IsHermitian d b →
      ∀ x y, (x,y) ∈ (U.closedSmoothField hc b d f).graph →
        (Q x,Q y) ∈ (U.closedSmoothField hc b d f).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  obtain ⟨S,hS,hspan⟩ := U.exists_hermitian_primary_spanning d
  have hSP : Submodule.span ℂ (S : Set V) ≤ U.stateCommutant hc d f.rapid_coefficients R := by
    apply Submodule.span_le.mpr
    intro b hb
    obtain ⟨hbd,hbp,hbh⟩ := hS b hb
    refine ⟨hbd,?_⟩
    exact SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc hbd f.rapid_coefficients) Q hQ (U.closedSmoothField hc b d f)
      (U.smoothSmear_graph hc hbd f.rapid_coefficients) (hH b hbd hbp hbh)
  obtain ⟨_,hac⟩ := hSP (hspan a ha hp)
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hac hxy
lemma smoothConjugate_primary_complex_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈
       (U.closedSmoothField hc a d f).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (U.closedSmoothField_isClosed hc ha f)
    Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc ha f t Q _ hxy
  intro u v huv
  exact U.primary_complex_graph_invariant hc ha hp hh hd (f.translate (-t)) hO
    (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ huv
 

lemma all_primary_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hs
  let r : ℕ → ℝ := fun n => ε/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos hε (by positivity)
  have hrle (n : ℕ) : r n ≤ ε := div_le_self hε.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    apply U.primary_graph_invariant_of_hermitian hc ha hp f (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ hxy
    intro b hbd hbp hbh u v huv
    exact U.smoothConjugate_primary_complex_graph hc hbd hbp hbh hd f hO Q hQ (r n) (hr n)
      (fun t ht => hεF t (ht.trans_le (hrle n))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma all_primary_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hd : 0 < d) (f : SmoothCircleFunction)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.all_primary_graph_invariant hc ha hp hd f hO hs Q hQ hxy
  · intro x y hxy
    exact U.all_primary_graph_invariant hc ha hp hd f hO hs Q.adjoint (star_mem hQ) hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
lemma frequency_weight_shift (n j : ℤ) :
    1+|(n:ℝ)| ≤ (1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|) := by
  have h := abs_add_le ((n:ℝ)-(j:ℝ)) (j:ℝ)
  have hp := mul_nonneg (abs_nonneg ((n:ℝ)-(j:ℝ))) (abs_nonneg (j:ℝ))
  push_cast
  rw [sub_add_cancel] at h
  nlinarith
namespace RapidCoefficients
lemma shift {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) :
    RapidCoefficients (fun n => f (n-j)) := by
  intro p
  have hs : Summable (fun n : ℤ => ‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p) :=
    (hf p).comp_injective (fun x y h => by omega)
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ (hs.mul_right ((1+|(j:ℝ)|)^p))
  intro n
  calc
    _ ≤ ‖f (n-j)‖*((1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|))^p := by
      gcongr
      exact frequency_weight_shift n j
    _ = _ := by rw [mul_pow]; ring
end RapidCoefficients
namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
lemma physicalMode_bound_of_homogeneous {a : V} {d k : ℕ}
    (ha : a ∈ A.grade d) (n : ℤ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ h (v : V), v ∈ A.grade h →
      ‖A.physicalMode a d n v‖ ≤ C*(1+(h:ℝ))^k*‖v‖) (v : V) :
    ‖A.physicalMode a d n v‖ ≤ C*‖(A.energyShift^k) v‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [physicalMode,U.mode_norm_sq_eq_sum_grades ha]
  calc
    _ ≤ ∑ h ∈ A.gradeSupport v, (C*(1+(h:ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      apply Finset.sum_le_sum
      intro h _
      exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
        (hb h _ (A.gradeComponent_mem h v))
    _ = C^2*∑ h ∈ A.gradeSupport v, ((1+(h:ℝ))^k*‖A.gradeComponent h v‖)^2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h _
      ring
    _ = _ := by rw [← U.energy_norm_sq_eq_sum_grades]; ring
include U in
 

lemma physicalMode_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    (R j : ℕ) (n : ℤ) (v : V) :
    ‖A.physicalMode a d n v‖ ≤
      (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R)*(1+(j:ℝ))^p/(1+(j:ℝ))^R)*
        ‖(A.energyShift^(k+R)) v‖ := by
  apply U.physicalMode_bound_of_homogeneous ha n (by positivity)
  intro h w hw
  by_cases hnh : (h:ℤ) < n
  · rw [show A.physicalMode a d n w=0 from A.mode_eq_zero_of_negative_energy ha hw _ (by omega),norm_zero]
    positivity
  have hjw : 1+(j:ℝ) ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)) := by
    have hh : (n:ℝ) ≤ h := by exact_mod_cast le_of_not_gt hnh
    have hab := neg_le_abs ((n:ℝ)-(j:ℝ))
    have hp := mul_nonneg (abs_nonneg ((n:ℝ)-(j:ℝ))) (Nat.cast_nonneg (α := ℝ) h)
    push_cast
    nlinarith
  have hnw : 1+|(n:ℝ)| ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)) := by
    simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using frequency_weight_shift n j
  have hjpos : 0 < (1+(j:ℝ))^R := pow_pos (by positivity) _
  rw [div_mul_eq_mul_div,div_mul_eq_mul_div]
  apply (le_div_iff₀ hjpos).mpr
  have hz := hb n w
  rw [A.energyShift_pow_norm_on_grade hw] at hz
  calc
    ‖A.physicalMode a d n w‖*(1+(j:ℝ))^R ≤
        (C*(1+|(n:ℝ)|)^p*((1+(h:ℝ))^k*‖w‖))*
          ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)))^R := by
      gcongr
    _ ≤ (C*((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)))^p*((1+(h:ℝ))^k*‖w‖))*
          ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(h:ℝ)))^R := by gcongr
    _ = _ := by simp only [mul_pow,pow_add]; ring
include U in
lemma physicalMode_sobolev_fixed_bound {a : V} {d k : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (n : ℤ) (hb : ∀ v, ‖A.physicalMode a d n v‖ ≤ C*‖(A.energyShift^k) v‖)
    (r : ℕ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) v‖ := by
  induction r generalizing v with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero,mul_one] using hb v
  | succ r ih =>
    have he : A.energyShift (A.physicalMode a d n v) =
        (-(n : ℂ)) • A.physicalMode a d n v + A.physicalMode a d n (A.energyShift v) :=
      sub_eq_iff_eq_add.mp (A.energyShift_physical_commutator ha n v)
    rw [pow_succ,Module.End.mul_apply,he,map_add,map_smul]
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hp : (A.energyShift^(k+r)) (A.energyShift v) =
        (A.energyShift^(k+(r+1))) v := by
      rw [show k+(r+1)=k+r+1 by omega,pow_succ,Module.End.mul_apply]
    have hm := U.energyShift_pow_norm_mono (show k+r ≤ k+(r+1) by omega) v
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖ +
          ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) v‖) +
          C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+r)) (A.energyShift v)‖ := by
        rw [norm_smul,hn]
        exact add_le_add (mul_le_mul_of_nonneg_left (ih v) (abs_nonneg _)) (ih _)
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+(r+1))) v‖) +
          C*(1+|(n : ℝ)|)^r*‖(A.energyShift^(k+(r+1))) v‖ := by
        rw [hp]
        gcongr
      _ = _ := by rw [pow_succ]; ring

include U in
lemma physicalMode_positive_shift_sobolev_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    (R j r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)*(1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*
        ‖(A.energyShift^(k+R+r)) v‖ := by
  have h := U.physicalMode_sobolev_fixed_bound ha (by positivity)
    n (U.physicalMode_positive_shift_bound ha hC hb R j n) r v
  apply h.trans
  have hnw : 1+|(n:ℝ)| ≤ (1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)) := by
    simpa only [Int.cast_natCast,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) j)] using frequency_weight_shift n j
  calc
    _ ≤ (C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R)*(1+(j:ℝ))^p/(1+(j:ℝ))^R)*
        ((1+|((n-(j:ℤ):ℤ):ℝ)|)*(1+(j:ℝ)))^r*‖(A.energyShift^(k+R+r)) v‖ := by gcongr
    _ = _ := by simp only [mul_pow,pow_add]; ring

lemma weightedSmearedMap_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j r : ℕ) (v : V) :
    ‖U.weightedSmearedMap ha he (hf.shift (j:ℤ)) r v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))*C*
        (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖ := by
  rw [weightedSmearedMap_apply]
  have hs := U.summable_norm_sobolevSmear ha he (hf.shift (j:ℤ)) r v
  apply (norm_tsum_le_tsum_norm hs).trans
  have hsum : Summable (fun n : ℤ => ‖f (n-(j:ℤ))‖*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)) :=
    (hf (p+R+r)).comp_injective (Equiv.subRight (j:ℤ)).injective
  calc
    _ ≤ ∑' n : ℤ, (‖f (n-(j:ℤ))‖*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r))*
        (C*(1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R*‖(A.energyShift^(k+R+r)) v‖) := by
      apply Summable.tsum_le_tsum _ hs (hsum.mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f (n-(j:ℤ))‖*((C*(1+|((n-(j:ℤ):ℤ):ℝ)|)^(p+R+r)*
          (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖) :=
            mul_le_mul_of_nonneg_left (U.physicalMode_positive_shift_sobolev_bound ha hC hb R j r n v)
              (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by
      rw [tsum_mul_right]
      have hts := (Equiv.subRight (j:ℤ)).tsum_eq (fun n => ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))
      simp only [Equiv.subRight_apply] at hts
      rw [hts]
      ring

include U in
lemma smearedMap_positive_shift_bound {a : V} {d k p : ℕ}
    (ha : a ∈ A.grade d) (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j : ℕ) (v : V) :
    ‖A.smearedMap a d he (fun n => f (n-(j:ℤ))) (hf.shift (j:ℤ)) v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R))*C*
        (1+(j:ℝ))^p/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R)) v‖ := by
  simpa only [weightedSmearedMap_apply,pow_zero,Module.End.one_apply,Nat.add_zero,smearedMap_apply] using
    U.weightedSmearedMap_positive_shift_bound ha he hC hb hf R j 0 v

lemma smoothSmear_positive_shift_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k p : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j : ℕ) (x : U.smoothEnergySpace) :
    ‖(U.smoothSmear hc ha (hf.shift (j:ℤ)) x : Completion V)‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R))*C*
        (1+(j:ℝ))^p/(1+(j:ℝ))^R)*‖U.smoothEnergyPower (k+R) x‖ := by
  have hm := U.smearedMap_positive_shift_bound ha (U.polynomialEnergyBounds hc a) hC hb hf R j
  rw [U.smoothSmear_eq_extension hc ha (hf.shift (j:ℤ)) hm x (U.smoothEnergyPower_graph (k+R) x)]
  exact (U.sobolevExtension _ _).le_of_opNorm_le (U.sobolevExtension_norm _ _ (by positivity) hm) _

lemma smoothEnergyPower_smoothSmear_eq_extension (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d K : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) {C D : ℝ}
    (hm : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v‖ ≤ C*‖(A.energyShift^K) v‖)
    (hn : ∀ v, ‖U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r v‖ ≤ D*‖(A.energyShift^K) v‖)
    (x : U.smoothEnergySpace) :
    U.smoothEnergyPower r (U.smoothSmear hc ha hf x)=
      U.sobolevExtension K (U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r)
        (U.smoothEnergyPower K x) := by
  have hg := U.sobolevExtension_graph K _ _ hm hn (U.energyPower r) (U.energyOperator_closed _)
    (U.smearedMap_energyGraph ha (U.polynomialEnergyBounds hc a) hf r) (U.smoothEnergyPower K x)
  rw [← U.smoothSmear_eq_extension hc ha hf hm x (U.smoothEnergyPower_graph K x)] at hg
  exact (U.energyPower r).mem_graph_snd_inj (U.smoothEnergyPower_graph r _) hg rfl

lemma smoothSmear_positive_shift_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d k p : ℕ} (ha : a ∈ A.grade d) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n:ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (R j r : ℕ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.smoothSmear hc ha (hf.shift (j:ℤ)) x)‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R+r))*C*
        (1+(j:ℝ))^(p+r)/(1+(j:ℝ))^R)*‖U.smoothEnergyPower (k+R+r) x‖ := by
  have hm : ∀ v, ‖A.smearedMap a d (U.polynomialEnergyBounds hc a) _ (hf.shift (j:ℤ)) v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n:ℝ)|)^(p+R))*C*
        (1+(j:ℝ))^p/(1+(j:ℝ))^R)*‖(A.energyShift^(k+R+r)) v‖ := by
    intro v
    exact (U.smearedMap_positive_shift_bound ha (U.polynomialEnergyBounds hc a) hC hb hf R j v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k+R ≤ k+R+r) v) (by positivity))
  have hn := U.weightedSmearedMap_positive_shift_bound ha (U.polynomialEnergyBounds hc a) hC hb hf R j r
  rw [U.smoothEnergyPower_smoothSmear_eq_extension hc ha (hf.shift (j:ℤ)) r hm hn x]
  exact (U.sobolevExtension _ _).le_of_opNorm_le (U.sobolevExtension_norm _ _ (by positivity) hn) _
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA
lemma coefficientSeminorm_shift {f : ℤ → ℂ} (hf : RapidCoefficients f) (j : ℤ) (p : ℕ) :
    coefficientSeminorm (fun n => f (n-j)) p ≤ coefficientSeminorm f p*(1+|(j:ℝ)|)^p := by
  have hs : Summable (fun n : ℤ => ‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p) :=
    (hf p).comp_injective (Equiv.subRight j).injective
  unfold coefficientSeminorm
  calc
    _ ≤ ∑' n : ℤ, (‖f (n-j)‖*(1+|((n-j:ℤ):ℝ)|)^p)*(1+|(j:ℝ)|)^p := by
      apply Summable.tsum_le_tsum _ ((hf.shift j) p) (hs.mul_right _)
      intro n
      calc
        _ ≤ ‖f (n-j)‖*((1+|((n-j:ℤ):ℝ)|)*(1+|(j:ℝ)|))^p := by
          gcongr
          exact frequency_weight_shift n j
        _ = _ := by rw [mul_pow]; ring
    _ = _ := by
      rw [tsum_mul_right]
      have he := (Equiv.subRight j).tsum_eq (fun n => ‖f n‖*(1+|(n:ℝ)|)^p)
      simp only [Equiv.subRight_apply] at he
      rw [he]

namespace CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end CFTTypeVOA.UnitaryStructure
end StronglyRationalVOA

end

end OAI
