import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.LocalNormalSeries

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
lemma localNormalMap_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖U.localNormalMap hc ha hb f χ c x‖ ≤ C*‖U.smoothEnergyPower r x‖ :=
  U.smooth_linear_add_bound _ _
    (U.modulatedSum_sobolev_bound hc ha hb f.rapid_coefficients χ.rapid_coefficients (1-c))
    (U.modulatedSum_sobolev_bound hc hb ha χ.rapid_coefficients f.rapid_coefficients c)
lemma smoothSmear_sobolev_bound (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    ∃ r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
      ‖(U.smoothSmear hc ha hf x : Completion V)‖ ≤ C*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨C,hC,p,k,hA⟩ := (U.polynomialEnergyBounds hc a).physical A d
  refine ⟨k,coefficientSeminorm f p*C,mul_nonneg (coefficientSeminorm_nonneg f p) hC.le,?_⟩
  intro x
  rw [U.smoothSmear_eq_normalized hc ha hA hf]
  exact (U.normalizedField hc a d k hf).le_of_opNorm_le (U.normalizedField_norm hc hC.le hA hf) _
 

lemma localNormalMap_eq_smoothSmear (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (x : U.smoothEnergySpace) :
    U.localNormalMap hc ha hb f χ (1-(d:ℤ)) x=
      (U.smoothSmear hc (A.mode_mem_grade (k := d+e) ha hb (-1) (by omega))
        f.rapid_coefficients x : Completion V) := by
  let hn := A.mode_mem_grade (k := d+e) ha hb (-1) (by omega)
  let M := U.smoothEnergySpace.subtype.comp (U.smoothSmear hc hn f.rapid_coefficients)
  have H : U.localNormalMap hc ha hb f χ (1-(d:ℤ))=M := by
    apply U.smooth_linear_eq_of_core _ _ (U.localNormalMap_bound hc ha hb f χ _)
      (U.smoothSmear_sobolev_bound hc hn f.rapid_coefficients)
    intro v
    exact (U.localNormalMap_core hc ha hb hχ v).trans (U.smoothSmear_coe hc hn f.rapid_coefficients v).symm
  exact congrArg (fun L => L x) H
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
namespace StronglyRationalVOA.SmoothCircleFunction
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
def modulate (f : SmoothCircleFunction) (j : ℤ) : SmoothCircleFunction where
  toFun := fun t => fourier j (t : AddCircle (2*Real.pi))*f t
  periodic := by
    intro t
    simp only [AddCircle.coe_add,AddCircle.coe_period,add_zero]
    rw [f.periodic t]
  smooth := by
    apply ContDiff.mul _ f.smooth
    simp only [fourier_coe_apply]
    exact (((contDiff_const.mul Complex.ofRealCLM.contDiff).div_const _).cexp)
lemma modulate_coefficient (f : SmoothCircleFunction) (j n : ℤ) :
    (f.modulate j).coefficient n=f.coefficient (n-j) := by
  have h : (f.modulate j).toContinuousMap=(fourier j : C(AddCircle (2*Real.pi),ℂ))*f.toContinuousMap := by
    ext x
    induction x using Quotient.inductionOn with | h t => rfl
  rw [← fourierCoeff_toContinuousMap,h,FourierAnalysis.coefficient_character_mul,fourierCoeff_toContinuousMap]
lemma modulate_support (f : SmoothCircleFunction) (j : ℤ) :
    tsupport (f.modulate j).onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change fourier j (t : AddCircle (2*Real.pi))*f t ≠ 0 at hx
  change f t ≠ 0
  exact (mul_ne_zero_iff.mp hx).2
end StronglyRationalVOA.SmoothCircleFunction

open Set
namespace StronglyRationalVOA.SmoothCircleFunction
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
lemma modulate_translate_support (f : SmoothCircleFunction) (j : ℤ) (t : ℝ) :
    tsupport ((f.modulate j).translate t).onCircle ⊆ tsupport (f.translate t).onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h s =>
  change fourier j ((s-t : ℝ) : AddCircle (2*Real.pi))*f (s-t) ≠ 0 at hx
  change f (s-t) ≠ 0
  exact (mul_ne_zero_iff.mp hx).2
 

lemma exists_normal_cutoff (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))}
    (hO : IsOpen O) (hf : tsupport f.onCircle ⊆ O) :
    ∃ χ : SmoothCircleFunction, tsupport χ.onCircle ⊆ O ∧
      Disjoint (tsupport (χ.add (constant (-1)))) (tsupport f) := by
  obtain ⟨W,hW,hfW,hWO,hWc⟩ := exists_open_between_and_isCompact_closure isClosed_closure.isCompact hO hf
  obtain ⟨χ,_,hχ1,hχO⟩ := exists_real_cutoff hWc hO hWO
  refine ⟨χ,hχO,disjoint_lift ?_⟩
  have hG : tsupport (χ.add (constant (-1))).onCircle ⊆ Wᶜ := by
    apply closure_minimal _ hW.isClosed_compl
    intro x hx hxW
    have he := hχ1 (subset_closure hxW)
    induction x using Quotient.inductionOn with | h t =>
    change χ t+(-1:ℂ) ≠ 0 at hx
    change χ t=1 at he
    exact hx (by rw [he]; ring)
  exact Set.disjoint_left.mpr (fun x hx hfx => hG hx (hfW hfx))
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma modulatedSum_commutes (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : ℤ → ℂ} (hf : RapidCoefficients f) (hg : RapidCoefficients g) (r : ℤ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, U.smoothSmear hc ha (hg.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc ha (hg.shift j))
    (hB : ∀ j : ℤ, U.smoothSmear hc hb (hf.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc hb (hf.shift j))
    (x : U.smoothEnergySpace) :
    U.modulatedSum hc ha hb hf hg r (SymmetricOperator.restricted U.smoothEnergySpace Q hQ x)=
      Q (U.modulatedSum hc ha hb hf hg r x) := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have he (j : ℕ) : (U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
      (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) (R x)) : Completion V)=
      Q (U.smoothSmear hc ha (hg.shift (-(j+r:ℤ)))
        (U.smoothSmear hc hb (hf.shift (j+r:ℤ)) x)) := by
    have h (S T : Module.End ℂ U.smoothEnergySpace) (hS : S*R=R*S) (hT : T*R=R*T) :
        S*(T*R)=R*(S*T) := by rw [hT,← mul_assoc,hS,mul_assoc]
    exact congrArg (fun P : Module.End ℂ U.smoothEnergySpace => (P x : Completion V))
      (h _ _ (hA _) (hB _))
  rw [U.modulatedSum_apply,U.modulatedSum_apply]
  exact (tsum_congr he).trans (Q.hasSum (U.summable_modulated_product_shift hc ha hb hf hg r x).hasSum).tsum_eq
lemma localNormalMap_commutes (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (f χ : SmoothCircleFunction) (c : ℤ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, U.smoothSmear hc ha (χ.rapid_coefficients.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc ha (χ.rapid_coefficients.shift j))
    (hB : ∀ j : ℤ, U.smoothSmear hc hb (f.rapid_coefficients.shift j)*SymmetricOperator.restricted U.smoothEnergySpace Q hQ =
      SymmetricOperator.restricted U.smoothEnergySpace Q hQ*U.smoothSmear hc hb (f.rapid_coefficients.shift j))
    (x : U.smoothEnergySpace) :
    U.localNormalMap hc ha hb f χ c (SymmetricOperator.restricted U.smoothEnergySpace Q hQ x)=
      Q (U.localNormalMap hc ha hb f χ c x) := by
  dsimp only [localNormalMap,LinearMap.add_apply]
  rw [map_add,U.modulatedSum_commutes hc ha hb _ _ _ Q hQ hA hB,
    U.modulatedSum_commutes hc hb ha _ _ _ Q hQ hB hA]
lemma normal_product_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {χ f : SmoothCircleFunction}
    (hχ : Disjoint (tsupport (χ.add (SmoothCircleFunction.constant (-1)))) (tsupport f))
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hA : ∀ j : ℤ, ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (χ.modulate j)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (χ.modulate j)).graph)
    (hB : ∀ j : ℤ, ∀ x y, (x,y) ∈ (U.closedSmoothField hc b e (f.modulate j)).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc b e (f.modulate j)).graph)
    {x y : Completion V}
    (hxy : (x,y) ∈ (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph := by
  let hn : mode A.fields a (-1) b ∈ A.grade (d+e) := A.mode_mem_grade ha hb (-1) (by omega)
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hcA (j : ℤ) : U.smoothSmear hc ha (χ.rapid_coefficients.shift j)*R=R*U.smoothSmear hc ha (χ.rapid_coefficients.shift j) := by
    have H := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc ha (χ.modulate j).rapid_coefficients) Q hQ (U.closedSmoothField hc a d (χ.modulate j))
      (U.smoothSmear_graph hc ha (χ.modulate j).rapid_coefficients) (hA j)
    have he : (χ.modulate j).coefficient=fun n => χ.coefficient (n-j) := funext (χ.modulate_coefficient j)
    simpa only [he] using H
  have hcB (j : ℤ) : U.smoothSmear hc hb (f.rapid_coefficients.shift j)*R=R*U.smoothSmear hc hb (f.rapid_coefficients.shift j) := by
    have H := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
      (U.smoothSmear hc hb (f.modulate j).rapid_coefficients) Q hQ (U.closedSmoothField hc b e (f.modulate j))
      (U.smoothSmear_graph hc hb (f.modulate j).rapid_coefficients) (hB j)
    have he : (f.modulate j).coefficient=fun n => f.coefficient (n-j) := funext (f.modulate_coefficient j)
    simpa only [he] using H
  have hcomm : U.smoothSmear hc hn f.rapid_coefficients*R=R*U.smoothSmear hc hn f.rapid_coefficients := by
    ext z
    have H := U.localNormalMap_commutes hc ha hb f χ (1-(d:ℤ)) Q hQ hcA hcB z
    rw [U.localNormalMap_eq_smoothSmear hc ha hb hχ,
      U.localNormalMap_eq_smoothSmear hc ha hb hχ] at H
    convert! H using 1

  have hce := U.smoothSmear_core hc hn f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc hn f.rapid_coefficients)).closure =
    U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc hn f.rapid_coefficients) Q hQ hcomm hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def LocalState (hc : A.toVertexAlgebra.C2Cofinite) (a : V) (d : ℕ) : Prop :=
  ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
    tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
    Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
    (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph
lemma smoothConjugate_localState_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hL : U.LocalState hc a d)
    (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
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
  exact hL O hO (f.translate (-t)) (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ u v huv
lemma LocalState.normal_product (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hLa : U.LocalState hc a d) (hLb : U.LocalState hc b e) :
    U.LocalState hc (mode A.fields a (-1) b) (d+e) := by
  intro O hO f hf Q hQ x y hxy
  obtain ⟨χ,hχO,hχ⟩ := f.exists_normal_cutoff hO hf
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hf
  obtain ⟨δ,hδ,hδF⟩ := χ.exists_translation_radius hO hχO
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_min hε.le hδ.le) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈
      (U.closedSmoothField hc (mode A.fields a (-1) b) (d+e) f).graph := by
    apply U.normal_product_graph_invariant hc ha hb hχ (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro j u v huv
      apply U.smoothConjugate_localState_graph hc ha hLa (χ.modulate j) hO Q hQ (r n) (hr n) _ huv
      intro t ht
      exact (χ.modulate_translate_support j t).trans
        (hδF t (ht.trans_le ((hrle n).trans (min_le_right _ _))))
    · intro j u v huv
      apply U.smoothConjugate_localState_graph hc hb hLb (f.modulate j) hO Q hQ (r n) (hr n) _ huv
      intro t ht
      exact (f.modulate_translate_support j t).trans
        (hεF t (ht.trans_le ((hrle n).trans (min_le_left _ _))))
  exact (U.closedSmoothField_isClosed hc (A.mode_mem_grade ha hb (-1) (by omega)) f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma LocalState.span (hc : A.toVertexAlgebra.C2Cofinite) (d : ℕ) {S : Set V}
    (hS : ∀ a ∈ S, a ∈ A.grade d ∧ U.LocalState hc a d)
    {a : V} (ha : a ∈ Submodule.span ℂ S) : U.LocalState hc a d := by
  have hgrade : Submodule.span ℂ S ≤ A.grade d := Submodule.span_le.mpr (fun a h => (hS a h).1)
  intro O hO f hf Q hQ x y hxy
  obtain ⟨ε,hε,hεF⟩ := f.exists_translation_radius hO hf
  let r : ℕ → ℝ := fun n => ε/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos hε (by positivity)
  have hrle (n : ℕ) : r n ≤ ε := div_le_self hε.le (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ε
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc a d f).graph := by
    have hRs (z : U.smoothEnergySpace) : R n z ∈ U.smoothEnergySpace :=
      U.smoothConjugate_smooth Q (r n) (hr n) z.property
    let R' := SymmetricOperator.restricted U.smoothEnergySpace (R n) hRs
    have hSP : Submodule.span ℂ S ≤ U.stateCommutant hc d f.rapid_coefficients R' := by
      apply Submodule.span_le.mpr
      intro b hb
      obtain ⟨hbd,hLb⟩ := hS b hb
      refine ⟨hbd,?_⟩
      apply SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
        (U.smoothSmear hc hbd f.rapid_coefficients) (R n) hRs (U.closedSmoothField hc b d f)
        (U.smoothSmear_graph hc hbd f.rapid_coefficients)
      intro u v huv
      exact U.smoothConjugate_localState_graph hc hbd hLb f hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le (hrle n))) huv
    obtain ⟨_,hac⟩ := hSP ha
    have hce := U.smoothSmear_core hc (hgrade ha) f.rapid_coefficients
    change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc (hgrade ha) f.rapid_coefficients)).closure =
      U.closedSmoothField hc a d f at hce
    rw [← hce] at hxy ⊢
    exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
      (U.smoothSmear_core_closable hc (hgrade ha) f.rapid_coefficients) (R n) hRs hac hxy
  exact (U.closedSmoothField_isClosed hc (hgrade ha) f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace
namespace StronglyRationalVOA.SmoothCircleFunction
lemma differentiated_support_circle (f : SmoothCircleFunction) (k : ℕ) :
    tsupport (f.differentiated k).onCircle ⊆ tsupport f.onCircle := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  exact f.tsupport_lift_subset (f.differentiated_support k (subset_closure hx))
def translationTest (f : SmoothCircleFunction) (d : ℕ) : SmoothCircleFunction :=
  ((f.differentiated 1).scale Complex.I).add (f.scale (-(d:ℂ)))
lemma translationTest_coefficient (f : SmoothCircleFunction) (d : ℕ) (n : ℤ) :
    (f.translationTest d).coefficient n= (-((n:ℂ)+d))*f.coefficient n := by
  rw [translationTest,coefficient_add,coefficient_scale,coefficient_scale,coefficient_differentiated,pow_one]
  linear_combination (f.coefficient n*(n:ℂ))*(Complex.I_sq)
lemma translationTest_support (f : SmoothCircleFunction) (d : ℕ) :
    tsupport (f.translationTest d).onCircle ⊆ tsupport f.onCircle := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  have hf : f.onCircle x=0 := (Function.notMem_support.mp (fun h => hn (subset_closure h)))
  have hd : (f.differentiated 1).onCircle x=0 :=
    (Function.notMem_support.mp (fun h => hn (f.differentiated_support_circle 1 (subset_closure h))))
  induction x using Quotient.inductionOn with | h t =>
  change f t=0 at hf
  change f.differentiated 1 t=0 at hd
  exact hx (by change Complex.I * f.differentiated 1 t + (-(d:ℂ))*f t = 0; rw [hf,hd]; ring)
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma closedSmoothField_translation (hc : A.toVertexAlgebra.C2Cofinite)
    (a : V) (d : ℕ) (f : SmoothCircleFunction) :
    U.closedSmoothField hc (A.toVertexAlgebra.translation a) (d+1) f=
      U.closedSmoothField hc a d (f.translationTest d) := by
  have h : A.smearedMap (A.toVertexAlgebra.translation a) (d+1) (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients =
      A.smearedMap a d (U.polynomialEnergyBounds hc _) (f.translationTest d).coefficient (f.translationTest d).rapid_coefficients := by
    ext v
    simp only [CFTTypeVOA.smearedMap_apply]
    apply tsum_congr
    intro n
    rw [A.translation_physicalMode,LinearMap.smul_apply,Completion.coe_smul,f.translationTest_coefficient]
    simp only [smul_smul]
    congr 1
    ring
  exact congrArg (fun M : V →ₗ[ℂ] Completion V => (HilbertCore.operator M).closure) h
lemma LocalState.translation (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (hL : U.LocalState hc a d) :
    U.LocalState hc (A.toVertexAlgebra.translation a) (d+1) := by
  intro O hO f hf Q hQ x y hxy
  rw [U.closedSmoothField_translation] at hxy ⊢
  exact hL O hO (f.translationTest d) ((f.translationTest_support d).trans hf) Q hQ x y hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_realLocal_graph (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hL : ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
      f.IsReal → tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
      Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
      (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph)
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
  exact hL O hO (f.translate (-t)) (SmoothCircleFunction.translate_real hf (-t))
    (hs (-t) (by simpa only [abs_neg] using ht')) Q hQ u v huv
 

lemma localState_of_real (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hL : ∀ (O : Set (AddCircle (2*Real.pi))), IsOpen O → ∀ f : SmoothCircleFunction,
      f.IsReal → tsupport f.onCircle ⊆ O → ∀ Q : Completion V →L[ℂ] Completion V,
      Q ∈ (U.primaryAlgebra hc O).commutant → ∀ x y,
      (x,y) ∈ (U.closedSmoothField hc a d f).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph) : U.LocalState hc a d := by
  intro O hO f hs Q hQ x y hxy
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
      exact U.smoothConjugate_realLocal_graph hc ha hL f.rePart f.rePart_real hO Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      exact U.smoothConjugate_realLocal_graph hc ha hL f.imPart f.imPart_real hO Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) huv
  exact (U.closedSmoothField_isClosed hc ha f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma stress_localState (hc : A.toVertexAlgebra.C2Cofinite) :
    U.LocalState hc A.conformalVector 2 := by
  apply U.localState_of_real hc A.conformal_mem
  intro O _ f hf hs Q hQ x y hxy
  let F : U.PrimaryTestField :=
    ⟨A.conformalVector,2,A.conformal_mem,A.conformal_quasiPrimary,U.stress_hermitian,
      f,hf,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  exact F.commutant_preserves_graph hc hs hQ hxy
lemma primary_localState (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (hd : 0 < d) :
    U.LocalState hc a d := by
  intro O hO f hs Q hQ x y hxy
  exact U.all_primary_graph_invariant hc ha hp hd f hO hs Q hQ hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma vacuum_smearedMap (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction) (v : V) :
    A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients v=
      f.coefficient 0 • (v : Completion V) := by
  have hm (n : ℤ) : A.physicalMode A.vacuum 0 n=if n=0 then 1 else 0 := by
    by_cases h : n=0
    · subst n
      simp [physicalMode,A.vacuum_mode]
    · have h' : n-1 ≠ -1 := by omega
      simp [physicalMode,A.vacuum_mode,h,h']
  rw [A.smearedMap_apply,tsum_eq_single 0]
  · simp [hm]
  · intro n hn
    simp [hm,hn]
lemma vacuum_closed_graph (hc : A.toVertexAlgebra.C2Cofinite) (f : SmoothCircleFunction)
    (x y : Completion V) :
    (x,y) ∈ (U.closedSmoothField hc A.vacuum 0 f).graph ↔ y=f.coefficient 0 • x := by
  have hv : A.vacuum ∈ A.grade 0 := by rw [A.grade_zero]; exact Submodule.mem_span_singleton_self _
  let c := f.coefficient 0
  let g : Completion V → Completion V × Completion V := fun x => (x,c • x)
  have hg : Continuous g := continuous_id.prodMk (continuous_id.const_smul c)
  have hcore : ((U.smoothSmearedField hc A.vacuum 0 f).graph : Set (Completion V × Completion V))=
      Set.range (fun v : V => g (v : Completion V)) := by
    ext p
    constructor
    · intro hp
      obtain ⟨z,hz,hp⟩ := (U.smoothSmearedField hc A.vacuum 0 f).mem_graph_iff.mp hp
      obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective z
      refine ⟨v,?_⟩
      have he := U.vacuum_smearedMap hc f v
      change HilbertCore.operator (A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients) (HilbertCore.equiv V v)=p.2 at hp
      rw [HilbertCore.operator_apply] at hp
      exact Prod.ext hz (he.symm.trans hp)
    · rintro ⟨v,rfl⟩
      apply (U.smoothSmearedField hc A.vacuum 0 f).mem_graph_iff.mpr
      refine ⟨HilbertCore.equiv V v,rfl,?_⟩
      change HilbertCore.operator (A.smearedMap A.vacuum 0 (U.polynomialEnergyBounds hc _) f.coefficient f.rapid_coefficients) (HilbertCore.equiv V v)=_
      rw [HilbertCore.operator_apply]
      exact U.vacuum_smearedMap hc f v
  change (x,y) ∈ ((U.closedSmoothField hc A.vacuum 0 f).graph : Set (Completion V × Completion V)) ↔ _
  rw [U.closedSmoothField_graph hc hv f,hcore]
  constructor
  · intro h
    have hs : closure (Set.range (fun v : V => g (v : Completion V))) ⊆
        {p : Completion V × Completion V | p.2=c • p.1} := by
      apply closure_minimal _ (isClosed_eq continuous_snd (continuous_fst.const_smul c))
      rintro _ ⟨v,rfl⟩
      rfl
    exact hs h
  · intro h
    rw [h]
    have H := mem_closure_image hg.continuousAt (Completion.denseRange_coe x)
    have hr : g '' Set.range (Completion.coe' : V → Completion V) =
        Set.range (fun v : V => g (v : Completion V)) := by
      ext p
      constructor
      · rintro ⟨_,⟨v,rfl⟩,rfl⟩
        exact ⟨v,rfl⟩
      · rintro ⟨v,rfl⟩
        exact ⟨(v : Completion V),⟨v,rfl⟩,rfl⟩
    rw [hr] at H
    exact H
lemma vacuum_localState (hc : A.toVertexAlgebra.C2Cofinite) : U.LocalState hc A.vacuum 0 := by
  intro O _ f _ Q _ x y hxy
  rw [U.vacuum_closed_graph] at hxy ⊢
  rw [hxy,map_smul]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
