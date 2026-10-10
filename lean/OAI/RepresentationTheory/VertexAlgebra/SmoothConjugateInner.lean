import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.GraphInvariantOf

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
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SmoothRotationKernel
lemma smoothConjugate_inner_left (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x y : H) :
    inner ℂ (smoothConjugate T hs Q ε hε x) y =
      ∫ t, (kernel ε hε t : ℂ) * inner ℂ (conjugation T hs Q t x) y := by
  rw [smoothConjugate_apply]
  let L : H →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ y).restrictScalars ℝ)
  have h := L.integral_comp_comm (smoothConjugate_integrable T hs Q ε hε x)
  change (∫ t, starRingEnd ℂ (inner ℂ y (kernel ε hε t • conjugation T hs Q t x))) =
    starRingEnd ℂ (inner ℂ y (∫ t, kernel ε hε t • conjugation T hs Q t x)) at h
  simp_rw [inner_conj_symm,← Complex.coe_smul,inner_smul_left,Complex.conj_ofReal] at h
  exact h.symm
lemma smoothConjugate_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) :
    (smoothConjugate T hs Q ε hε).adjoint = smoothConjugate T hs Q.adjoint ε hε := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  rw [smoothConjugate_inner_left,smoothConjugate_inner_right]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← conjugation_adjoint,ContinuousLinearMap.adjoint_inner_left]
end StronglyRationalVOA.SymmetricOperator

open Set MeasureTheory Filter UniformSpace
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
local instance smoothConjugateInnerPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
lemma translate_power (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    (f.power k).translate t = (f.translate t).power k := by
  ext s
  rfl
lemma translate_tsupport_subset (f : SmoothCircleFunction) (t : ℝ) :
    tsupport (f.translate t).onCircle ⊆
      (fun x : AddCircle (2*Real.pi) => x-(t : AddCircle (2*Real.pi))) ⁻¹' tsupport f.onCircle := by
  apply closure_minimal
  · intro x hx
    exact subset_closure (by simpa only [Function.mem_support,translate_onCircle] using hx)
  · exact isClosed_closure.preimage (continuous_id.sub continuous_const)
 

lemma exists_translation_radius (f : SmoothCircleFunction) {O : Set (AddCircle (2*Real.pi))}
    (hO : IsOpen O) (hf : tsupport f.onCircle ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → tsupport (f.translate t).onCircle ⊆ O := by
  let N : Set (ℝ × AddCircle (2*Real.pi)) :=
    (fun z => z.2+(z.1 : AddCircle (2*Real.pi))) ⁻¹' O
  have hc : Continuous (fun t : ℝ => (t : AddCircle (2*Real.pi))) := continuous_quotient_mk'
  have hN : IsOpen N := hO.preimage (continuous_snd.add (hc.comp continuous_fst))
  have hsub : ({0} : Set ℝ) ×ˢ tsupport f.onCircle ⊆ N := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have ht0 : t=0 := ht
    subst t
    change x+(0 : AddCircle (2*Real.pi)) ∈ O
    simpa only [add_zero] using hf hx
  obtain ⟨u,v,hu,_,h0,hf',huv⟩ := generalized_tube_lemma isCompact_singleton
    isClosed_closure.isCompact hN hsub
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (h0 (by rfl)))
  refine ⟨ε,hε,fun t ht x hx => ?_⟩
  have ht' : t ∈ u := he (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
  have hx' := f.translate_tsupport_subset t hx
  have h : (t,x-(t : AddCircle (2*Real.pi))) ∈ N := huv ⟨ht',hf' hx'⟩
  change x-(t : AddCircle (2*Real.pi))+(t : AddCircle (2*Real.pi)) ∈ O at h
  simpa only [sub_add_cancel] using h
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
namespace PrimaryTestField
variable {U}
def translate (F : U.PrimaryTestField) (t : ℝ) : U.PrimaryTestField where
  state := F.state
  weight := F.weight
  homogeneous := F.homogeneous
  quasiPrimary := F.quasiPrimary
  hermitian := F.hermitian
  test := F.test.translate t
  real := SmoothCircleFunction.translate_real F.real t
  kind := by
    rcases F.kind with h | h | ⟨hp,hd,b,hb,he⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨hp,hd,b.translate t,SmoothCircleFunction.translate_real hb t,
        by rw [he,SmoothCircleFunction.translate_power,SmoothCircleFunction.translate_power]⟩)
lemma commutant_preserves_graph (F : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite)
    {O : Set (AddCircle (2*Real.pi))} (hF : tsupport F.test.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (F.field hc).graph) :
    (Q x,Q y) ∈ (F.field hc).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes (F.field hc) (F.closed hc) Q _ hxy
  intro i j
  rw [← SetLike.mem_coe,primaryAlgebra,LocalOperatorAlgebra.coe_generated_commutant] at hQ
  exact (hQ _ (Or.inl ⟨F,hF,i,j,rfl⟩)).symm
end PrimaryTestField
 
lemma conjugation_preserves_field_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d (f.translate (-t))).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d (f.translate (-t))).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (SymmetricOperator.conjugation U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q t x,
     SymmetricOperator.conjugation U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q t y) ∈
      (U.closedSmoothField hc a d f).graph := by
  have h := U.rotation_closedSmoothField_graph hc ha (f.translate (-t)) t
    (hQ _ _ (U.rotation_closedSmoothField_graph hc ha f (-t) hxy))
  simpa only [SmoothCircleFunction.translate_add,neg_add_cancel,SmoothCircleFunction.translate_zero,
    SymmetricOperator.conjugation,← U.rotation_eq_hamiltonianFlow,mul_apply_eq_comp] using h
lemma smoothConjugate_preserves_primary_graph (hc : A.toVertexAlgebra.C2Cofinite)
    (F : U.PrimaryTestField) {O : Set (AddCircle (2*Real.pi))}
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    (ε : ℝ) (hε : 0 < ε)
    (hF : ∀ t : ℝ, |t| < ε → tsupport (F.test.translate t).onCircle ⊆ O)
    {x y : Completion V} (hxy : (x,y) ∈ (F.field hc).graph) :
    (SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x,
     SymmetricOperator.smoothConjugate U.conformalHamiltonian
       (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε y) ∈ (F.field hc).graph := by
  apply SymmetricOperator.conjugationIntegral_preserves_graph _ _ _ (F.closed hc) Q _ _ _ _ _ _ _ hxy
  intro t ht x y hxy
  have ht' : |t| < ε := by
    have hk : SmoothRotationKernel.kernel ε hε t ≠ 0 := by
      intro h
      exact ht (by simp only [SmoothRotationKernel.jet_zero,h,Complex.ofReal_zero])
    have h := (SmoothRotationKernel.support ε hε).le hk
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  apply U.conjugation_preserves_field_graph hc F.homogeneous F.test t Q _ hxy
  intro u v huv
  exact (F.translate (-t)).commutant_preserves_graph hc (hF (-t) (by simpa only [abs_neg] using ht')) hQ huv
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
lemma onSubmodule_closure_graph_invariant (D : Submodule ℂ H) (P : Module.End ℂ D)
    (hP : (onSubmodule D P).IsClosable) (Q : H →L[ℂ] H) (hQ : ∀ x : D, Q x ∈ D)
    (hc : P*restricted D Q hQ = restricted D Q hQ*P)
    {x y : H} (hxy : (x,y) ∈ (onSubmodule D P).closure.graph) :
    (Q x,Q y) ∈ (onSubmodule D P).closure.graph := by
  apply graph_invariant_of_core _ hP Q _ hxy
  intro u v huv
  obtain ⟨z,rfl,rfl⟩ := (onSubmodule D P).mem_graph_iff.mp huv
  have h := onSubmodule_mem_graph D P (restricted D Q hQ z)
  have he := congrArg (fun R : Module.End ℂ D => (R z : H)) hc
  change (P (restricted D Q hQ z) : H) = Q (P z) at he
  rw [he] at h
  exact LinearPMap.le_graph_of_le (onSubmodule D P).le_closure h
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothSmear_scale (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (c : ℂ) :
    U.smoothSmear hc ha (f.scale c).rapid_coefficients=c • U.smoothSmear hc ha f.rapid_coefficients := by
  have he : (f.scale c).coefficient=fun n => c*f.coefficient n := funext (f.coefficient_scale c)
  rw [show U.smoothSmear hc ha (f.scale c).rapid_coefficients=
    U.smoothSmear hc ha (f.rapid_coefficients.smul c) from by congr 1]
  exact U.smoothSmear_smul hc ha _ c
lemma smoothSmear_linearCombination (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f g h : SmoothCircleFunction) (c : ℂ)
    (he : ∀ t, f t=c*(g t-h t)) :
    U.smoothSmear hc ha f.rapid_coefficients =
      c • (U.smoothSmear hc ha g.rapid_coefficients-U.smoothSmear hc ha h.rapid_coefficients) := by
  have hf : f=(g.add (h.scale (-1))).scale c := by
    ext t
    simpa only [SmoothCircleFunction.scale_apply,SmoothCircleFunction.add_apply,neg_one_mul,sub_eq_add_neg] using he t
  rw [hf,U.smoothSmear_scale,U.smoothSmear_add_functions,U.smoothSmear_scale]
  module
 

lemma field_graph_invariant_linearCombination (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f g h : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(g t-h t))
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hg : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d g).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d g).graph)
    (hh : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d h).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d h).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hgc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha g.rapid_coefficients) Q hQ (U.closedSmoothField hc a d g)
    (U.smoothSmear_graph hc ha g.rapid_coefficients) hg
  have hhc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha h.rapid_coefficients) Q hQ (U.closedSmoothField hc a d h)
    (U.smoothSmear_graph hc ha h.rapid_coefficients) hh
  have hfc : U.smoothSmear hc ha f.rapid_coefficients*R=R*U.smoothSmear hc ha f.rapid_coefficients := by
    rw [U.smoothSmear_linearCombination hc ha f g h c he,smul_mul_assoc,mul_smul_comm,
      sub_mul,mul_sub,hgc,hhc]
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hfc hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_difference_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : U.PrimaryTestField) (hs : G.state=F.state) (hw : G.weight=F.weight)
    (f : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(F.test t-G.test t))
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hF : tsupport F.test.onCircle ⊆ O) (hG : tsupport G.test.onCircle ⊆ O)
    (Q : Completion V →L[ℂ] Completion V) (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc F.state F.weight f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc F.state F.weight f).graph := by
  obtain ⟨ε,hε,hεF⟩ := F.test.exists_translation_radius hO hF
  obtain ⟨δ,hδ,hδG⟩ := G.test.exists_translation_radius hO hG
  let r : ℕ → ℝ := fun n => min ε δ/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := div_pos (lt_min hε hδ) (by positivity)
  have hrle (n : ℕ) : r n ≤ min ε δ :=
    div_le_self (le_of_lt (lt_min hε hδ)) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hl : Tendsto r atTop (𝓝 0) := by
    simpa only [zero_mul,mul_zero,mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (min ε δ)
  let R (n : ℕ) := SymmetricOperator.smoothConjugate U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q (r n) (hr n)
  have hRn (n : ℕ) : (R n x,R n y) ∈ (U.closedSmoothField hc F.state F.weight f).graph := by
    apply U.field_graph_invariant_linearCombination hc F.homogeneous f F.test G.test c he (R n)
      (fun z => U.smoothConjugate_smooth Q (r n) (hr n) z.property) _ _ hxy
    · intro u v huv
      exact U.smoothConjugate_preserves_primary_graph hc F Q hQ (r n) (hr n)
        (fun t ht => hεF t (ht.trans_le ((hrle n).trans (min_le_left ε δ)))) huv
    · intro u v huv
      have hG' : (u,v) ∈ (G.field hc).graph := by
        simpa only [PrimaryTestField.field,hs,hw] using huv
      have h := U.smoothConjugate_preserves_primary_graph hc G Q hQ (r n) (hr n)
        (fun t ht => hδG t (ht.trans_le ((hrle n).trans (min_le_right ε δ)))) hG'
      simpa only [PrimaryTestField.field,hs,hw] using h
  exact (U.closedSmoothField_isClosed hc F.homogeneous f).mem_of_tendsto
    ((SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl x).prodMk_nhds
      (SymmetricOperator.smoothConjugate_strong _ _ Q r hr hl y)) (Eventually.of_forall hRn)
lemma primary_difference_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    (F G : U.PrimaryTestField) (hs : G.state=F.state) (hw : G.weight=F.weight)
    (f : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=c*(F.test t-G.test t))
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O)
    (hF : tsupport F.test.onCircle ⊆ O) (hG : tsupport G.test.onCircle ⊆ O) (i j : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight f)
      (U.closedSmoothField_isClosed hc F.homogeneous f) i j ∈ U.primaryAlgebra hc O := by
  rw [← VonNeumannAlgebra.commutant_commutant (U.primaryAlgebra hc O),VonNeumannAlgebra.mem_commutant_iff]
  intro Q hQ
  apply ClosedGraphData.entry_commutes_of_graph_invariant
  · intro x y hxy
    exact U.primary_difference_graph_invariant hc F G hs hw f c he hO hF hG Q hQ hxy
  · intro x y hxy
    exact U.primary_difference_graph_invariant hc F G hs hw f c he hO hF hG Q.adjoint
      (star_mem hQ) hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
lemma compact_translation_radius {K O : Set (AddCircle (2*Real.pi))}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → ∀ x ∈ K, x+(t : AddCircle (2*Real.pi)) ∈ O := by
  let N : Set (ℝ × AddCircle (2*Real.pi)) :=
    (fun z => z.2+(z.1 : AddCircle (2*Real.pi))) ⁻¹' O
  have hc : Continuous (fun t : ℝ => (t : AddCircle (2*Real.pi))) := continuous_quotient_mk'
  have hN : IsOpen N := hO.preimage (continuous_snd.add (hc.comp continuous_fst))
  have hsub : ({0} : Set ℝ) ×ˢ K ⊆ N := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    have ht0 : t=0 := ht
    subst t
    change x+(0 : AddCircle (2*Real.pi)) ∈ O
    simpa only [add_zero] using hKO hx
  obtain ⟨u,v,hu,_,h0,hK',huv⟩ := generalized_tube_lemma isCompact_singleton hK hN hsub
  obtain ⟨ε,hε,he⟩ := Metric.mem_nhds_iff.mp (hu.mem_nhds (h0 (by rfl)))
  refine ⟨ε,hε,fun t ht x hx => ?_⟩
  change (t,x) ∈ N
  apply huv
  refine ⟨?_,hK' hx⟩
  exact he (by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using ht)
 

lemma exists_real_cutoff {K O : Set (AddCircle (2*Real.pi))}
    (hK : IsCompact K) (hO : IsOpen O) (hKO : K ⊆ O) :
    ∃ χ : SmoothCircleFunction, χ.IsReal ∧ Set.EqOn χ.onCircle 1 K ∧
      tsupport χ.onCircle ⊆ O := by
  obtain ⟨V,hV,hKV,hVO,hVc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  obtain ⟨q,hq1,hqc,hqO,hq01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hVc hO hVO
  obtain ⟨ε,hε,hεK⟩ := compact_translation_radius hK hV hKV
  obtain ⟨δ,hδ,hδq⟩ := compact_translation_radius hqc hO hqO
  let r : ℝ := min ε δ/2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left ε δ)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right ε δ)
  let b : ℝ → ℝ := SmoothRotationKernel.kernel r hr
  have hbc : HasCompactSupport b := by
    change IsCompact (tsupport (SmoothRotationKernel.kernel r hr))
    rw [SmoothRotationKernel.tsupport]
    exact isCompact_closedBall 0 r
  have hbs : ContDiff ℝ ∞ b := (SmoothRotationKernel.bump r hr).contDiff_normed
  let ql : ℝ → ℝ := fun t => q (t : AddCircle (2*Real.pi))
  have hql : Continuous ql := q.continuous.comp continuous_quotient_mk'
  let w : ℝ → ℝ := fun t => ∫ s, b s * ql (t-s)
  have hws : ContDiff ℝ ∞ w := by
    exact hbc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hbs hql.locallyIntegrable
  have hwp : Function.Periodic w (2*Real.pi) := by
    intro t
    apply integral_congr_ae
    filter_upwards [] with s
    change b s * q ((t+2*Real.pi-s : ℝ) : AddCircle (2*Real.pi)) =
      b s * q ((t-s : ℝ) : AddCircle (2*Real.pi))
    congr 2
    rw [show t+2*Real.pi-s=(t-s)+2*Real.pi by ring,AddCircle.coe_add,AddCircle.coe_period,add_zero]
  let χ := ofRealPeriodic w hwp hws
  have hbe {s : ℝ} (hs : b s ≠ 0) : |s| < r := by
    have h : s ∈ Function.support (SmoothRotationKernel.kernel r hr) := hs
    rw [SmoothRotationKernel.support] at h
    simpa only [Metric.mem_ball,Real.dist_eq,sub_zero] using h
  have hcut : Set.EqOn χ.onCircle 1 K := by
    intro x hx
    induction x using Quotient.inductionOn with | h t =>
    change ((w t : ℝ) : ℂ)=1
    have he : w t=1 := by
      calc
        w t = ∫ s, b s := by
          apply integral_congr_ae
          filter_upwards [] with s
          by_cases hs : b s=0
          · simp only [hs,zero_mul]
          · have ht : ((t-s : ℝ) : AddCircle (2*Real.pi)) ∈ V := by
              rw [AddCircle.coe_sub]
              exact hεK (-s) (by simpa only [abs_neg] using (hbe hs).trans hrε) _ hx
            have he := hq1 (subset_closure ht)
            change ql (t-s)=1 at he
            rw [he,mul_one]
        _ = 1 := SmoothRotationKernel.integral r hr
    rw [he,Complex.ofReal_one]
  let S : Set (AddCircle (2*Real.pi)) :=
    (fun z : ℝ × AddCircle (2*Real.pi) => z.2+(z.1 : AddCircle (2*Real.pi))) ''
      (Metric.closedBall 0 r ×ˢ tsupport q)
  have hSc : IsCompact S := ((isCompact_closedBall (0 : ℝ) r).prod hqc).image
    (continuous_snd.add (continuous_quotient_mk'.comp continuous_fst))
  have hSO : S ⊆ O := by
    rintro _ ⟨⟨s,x⟩,⟨hs,hx⟩,rfl⟩
    apply hδq s _ x hx
    exact (by simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hs : |s| ≤ r).trans_lt hrδ
  have hχS : tsupport χ.onCircle ⊆ S := by
    apply closure_minimal _ hSc.isClosed
    intro x hx
    by_contra hnot
    apply hx
    induction x using Quotient.inductionOn with | h t =>
    change ((w t : ℝ) : ℂ)=0
    have hz : w t=0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with s
      change b s * ql (t-s)=0
      by_cases hs : b s=0
      · simp only [hs,zero_mul]
      · have ht : ((t-s : ℝ) : AddCircle (2*Real.pi)) ∉ tsupport q := by
          intro ht
          apply hnot
          refine ⟨(s,((t-s : ℝ) : AddCircle (2*Real.pi))),⟨?_,ht⟩,?_⟩
          · simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using (hbe hs).le
          · change ((t-s : ℝ) : AddCircle (2*Real.pi))+(s : AddCircle (2*Real.pi))=t
            rw [← AddCircle.coe_add,sub_add_cancel]
        have he := image_eq_zero_of_notMem_tsupport ht
        change ql (t-s)=0 at he
        rw [he,mul_zero]
    rw [hz,Complex.ofReal_zero]
  exact ⟨χ,ofRealPeriodic_real _ _ _,hcut,hχS.trans hSO⟩
end StronglyRationalVOA.SmoothCircleFunction

open Set UniformSpace
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
lemma power_tsupport_circle_subset (f : SmoothCircleFunction) {k : ℕ} (hk : 0 < k) :
    tsupport (f.power k).onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change f t ^ k ≠ 0 at hx
  change f t ≠ 0
  exact fun h => hx (by rw [h,zero_pow (by omega)])
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma primary_real_entry_mem (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    (i j : Bool) : ClosedGraphData.entry (U.closedSmoothField hc a d f)
      (U.closedSmoothField_isClosed hc ha f) i j ∈ U.primaryAlgebra hc O := by
  have hq : A.IsQuasiPrimary a := hp 1 (by norm_num)
  by_cases hd1 : d=1
  · let F : U.PrimaryTestField := ⟨a,d,ha,hq,hh,f,hf,Or.inl hd1⟩
    exact LocalOperatorAlgebra.subset_generated _ ⟨F,hs,i,j,rfl⟩
  · have hd2 : 2 ≤ d := by omega
    let : Fact (0 < 2*Real.pi) := ⟨SmoothCircleFunction.period_pos⟩
    obtain ⟨χ,hχ,hχ1,hχO⟩ := SmoothCircleFunction.exists_real_cutoff isClosed_closure.isCompact hO hs
    have hcut (t : ℝ) (ht : f t ≠ 0) : χ t=1 := by
      have hm : (t : AddCircle (2*Real.pi)) ∈ Function.support f.onCircle := ht
      simpa only [SmoothCircleFunction.onCircle_coe,Pi.one_apply] using hχ1 (subset_closure hm)
    obtain ⟨C,g,hC,hg,hgχ,he⟩ := f.exists_even_power_difference χ hf hχ hcut (by omega : 0 < d-1)
    let F : U.PrimaryTestField := ⟨a,d,ha,hq,hh,(g.power 2).power (d-1),
      SmoothCircleFunction.power_real (SmoothCircleFunction.power_real hg 2) (d-1),
      Or.inr (Or.inr ⟨hp,hd2,g,hg,rfl⟩)⟩
    let G : U.PrimaryTestField := ⟨a,d,ha,hq,hh,(χ.power 2).power (d-1),
      SmoothCircleFunction.power_real (SmoothCircleFunction.power_real hχ 2) (d-1),
      Or.inr (Or.inr ⟨hp,hd2,χ,hχ,rfl⟩)⟩
    apply U.primary_difference_entry_mem hc F G rfl rfl f (C:ℂ) he hO _ _ i j
    · exact ((g.power 2).power_tsupport_circle_subset (by omega)).trans
        ((g.power_tsupport_circle_subset (by omega)).trans (hgχ.trans hχO))
    · exact ((χ.power 2).power_tsupport_circle_subset (by omega)).trans
        ((χ.power_tsupport_circle_subset (by omega)).trans hχO)
 

lemma primary_real_graph_invariant (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 0 < d)
    (f : SmoothCircleFunction) (hf : f.IsReal)
    {O : Set (AddCircle (2*Real.pi))} (hO : IsOpen O) (hs : tsupport f.onCircle ⊆ O)
    {Q : Completion V →L[ℂ] Completion V} (hQ : Q ∈ (U.primaryAlgebra hc O).commutant)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  apply ClosedGraphData.graph_invariant_of_entry_commutes _ (U.closedSmoothField_isClosed hc ha f) Q _ hxy
  intro i j
  exact ((VonNeumannAlgebra.mem_commutant_iff.mp hQ) _
    (U.primary_real_entry_mem hc ha hp hh hd f hf hO hs i j)).symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff in
def rePart (f : SmoothCircleFunction) : SmoothCircleFunction :=
  ofRealPeriodic (fun t => (f t).re) (fun t => congrArg Complex.re (f.periodic t))
    (Complex.reCLM.contDiff.comp f.smooth)
open scoped ContDiff in
def imPart (f : SmoothCircleFunction) : SmoothCircleFunction :=
  ofRealPeriodic (fun t => (f t).im) (fun t => congrArg Complex.im (f.periodic t))
    (Complex.imCLM.contDiff.comp f.smooth)
lemma rePart_real (f : SmoothCircleFunction) : f.rePart.IsReal := ofRealPeriodic_real _ _ _
lemma imPart_real (f : SmoothCircleFunction) : f.imPart.IsReal := ofRealPeriodic_real _ _ _
lemma rePart_support (f : SmoothCircleFunction) : tsupport f.rePart.onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change ((f t).re:ℂ) ≠ 0 at hx
  change f t ≠ 0
  intro h
  exact hx (by simp only [h,Complex.zero_re,Complex.ofReal_zero])
lemma imPart_support (f : SmoothCircleFunction) : tsupport f.imPart.onCircle ⊆ tsupport f.onCircle := by
  apply closure_mono
  intro x hx
  induction x using Quotient.inductionOn with | h t =>
  change ((f t).im:ℂ) ≠ 0 at hx
  change f t ≠ 0
  intro h
  exact hx (by simp only [h,Complex.zero_im,Complex.ofReal_zero])
lemma rePart_add_imPart (f : SmoothCircleFunction) (t : ℝ) :
    f t=f.rePart t+Complex.I*f.imPart t := by
  change f t=((f t).re:ℂ)+Complex.I*((f t).im:ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (f t)).symm
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma field_graph_invariant_add_smul (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (f g h : SmoothCircleFunction) (c : ℂ) (he : ∀ t, f t=g t+c*h t)
    (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ x : U.smoothEnergySpace, Q x ∈ U.smoothEnergySpace)
    (hg : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d g).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d g).graph)
    (hh : ∀ x y, (x,y) ∈ (U.closedSmoothField hc a d h).graph →
      (Q x,Q y) ∈ (U.closedSmoothField hc a d h).graph)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (Q x,Q y) ∈ (U.closedSmoothField hc a d f).graph := by
  let R := SymmetricOperator.restricted U.smoothEnergySpace Q hQ
  have hgc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha g.rapid_coefficients) Q hQ (U.closedSmoothField hc a d g)
    (U.smoothSmear_graph hc ha g.rapid_coefficients) hg
  have hhc := SymmetricOperator.restricted_commutes_of_graph U.smoothEnergySpace
    (U.smoothSmear hc ha h.rapid_coefficients) Q hQ (U.closedSmoothField hc a d h)
    (U.smoothSmear_graph hc ha h.rapid_coefficients) hh
  have he' : f=g.add (h.scale c) := SmoothCircleFunction.ext he
  have hfc : U.smoothSmear hc ha f.rapid_coefficients*R=R*U.smoothSmear hc ha f.rapid_coefficients := by
    rw [he',U.smoothSmear_add_functions,U.smoothSmear_scale,add_mul,mul_add,
      smul_mul_assoc,mul_smul_comm,hgc,hhc]
  have hce := U.smoothSmear_core hc ha f.rapid_coefficients
  change (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha f.rapid_coefficients)).closure =
    U.closedSmoothField hc a d f at hce
  rw [← hce] at hxy ⊢
  exact SymmetricOperator.onSubmodule_closure_graph_invariant _ _
    (U.smoothSmear_core_closable hc ha f.rapid_coefficients) Q hQ hfc hxy
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
