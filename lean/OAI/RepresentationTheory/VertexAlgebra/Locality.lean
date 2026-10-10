import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SmoothEnergyPower

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
namespace PrimaryTestField
variable {U}
lemma locality (F G : U.PrimaryTestField) (hc : A.toVertexAlgebra.C2Cofinite)
    (h : Disjoint (tsupport F.test) (tsupport G.test)) (i j k l : Bool) :
    ClosedGraphData.entry (F.field hc) (F.closed hc) i j *
      ClosedGraphData.entry (G.field hc) (G.closed hc) k l =
    ClosedGraphData.entry (G.field hc) (G.closed hc) k l *
      ClosedGraphData.entry (F.field hc) (F.closed hc) i j := by
  rcases F.kind with hw | ⟨hw,ha⟩ | ⟨hp,hd,b,hb,he⟩
  · obtain ⟨C,hC,hbound⟩ := U.current_linear_energyBound hc (hw ▸ F.homogeneous)
      F.quasiPrimary (hw ▸ F.hermitian)
    have HB : ∀ n v, ‖A.physicalMode F.state F.weight n v‖ ≤ C*(1+|(n:ℝ)|)^1*‖A.energyShift v‖ := by
      simpa only [hw,pow_one] using hbound
    exact (U.highField_firstOrder_graph_entries_commute hc G.homogeneous F.homogeneous
      G.quasiPrimary F.quasiPrimary G.hermitian F.hermitian hC.le HB
      G.real F.real h.symm k l i j).symm
  · change ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight F.test) _ i j * _ = _
    have H := U.highField_stress_graph_entries_commute hc G.homogeneous G.quasiPrimary
      G.hermitian G.real F.real h.symm k l i j
    simpa only [field,hw,ha] using H.symm
  · change ClosedGraphData.entry (U.closedSmoothField hc F.state F.weight F.test) _ i j * _ = _
    have hs : tsupport (b.power 2) = tsupport F.test := by
      rw [he,SmoothCircleFunction.power_tsupport_eq _ (by omega : 0 < F.weight-1)]
    have H := U.primary_power_graph_locality_of_localEstimate hc F.homogeneous G.homogeneous hp
      G.quasiPrimary F.hermitian G.hermitian hd (SmoothCircleFunction.power_real hb 2) G.real
      (by rwa [hs]) (U.primary_realSquare_localEnergy hc F.homogeneous hp F.hermitian hd hb) i j k l
    simpa only [field,he] using H
end PrimaryTestField
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Set
namespace StronglyRationalVOA.ProperCircleArc
lemma disjoint_complement (I : ProperCircleArc) : Disjoint I.carrier I.complement.carrier := by
  let : Fact (0 < 2*Real.pi) := ⟨SmoothCircleFunction.period_pos⟩
  apply Set.disjoint_left.mpr
  rintro x ⟨s,hs,rfl⟩ ⟨t,ht,he⟩
  have hs' : s ∈ Ico I.left (I.left+2*Real.pi) := ⟨hs.1.le,hs.2.trans I.nondense'⟩
  have ht' : t ∈ Ico I.left (I.left+2*Real.pi) :=
    ⟨I.nonempty'.le.trans ht.1.le,ht.2⟩
  have hst : t=s := (AddCircle.coe_eq_coe_iff_of_mem_Ico ht' hs').mp he
  have hlt : I.right < t := ht.1
  linarith [hs.2]
end StronglyRationalVOA.ProperCircleArc
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

def primaryGraphData (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : Set (Completion V →L[ℂ] Completion V) :=
  {x | ∃ F : U.PrimaryTestField, tsupport F.test.onCircle ⊆ O ∧ ∃ i j : Bool,
    x = ClosedGraphData.entry (F.field hc) (F.closed hc) i j}
lemma primaryGraphData_subset (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : U.primaryGraphData hc O ⊆ U.localGraphData hc O := by
  rintro x ⟨F,hF,i,j,rfl⟩
  exact ⟨F.state,F.weight,F.homogeneous,F.test,hF,i,j,rfl⟩
 

def primaryAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : VonNeumannAlgebra (Completion V) :=
  LocalOperatorAlgebra.generated (U.primaryGraphData hc O)
lemma primaryAlgebra_le_localAlgebra (hc : A.toVertexAlgebra.C2Cofinite)
    (O : Set (AddCircle (2*Real.pi))) : U.primaryAlgebra hc O ≤ U.localAlgebra hc O :=
  LocalOperatorAlgebra.generated_mono (U.primaryGraphData_subset hc O)
lemma primaryAlgebra_isotone (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (h : O ⊆ P) : U.primaryAlgebra hc O ≤ U.primaryAlgebra hc P := by
  apply LocalOperatorAlgebra.generated_mono
  rintro x ⟨F,hF,i,j,rfl⟩
  exact ⟨F,hF.trans h,i,j,rfl⟩
lemma primaryAlgebra_locality (hc : A.toVertexAlgebra.C2Cofinite)
    {O P : Set (AddCircle (2*Real.pi))} (h : Disjoint O P) :
    U.primaryAlgebra hc O ≤ (U.primaryAlgebra hc P).commutant := by
  apply (LocalOperatorAlgebra.generated_le_commutant_iff _ _).mpr
  rintro x ⟨F,hF,i,j,rfl⟩ y ⟨G,hG,k,l,rfl⟩
  have hFG := SmoothCircleFunction.disjoint_lift (h.mono hF hG)
  refine ⟨(F.locality G hc hFG i j k l).symm,?_⟩
  rw [ClosedGraphData.star_entry]
  exact (F.locality G hc hFG i j l k).symm
lemma primaryAlgebra_interval_locality (hc : A.toVertexAlgebra.C2Cofinite) (I : ProperCircleArc) :
    U.primaryAlgebra hc I.carrier ≤ (U.primaryAlgebra hc I.complement.carrier).commutant :=
  U.primaryAlgebra_locality hc I.disjoint_complement
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Set
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction
 

lemma exists_even_power_difference (f χ : SmoothCircleFunction)
    (hf : f.IsReal) (hχ : χ.IsReal)
    (hcut : ∀ t, f t ≠ 0 → χ t = 1) {k : ℕ} (hk : 0 < k) :
    ∃ (C : ℝ) (g : SmoothCircleFunction), 0 < C ∧ g.IsReal ∧
      tsupport g.onCircle ⊆ tsupport χ.onCircle ∧
      ∀ t, f t = (C : ℂ) * (((g.power 2).power k) t - ((χ.power 2).power k) t) := by
  let : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn f.smooth.continuous.continuousOn
  have hb (t : ℝ) : ‖f t‖ ≤ M := by
    let s := (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).val
    have hs : s ∈ Icc 0 (2*Real.pi) := by
      simpa only [s,mem_Icc,zero_add] using
        (⟨(AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).property.1,
        (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).property.2.le⟩ :
        (AddCircle.equivIco (2*Real.pi) 0 (t : AddCircle (2*Real.pi))).val ∈ Icc 0 (0+2*Real.pi))
    have he : f s = f t := by
      have H := congrArg f.onCircle (AddCircle.coe_equivIco (p := 2*Real.pi) (a := 0) (y := (t : AddCircle (2*Real.pi))))
      simpa only [onCircle_coe] using H
    rw [← he]
    exact hM s hs
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hb 0)
  let C := M+1
  have hC : 0 < C := by dsimp [C]; linarith
  have hp (t : ℝ) : 0 < 1 + (f t).re / C := by
    have hr := (Complex.abs_re_le_norm (f t)).trans (hb t)
    have hh : -(M+1) < (f t).re := by rw [abs_le] at hr; linarith [hr.1]
    have hj : -1 < (f t).re/C := by
      apply (lt_div_iff₀ hC).mpr
      simpa only [neg_one_mul] using hh
    linarith
  let r : ℝ → ℝ := fun t => (1+(f t).re/C) ^ ((2*k : ℕ) : ℝ)⁻¹
  have hrs : ContDiff ℝ ∞ r := by
    apply (contDiff_const.add ((Complex.reCLM.contDiff.comp f.smooth).div_const C)).rpow_const_of_ne
    exact fun t => (hp t).ne'
  have hrp : Function.Periodic r (2*Real.pi) := by
    intro t
    dsimp [r]
    rw [f.periodic t]
  let g := ofRealPeriodic (fun t => (χ t).re * r t)
    (fun t => by dsimp only; rw [χ.periodic t,hrp t])
    ((Complex.reCLM.contDiff.comp χ.smooth).mul hrs)
  have hg (t : ℝ) : g t = χ t * (r t : ℂ) := by
    change (((χ t).re * r t : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul]
    have he := congrArg (fun q : SmoothCircleFunction => q t) (real_reconstruct χ hχ)
    change ((χ t).re : ℂ) = χ t at he
    rw [he]
  refine ⟨C,g,hC,ofRealPeriodic_real _ _ _,?_,?_⟩
  · apply closure_mono
    intro x hx
    induction x using Quotient.inductionOn with | h t =>
    change g t ≠ 0 at hx
    change χ t ≠ 0
    intro ht
    apply hx
    rw [hg,ht,zero_mul]
  · intro t
    have hpw : r t ^ (2*k) = 1+(f t).re/C :=
      Real.rpow_inv_natCast_pow (hp t).le (by omega)
    have hrf : ((f t).re : ℂ) = f t := by
      have he := congrArg (fun q : SmoothCircleFunction => q t) (real_reconstruct f hf)
      exact he
    simp only [power_apply,hg,← pow_mul, mul_pow]
    by_cases hz : f t = 0
    · have hrz : r t = 1 := by simp [r,hz]
      simp [hz,hrz]
    · rw [hcut t hz,one_pow,one_mul]
      have hpw' : (r t : ℂ)^(2*k) = 1+f t/(C : ℂ) := by
        rw [← Complex.ofReal_pow,hpw,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_div,hrf]
      rw [hpw']
      have hc' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
      field_simp
      ring
end StronglyRationalVOA.SmoothCircleFunction

open Filter
open scoped Topology
namespace StronglyRationalVOA.HilbertScale
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]
 
def rotation (w : ι → ℝ) (t : ℝ) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => Complex.exp ((t*w i : ℝ)*Complex.I)) zero_le_one
    (fun _ => (Complex.norm_exp_ofReal_mul_I _).le)
@[simp] lemma rotation_apply (w : ι → ℝ) (t : ℝ) (x : Space G) (i : ι) :
    rotation w t x i = Complex.exp ((t*w i : ℝ)*Complex.I) • x i := rfl
lemma rotation_opNorm (w : ι → ℝ) (t : ℝ) : ‖rotation (G := G) w t‖ ≤ 1 :=
  boundedMultiplier_norm _ _ _
lemma rotation_zero (w : ι → ℝ) : rotation (G := G) w 0 = 1 := by
  ext x i
  simp [rotation_apply]
lemma rotation_add (w : ι → ℝ) (s t : ℝ) :
    rotation (G := G) w (s+t) = rotation w s * rotation w t := by
  ext x i
  simp only [mul_apply_eq_comp,rotation_apply,smul_smul]
  congr 1
  rw [add_mul,Complex.ofReal_add,add_mul,Complex.exp_add]
lemma rotation_adjoint (w : ι → ℝ) (t : ℝ) :
    (rotation (G := G) w t).adjoint = rotation w (-t) := by
  rw [rotation,boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply,rotation_apply,Complex.star_def,← Complex.exp_conj,
    map_mul,Complex.conj_ofReal,Complex.conj_I,neg_mul,Complex.ofReal_neg,mul_neg]
lemma rotation_norm (w : ι → ℝ) (t : ℝ) (x : Space G) :
    ‖rotation w t x‖ = ‖x‖ := by
  apply le_antisymm
  · exact ((rotation w t).le_opNorm x).trans (by
      simpa only [one_mul] using (mul_le_mul_of_nonneg_right (rotation_opNorm (G := G) w t) (norm_nonneg x)))
  · have hi : rotation w (-t) (rotation w t x) = x := by
      rw [← mul_apply_eq_comp,← rotation_add,neg_add_cancel,rotation_zero]
      rfl
    calc
      ‖x‖ = ‖rotation w (-t) (rotation w t x)‖ := congrArg norm hi.symm
      _ ≤ ‖rotation (G := G) w (-t)‖ * ‖rotation w t x‖ := (rotation (G := G) w (-t)).le_opNorm (rotation w t x)
      _ ≤ ‖rotation w t x‖ := by
        simpa only [one_mul] using (mul_le_mul_of_nonneg_right
          (rotation_opNorm (G := G) w (-t)) (norm_nonneg (rotation w t x)))
variable [DecidableEq ι]
lemma rotation_single (w : ι → ℝ) (t : ℝ) (i : ι) (x : G i) :
    rotation w t (lp.single 2 i x) = Complex.exp ((t*w i : ℝ)*Complex.I) • lp.single 2 i x :=
  boundedMultiplier_single _ _ _ _ _
lemma rotation_continuous (w : ι → ℝ) (x : Space G) :
    Continuous (fun t : ℝ => rotation w t x) := by
  have hc : ∀ x ∈ finiteCore (G := G), Continuous (fun t : ℝ => rotation w t x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i,v,rfl⟩ := hx
      have h : Continuous (fun t : ℝ => Complex.exp ((t*w i : ℝ)*Complex.I)) := by fun_prop
      convert h.smul (continuous_const (y := (lp.single 2 i v))) using 1
      funext t
      exact rotation_single w t i v
    | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : ℝ => (0 : Space G)))
    | add x y _ _ hx hy =>
      convert hx.add hy using 1
      funext t
      exact map_add _ _ _
    | smul c x _ hx =>
      convert hx.const_smul c using 1
      funext t
      exact map_smul _ _ _
  apply continuous_iff_continuousAt.mpr
  intro t
  apply StrongLimit.tendsto_of_denseRange (fun x : finiteCore (G := G) => x.val)
    (show DenseRange (fun x : finiteCore (G := G) => x.val) from by
      rw [denseRange_subtype_val]; exact finiteCore_dense)
    (rotation w) (rotation w t) zero_le_one (Eventually.of_forall (rotation_opNorm w))
  intro v
  exact (hc v v.property).continuousAt.tendsto
omit [DecidableEq ι] in
lemma rotation_graph (w : ι → ℝ) (v : ι → ℂ) (t : ℝ) {x y : Space G}
    (h : (x,y) ∈ (diagonal v).graph) :
    (rotation w t x,rotation w t y) ∈ (diagonal v).graph := by
  rw [mem_graph_iff] at h ⊢
  intro i
  simp only [rotation_apply,h i,smul_smul]
  rw [mul_comm]
end StronglyRationalVOA.HilbertScale

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance gradeFinite (d : ℕ) : FiniteDimensional ℂ (A.grade d) := A.grade_finite d
 
def rotation (t : ℝ) : Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((HilbertScale.rotation (fun d : ℕ => (d : ℝ)) t).comp
      U.energyCoordinates.toContinuousLinearEquiv.toContinuousLinearMap)
lemma rotation_coordinates (t : ℝ) (x : Completion V) :
    U.energyCoordinates (U.rotation t x) =
      HilbertScale.rotation (fun d : ℕ => (d : ℝ)) t (U.energyCoordinates x) := by
  simp only [rotation,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.apply_symm_apply]
lemma rotation_zero : U.rotation 0 = 1 := by
  ext x
  apply U.energyCoordinates.injective
  rw [U.rotation_coordinates,HilbertScale.rotation_zero]
  rfl
lemma rotation_add (s t : ℝ) : U.rotation (s+t) = U.rotation s * U.rotation t := by
  ext x
  apply U.energyCoordinates.injective
  simp only [mul_apply_eq_comp,U.rotation_coordinates,HilbertScale.rotation_add]
lemma rotation_norm (t : ℝ) (x : Completion V) : ‖U.rotation t x‖ = ‖x‖ := by
  rw [← U.energyCoordinates.norm_map (U.rotation t x),U.rotation_coordinates,
    HilbertScale.rotation_norm,U.energyCoordinates.norm_map]
lemma rotation_continuous (x : Completion V) : Continuous (fun t : ℝ => U.rotation t x) := by
  exact U.energyCoordinates.symm.continuous.comp (HilbertScale.rotation_continuous _ _)
lemma rotation_energy_graph (w : ℕ → ℝ) (t : ℝ) {x y : Completion V}
    (h : (x,y) ∈ (U.energyOperator w).graph) :
    (U.rotation t x,U.rotation t y) ∈ (U.energyOperator w).graph := by
  rw [energyOperator,OperatorTransport.mem_graph_iff] at h ⊢
  rw [U.rotation_coordinates,U.rotation_coordinates]
  exact HilbertScale.rotation_graph _ _ _ h
lemma rotation_grade (t : ℝ) {d : ℕ} (a : A.grade d) :
    U.rotation t (a.val : Completion V) = Complex.exp ((t*d : ℝ)*Complex.I) • (a.val : Completion V) := by
  apply U.energyCoordinates.injective
  rw [U.rotation_coordinates,map_smul,U.energyCoordinates_grade,HilbertScale.rotation_single]
lemma rotation_core (t : ℝ) {x : Completion V} (hx : x ∈ HilbertCore.space V) :
    U.rotation t x ∈ HilbertCore.space V := by
  rw [← U.finiteCore_comap_energyCoordinates] at hx ⊢
  change U.energyCoordinates (U.rotation t x) ∈ HilbertScale.finiteCore
  rw [U.rotation_coordinates]
  exact HilbertScale.boundedMultiplier_preservesFiniteCore _ _ _ (U.energyCoordinates x) hx
lemma rotation_smooth (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    U.rotation t x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  let v : (U.energyPower r).domain := ⟨x,hx r⟩
  have h := U.rotation_energy_graph (fun d => (1+(d : ℝ))^r) t
    ((U.energyPower r).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
  obtain ⟨v,hv,_⟩ := (U.energyPower r).mem_graph_iff.mp h
  change v.val = U.rotation t x at hv
  rw [← hv]
  exact v.property
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction
open MeasureTheory AddCircle
local instance : Fact (0 < 2*Real.pi) := ⟨period_pos⟩
 
def translate (f : SmoothCircleFunction) (t : ℝ) : SmoothCircleFunction :=
  ⟨fun s => f (s-t),fun s => by dsimp only; rw [show s+2*Real.pi-t=(s-t)+2*Real.pi by ring,f.periodic],
    f.smooth.comp (contDiff_id.sub contDiff_const)⟩
@[simp] lemma translate_apply (f : SmoothCircleFunction) (t s : ℝ) :
    f.translate t s = f (s-t) := rfl
lemma translate_real {f : SmoothCircleFunction} (hf : f.IsReal) (t : ℝ) :
    (f.translate t).IsReal := fun s => hf (s-t)
lemma translate_onCircle (f : SmoothCircleFunction) (t : ℝ) (s : AddCircle (2*Real.pi)) :
    (f.translate t).onCircle s = f.onCircle (s-(t : AddCircle (2*Real.pi))) := by
  induction s using QuotientAddGroup.induction_on
  rename_i s
  change f (s-t) = f.onCircle ((s : AddCircle (2*Real.pi))-(t : AddCircle (2*Real.pi)))
  rw [← QuotientAddGroup.mk_sub]
  rfl
lemma translate_coefficient (f : SmoothCircleFunction) (t : ℝ) (n : ℤ) :
    (f.translate t).coefficient n = Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*f.coefficient n := by
  rw [← fourierCoeff_toContinuousMap,← fourierCoeff_toContinuousMap]
  unfold fourierCoeff
  have ht := integral_add_right_eq_self (μ := (haarAddCircle : Measure (AddCircle (2*Real.pi))))
    (fun s : AddCircle (2*Real.pi) => fourier (-n) s • (f.translate t).toContinuousMap s)
    (t : AddCircle (2*Real.pi))
  rw [← ht]
  have hchar (s : AddCircle (2*Real.pi)) : fourier (-n) (s+(t : AddCircle (2*Real.pi))) =
      Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*fourier (-n) s := by
    rw [fourier_apply,smul_add,toCircle_add,Circle.coe_mul,← fourier_apply,← fourier_apply,
      fourier_coe_apply]
    have hpi : (2*(Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (ne_of_gt period_pos)
    rw [mul_comm]
    congr 1
    congr 1
    push_cast
    field_simp
  calc
    _ = ∫ s : AddCircle (2*Real.pi),
        Complex.exp (-((t*(n : ℝ) : ℝ)*Complex.I))*(fourier (-n) s • f.toContinuousMap s) ∂haarAddCircle := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro s
      dsimp only
      rw [hchar]
      change (Complex.exp _*fourier (-n) s)*(f.translate t).onCircle (s+(t : AddCircle (2*Real.pi))) = _
      rw [translate_onCircle,add_sub_cancel_right]
      simp only [smul_eq_mul,mul_assoc]
      rfl
    _ = _ := integral_const_mul _ _
end StronglyRationalVOA.SmoothCircleFunction

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_physicalMode_grade {a v : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade e) (m : ℤ) (t : ℝ) :
    U.rotation t (A.physicalMode a d m v : Completion V) =
      Complex.exp ((t*((e : ℝ)-(m : ℝ)) : ℝ)*Complex.I) • (A.physicalMode a d m v : Completion V) := by
  by_cases hm : (e : ℤ) < m
  · have hz : A.physicalMode a d m v = 0 := A.mode_eq_zero_of_negative_energy ha hv _ (by omega)
    rw [hz,Completion.coe_zero,map_zero,smul_zero]
  · have hmode : A.physicalMode a d m v ∈ A.grade ((e : ℤ)-m).toNat :=
      A.mode_mem_grade ha hv _ (by omega)
    rw [U.rotation_grade t ⟨_,hmode⟩]
    have he : (((e : ℤ)-m).toNat : ℝ) = (e : ℝ)-(m : ℝ) := by
      have he0 : (((e : ℤ)-m).toNat : ℤ) = (e : ℤ)-m := Int.toNat_of_nonneg (by omega)
      exact_mod_cast he0
    rw [he]
lemma rotation_smearedMap_grade (hc : A.toVertexAlgebra.C2Cofinite) {a v : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hv : v ∈ A.grade e) (f : SmoothCircleFunction) (t : ℝ) :
    U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v) =
      Complex.exp ((t*(e : ℝ) : ℝ)*Complex.I) •
        A.smearedMap a d (U.polynomialEnergyBounds hc a) (f.translate t).coefficient
          (f.translate t).rapid_coefficients v := by
  rw [A.smearedMap_apply,A.smearedMap_apply,
    (U.rotation t).map_tsum (A.summable_norm_physicalSmear (U.polynomialEnergyBounds hc a) d f.rapid_coefficients v).of_norm,
    ← tsum_const_smul'']
  apply tsum_congr
  intro m
  rw [map_smul,U.rotation_physicalMode_grade ha hv, SmoothCircleFunction.translate_coefficient,smul_smul,smul_smul]
  congr 1
  have he : Complex.exp ((t*((e : ℝ)-(m : ℝ)) : ℝ)*Complex.I) =
      Complex.exp ((t*(e : ℝ) : ℝ)*Complex.I)*Complex.exp (-((t*(m : ℝ) : ℝ)*Complex.I)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring
lemma rotation_smearedCore_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ) (v : V) :
    (U.rotation t (v : Completion V),
      U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v)) ∈
      (U.closedSmoothField hc a d (f.translate t)).graph := by
  apply A.homogeneous_induction (P := fun v =>
    (U.rotation t (v : Completion V),
      U.rotation t (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients v)) ∈
      (U.closedSmoothField hc a d (f.translate t)).graph)
  · simp only [Completion.coe_zero,map_zero]
    exact (U.closedSmoothField hc a d (f.translate t)).graph.zero_mem
  · intro e v hv
    rw [U.rotation_grade t ⟨v,hv⟩,U.rotation_smearedMap_grade hc ha hv]
    have hg : ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.translate t).coefficient (f.translate t).rapid_coefficients v) ∈
        (U.closedSmoothField hc a d (f.translate t)).graph := by
      apply LinearPMap.le_graph_of_le (U.smoothSmearedField hc a d (f.translate t)).le_closure
      exact (U.smoothSmearedField hc a d (f.translate t)).mem_graph_iff.mpr
        ⟨HilbertCore.equiv V v,rfl,HilbertCore.operator_apply _ v⟩
    exact (U.closedSmoothField hc a d (f.translate t)).graph.smul_mem _ hg
  · intro x y hx hy
    simp only [Completion.coe_add,map_add]
    exact (U.closedSmoothField hc a d (f.translate t)).graph.add_mem hx hy
 
lemma rotation_closedSmoothField_graph (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    (U.rotation t x,U.rotation t y) ∈ (U.closedSmoothField hc a d (f.translate t)).graph := by
  have hclosed : IsClosed {p : Completion V × Completion V |
      (U.rotation t p.1,U.rotation t p.2) ∈ (U.closedSmoothField hc a d (f.translate t)).graph} :=
    (U.closedSmoothField_isClosed hc ha (f.translate t)).preimage
      (((U.rotation t).continuous.comp continuous_fst).prodMk
        ((U.rotation t).continuous.comp continuous_snd))
  change (x,y) ∈ ((U.closedSmoothField hc a d f).graph : Set _) at hxy
  rw [U.closedSmoothField_graph hc ha f] at hxy
  apply (closure_minimal (s := ((U.smoothSmearedField hc a d f).graph : Set _)) ?_ hclosed) hxy
  rintro p hp
  obtain ⟨v,hv,hy⟩ := (U.smoothSmearedField hc a d f).mem_graph_iff.mp hp
  obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective v
  obtain rfl : p = ((v : Completion V),A.smearedMap a d (U.polynomialEnergyBounds hc a)
      f.coefficient f.rapid_coefficients v) := by
    ext
    · exact hv.symm
    · exact hy.symm.trans (HilbertCore.operator_apply _ v)
  exact U.rotation_smearedCore_graph hc ha f t v
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
namespace StronglyRationalVOA.SmoothCircleFunction
@[simp] lemma translate_zero (f : SmoothCircleFunction) : f.translate 0 = f := by
  ext s
  simp only [translate_apply,sub_zero]
lemma translate_add (f : SmoothCircleFunction) (s t : ℝ) :
    (f.translate s).translate t = f.translate (s+t) := by
  ext r
  simp only [translate_apply]
  congr 1
  ring
end StronglyRationalVOA.SmoothCircleFunction
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma rotation_inverse (t : ℝ) (x : Completion V) : U.rotation (-t) (U.rotation t x) = x := by
  rw [← mul_apply_eq_comp,← U.rotation_add,neg_add_cancel,U.rotation_zero]
  rfl
lemma rotation_closedSmoothField_graph_iff (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (f : SmoothCircleFunction) (t : ℝ) (x y : Completion V) :
    (U.rotation t x,U.rotation t y) ∈ (U.closedSmoothField hc a d (f.translate t)).graph ↔
      (x,y) ∈ (U.closedSmoothField hc a d f).graph := by
  constructor
  · intro h
    have h' := U.rotation_closedSmoothField_graph hc ha (f.translate t) (-t) h
    simpa only [SmoothCircleFunction.translate_add,add_neg_cancel,SmoothCircleFunction.translate_zero,
      U.rotation_inverse] using h'
  · exact U.rotation_closedSmoothField_graph hc ha f t
lemma rotation_inner (t : ℝ) (x y : Completion V) :
    inner ℂ (U.rotation t x) (U.rotation t y) = inner ℂ x y := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  rw [← U.energyCoordinates.inner_map_map (U.rotation t x) (U.rotation t y),
    U.rotation_coordinates,U.rotation_coordinates,← ContinuousLinearMap.adjoint_inner_right,
    HilbertScale.rotation_adjoint,← mul_apply_eq_comp,← HilbertScale.rotation_add,neg_add_cancel,
    HilbertScale.rotation_zero,one_apply_eq_self,U.energyCoordinates.inner_map_map]
lemma rotation_adjoint (t : ℝ) : (U.rotation t).adjoint = U.rotation (-t) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  have h := U.rotation_inner t (U.rotation (-t) x) y
  rw [show U.rotation t (U.rotation (-t) x) = x by simpa only [neg_neg] using U.rotation_inverse (-t) x] at h
  exact h.symm
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.ClosedGraphData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma coordinate_ext {x y : Double H} (h : ∀ i, coordinate i x = coordinate i y) : x=y := by
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ H H).injective
  exact Prod.ext (h false) (h true)
omit [CompleteSpace H] in
lemma inclusion_coordinate_sum (x : Double H) :
    inclusion false (coordinate false x) + inclusion true (coordinate true x) = x := by
  apply coordinate_ext
  intro i
  cases i <;> simp [coordinate,inclusion]
lemma projection_commutes_of_entry_commutes (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (Q : H →L[ℂ] H) (hQ : ∀ i j, Q * entry T hT i j = entry T hT i j * Q) :
    (diagonalAction Q).comp (projection T hT) = (projection T hT).comp (diagonalAction Q) := by
  apply ContinuousLinearMap.ext
  intro x
  apply coordinate_ext
  intro i
  have he (j : Bool) := congrArg (fun L : H →L[ℂ] H => L (coordinate j x)) (hQ i j)
  have h1 := he false
  have h2 := he true
  have hde (j : Bool) : diagonalAction Q (inclusion j (coordinate j x)) =
      inclusion j (Q (coordinate j x)) := by
    exact congrArg (fun L : H →L[ℂ] Double H => L (coordinate j x)) (diagonalAction_inclusion Q j)
  have hc : coordinate i (diagonalAction Q (projection T hT x)) =
      Q (coordinate i (projection T hT x)) := by
    exact congrArg (fun L : Double H →L[ℂ] H => L (projection T hT x)) (coordinate_diagonalAction Q i)
  change coordinate i (diagonalAction Q (projection T hT x)) =
    coordinate i (projection T hT (diagonalAction Q x))
  rw [hc]
  conv_lhs => rw [← inclusion_coordinate_sum x]
  conv_rhs => rw [← inclusion_coordinate_sum x]
  simp only [map_add,hde]
  exact congrArg₂ (·+·) h1 h2
end StronglyRationalVOA.ClosedGraphData

end

end OAI
