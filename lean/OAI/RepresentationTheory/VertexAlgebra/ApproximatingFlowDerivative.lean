import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.BoundedFlows

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma approximatingFlow_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (t : ℝ) (x : H) :
    HasDerivAt (fun s : ℝ => approximatingFlow T hs n s x)
      (approximatingFlow T hs n t (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x)) t := by
  exact BoundedFlow.flow_derivative _ t x

lemma approximatingFlow_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (n : ℕ) (x : H) : Continuous (fun t : ℝ => approximatingFlow T hs n t x) :=
  continuous_iff_continuousAt.mpr (fun t => (approximatingFlow_derivative T hs n t x).continuousAt)

lemma approximatingFlow_derivative_limit (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (t : ℝ) {x y : H} (hxy : (x,y) ∈ T.graph) :
    Tendsto (fun n : ℕ => approximatingFlow T hs n t
      (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x))
      atTop (𝓝 (flow T hs t (Complex.I • y))) := by
  have hz : Tendsto (fun n : ℕ => approximatingFlow T hs n t
      (Complex.I • (boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x-y))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n : ℕ => ‖boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x-y‖)
    · intro n
      rw [approximatingFlow_norm,norm_smul,Complex.norm_I,one_mul]
    · simpa only [sub_self,norm_zero] using ((boundedGenerator_strong T hs hxy).sub_const y).norm
  have h := hz.add (flow_tendsto T hs t (Complex.I • y))
  simpa only [smul_sub,map_sub,sub_add_cancel,zero_add] using h

lemma flow_integral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    (∫ s in 0..t, flow T hs s (Complex.I • y)) = flow T hs t x-x := by
  let F (n : ℕ) (s : ℝ) := approximatingFlow T hs n s
    (Complex.I • boundedGenerator T hs (sampleRadius n) (sampleRadius_ge n) x)
  have hc (n : ℕ) : Continuous (F n) := approximatingFlow_continuous T hs n _
  have hb (n : ℕ) (s : ℝ) : ‖F n s‖ ≤ ‖y‖ := by
    dsimp [F]
    rw [approximatingFlow_norm,norm_smul,Complex.norm_I,one_mul,
      regularizer_on_graph T hs _ _ hxy]
    simpa only [one_mul] using (regularizer T hs (sampleRadius n) (sampleRadius_ge n)).le_of_opNorm_le
      (regularizer_norm_le T hs _ _) y
  have hi := StrongLimit.intervalIntegral_tendsto hc hb
    (fun s => approximatingFlow_derivative_limit T hs s hxy) 0 t
  have he (n : ℕ) : (∫ s in 0..t, F n s) = approximatingFlow T hs n t x-x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => approximatingFlow_derivative T hs n s x) ((hc n).intervalIntegrable 0 t)
    simpa only [F,approximatingFlow,BoundedFlow.flow_zero,one_apply_eq_self] using h
  simp_rw [he] at hi
  exact tendsto_nhds_unique hi ((flow_tendsto T hs t x).sub_const x)

lemma flow_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s : ℝ => flow T hs s x) (flow T hs t (Complex.I • y)) t := by
  have hc := flow_continuous T hs (Complex.I • y)
  have he : (fun s : ℝ => flow T hs s x) =
      (fun s : ℝ => x+∫ r in 0..s, flow T hs r (Complex.I • y)) := by
    funext s
    rw [flow_integral T hs hxy s]
    abel
  rw [he]
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt).const_add x

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma apply_tendsto {ι : Type*} {l : Filter ι} (F : ι → H →L[ℂ] H) (A : H →L[ℂ] H)
    {C : ℝ} (hF : ∀ n, ‖F n‖ ≤ C)
    (hf : ∀ x, Tendsto (fun n => F n x) l (𝓝 (A x)))
    {v : ι → H} {x : H} (hv : Tendsto v l (𝓝 x)) :
    Tendsto (fun n => F n (v n)) l (𝓝 (A x)) := by
  have hz : Tendsto (fun n => F n (v n-x)) l (𝓝 0) := by
    apply squeeze_zero_norm (a := fun n => C*‖v n-x‖)
    · exact fun n => (F n).le_of_opNorm_le (hF n) _
    · simpa only [sub_self,norm_zero,mul_zero] using
        (tendsto_const_nhds.mul (hv.sub_const x).norm)
  have h := hz.add (hf x)
  simpa only [map_sub,sub_add_cancel,zero_add] using h

 

lemma hasDerivAt_apply {F : ℝ → H →L[ℂ] H} {g : ℝ → H} {g' z' : H} {t C : ℝ}
    (hF : ∀ s, ‖F s‖ ≤ C) (hc : ∀ x, ContinuousAt (fun s => F s x) t)
    (hg : HasDerivAt g g' t) (hz : HasDerivAt (fun s => F s (g t)) z' t) :
    HasDerivAt (fun s => F s (g s)) (F t g'+z') t := by
  rw [hasDerivAt_iff_tendsto_slope] at hg hz ⊢
  have ha := apply_tendsto F (F t) hF (fun x => (hc x).tendsto.mono_left nhdsWithin_le_nhds) hg
  have h := ha.add hz
  convert h using 1
  funext s
  simp only [slope, vsub_eq_sub]
  rw [show F s ((s-t)⁻¹ • (g s-g t)) = (s-t)⁻¹ • F s (g s-g t) from
    (F s |>.restrictScalars ℝ).map_smul _ _]
  rw [map_sub]
  module

end StronglyRationalVOA.StrongLimit

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma norm_le_exp_of_derivative_bound {f f' : ℝ → H} {C : ℝ}
    (hf : ∀ t, HasDerivAt f (f' t) t) (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) (t : ℝ) :
    ‖f t‖ ≤ ‖f 0‖*Real.exp (C*|t|) := by
  have hp {f f' : ℝ → H} (hf : ∀ t, HasDerivAt f (f' t) t)
      (hb : ∀ t, ‖f' t‖ ≤ C*‖f t‖) {t : ℝ} (ht : 0 ≤ t) :
      ‖f t‖ ≤ ‖f 0‖*Real.exp (C*t) := by
    have hc : Continuous f := continuous_iff_continuousAt.mpr (fun s => (hf s).continuousAt)
    have h := norm_le_gronwallBound_of_norm_deriv_right_le (K := C) (ε := 0) hc.continuousOn
      (fun s _ => (hf s).hasDerivWithinAt) (le_refl ‖f 0‖)
      (fun s _ => by simpa only [add_zero] using hb s) t (show t ∈ Set.Icc 0 t from ⟨ht,le_rfl⟩)
    simpa only [gronwallBound_ε0,sub_zero] using h
  by_cases ht : 0 ≤ t
  · simpa only [abs_of_nonneg ht] using hp hf hb ht
  · have hn : 0 ≤ -t := by linarith
    have hd (s : ℝ) : HasDerivAt (fun r => f (-r)) (-f' (-s)) s := by
      simpa only [neg_one_smul, Function.comp_def] using (hf (-s)).scomp s (hasDerivAt_neg s)
    have hb' (s : ℝ) : ‖-f' (-s)‖ ≤ C*‖f (-s)‖ := by simpa only [norm_neg] using hb (-s)
    simpa only [neg_neg,neg_zero,abs_of_neg (lt_of_not_ge ht)] using hp hd hb' hn

end StronglyRationalVOA.SymmetricOperator

open scoped Topology
open Filter
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma flow_opNorm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    ‖flow T hs t‖ ≤ 1 := by
  apply (flow T hs t).opNorm_le_bound zero_le_one
  intro x
  simp only [flow_norm,one_mul,le_refl]

lemma flow_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (t : ℝ) :
    (flow T hs t).adjoint = flow T hs (-t) := by
  have hi := ContinuousLinearMap.norm_map_iff_adjoint_comp_self (flow T hs t) |>.mp (flow_norm T hs t)
  have hi' : (flow T hs t).adjoint * flow T hs t = 1 := hi
  calc
    (flow T hs t).adjoint = (flow T hs t).adjoint * (flow T hs t*flow T hs (-t)) := by
      rw [← flow_add,add_neg_cancel,flow_zero,mul_one]
    _ = flow T hs (-t) := by rw [← mul_assoc,hi',one_mul]

lemma regularizer_flow_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F)
    (t : ℝ) (x : H) :
    ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖ := by
  have hSa : S.adjoint = S := hS
  have hd : S.comp F = -(F.adjoint.comp S) := by
    have ha := congrArg ContinuousLinearMap.adjoint hdef
    rw [map_sub,ContinuousLinearMap.adjoint_adjoint,ContinuousLinearMap.adjoint_comp,hSa] at ha
    rw [← ha,← hdef]
    abel
  have hx (x y : H) (hxy : (x,y) ∈ T.graph) :
      ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖ := by
    let q (s : ℝ) := flow T hs (-s) (S (flow T hs s x))
    let dq (s : ℝ) := Complex.I • flow T hs (-s) (F.adjoint (S (flow T hs s x)))
    have hder (s : ℝ) : HasDerivAt q (dq s) s := by
      have hg' := (S.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s (flow_derivative T hs hxy s)
      have hz : HasDerivAt (fun r : ℝ => flow T hs (-r) (S (flow T hs s x)))
          (-(flow T hs (-s) (Complex.I • E (flow T hs s x)))) s := by
        simpa only [neg_one_smul,Function.comp_def] using
          (flow_derivative T hs (hg (flow T hs s x)) (-s)).scomp s (hasDerivAt_neg s)
      have hp := StrongLimit.hasDerivAt_apply (F := fun r => flow T hs (-r))
        (fun r => flow_opNorm T hs (-r))
        (fun v => ((flow_continuous T hs v).comp continuous_neg).continuousAt) hg' hz
      have hgxy := flow_graph T hs s hxy
      have he : E.adjoint (flow T hs s x) = S (flow T hs s y) :=
        regularizer_adjoint hs.dense_domain S E hS hg (by rwa [show T.adjoint=T from hs])
      have hval := congrArg (fun A : H →L[ℂ] H => A (flow T hs s x)) hdef
      change E (flow T hs s x)-E.adjoint (flow T hs s x) = S (F (flow T hs s x)) at hval
      have hval' := congrArg (fun A : H →L[ℂ] H => A (flow T hs s x)) hd
      change S (F (flow T hs s x)) = -F.adjoint (S (flow T hs s x)) at hval'
      have heq : S (flow T hs s y)-E (flow T hs s x) = F.adjoint (S (flow T hs s x)) := by
        rw [he] at hval
        rw [hval'] at hval
        simpa only [neg_sub,neg_neg] using congrArg Neg.neg hval
      convert hp using 1
      · rfl
      · change Complex.I • flow T hs (-s) (F.adjoint (S (flow T hs s x))) =
          flow T hs (-s) (S (flow T hs s (Complex.I • y))) +
            -flow T hs (-s) (Complex.I • E (flow T hs s x))
        simp only [map_smul]
        rw [← sub_eq_add_neg,← smul_sub,← map_sub,heq]
    have hb (s : ℝ) : ‖dq s‖ ≤ ‖F‖*‖q s‖ := by
      dsimp only [dq,q]
      rw [norm_smul,Complex.norm_I,one_mul,flow_norm,flow_norm]
      simpa only [LinearIsometryEquiv.norm_map] using F.adjoint.le_opNorm (S (flow T hs s x))
    have hb' := norm_le_exp_of_derivative_bound hder hb t
    dsimp only [q] at hb'
    simpa only [flow_norm,neg_zero,flow_zero,one_apply_eq_self,mul_comm] using hb'
  have hdense : DenseRange T.domain.subtype := by simpa [DenseRange] using hs.dense_domain
  apply hdense.induction_on (p := fun x => ‖S (flow T hs t x)‖ ≤ Real.exp (‖F‖*|t|)*‖S x‖)
  · exact isClosed_le (S.continuous.comp (flow T hs t).continuous).norm
      (continuous_const.mul S.continuous.norm)
  · intro u
    exact hx u (T u) (T.mem_graph_iff.mpr ⟨u,rfl,rfl⟩)

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma flow_regularizer_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F) (t : ℝ) :
    ∃ B : H →L[ℂ] H, (flow T hs t).comp S = S.comp B ∧ ‖B‖ ≤ Real.exp (‖F‖*|t|) := by
  let L := (S.comp (flow T hs (-t))).toLinearMap
  let Q := L.extendOfNorm S.toLinearMap
  have hb (x : H) : ‖L x‖ ≤ Real.exp (‖F‖*|t|)*‖S.toLinearMap x‖ := by
    simpa only [L,ContinuousLinearMap.coe_coe,ContinuousLinearMap.comp_apply,abs_neg] using
      regularizer_flow_bound T hs S E F hS hg hdef (-t) x
  have hQ : Q.comp S = S.comp (flow T hs (-t)) := by
    ext x
    exact L.extendOfNorm_eq hSd ⟨_,hb⟩ x
  have hQa : S.comp Q.adjoint = (flow T hs t).comp S := by
    have h := congrArg ContinuousLinearMap.adjoint hQ
    simpa only [ContinuousLinearMap.adjoint_comp,show S.adjoint=S from hS,flow_adjoint,neg_neg] using h
  refine ⟨Q.adjoint,hQa.symm,?_⟩
  rw [LinearIsometryEquiv.norm_map]
  exact L.opNorm_extendOfNorm_le hSd (Real.exp_pos _).le hb

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.HilbertScale
variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

lemma inverseEnergy_dense (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) :
    DenseRange (inverseEnergy (G := G) h hh) := by
  apply finiteCore_dense.mono
  intro x hx
  refine ⟨coreDiagonal (fun i => (h i : ℂ)) ⟨x,hx⟩,?_⟩
  rw [show coreDiagonal (fun i => (h i : ℂ)) ⟨x,hx⟩ =
    (coreMultiplier (fun i => (h i : ℂ)) ⟨x,hx⟩ : Space G) from rfl,inverseEnergy_core]
  exact congrArg Subtype.val (coreMultiplier_inv_cancel h hh ⟨x,hx⟩)

omit [DecidableEq ι] in
lemma inverseEnergy_on_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    {x y : Space G} (hxy : (x,y) ∈ (diagonal (fun i => (h i : ℂ))).graph) :
    inverseEnergy h hh y = x := by
  obtain ⟨v,hv,hy⟩ := (diagonal (fun i => (h i : ℂ))).mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hv hy
  rw [← hy,inverseEnergy_diagonal,hv]

lemma flow_energy_graph (T : Space G →ₗ.[ℂ] Space G) (hs : IsSelfAdjoint T)
    (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (E F : Space G →L[ℂ] Space G)
    (hg : ∀ x, (inverseEnergy h hh x,E x) ∈ T.graph)
    (hdef : E-E.adjoint = (inverseEnergy h hh).comp F)
    (t : ℝ) {x y : Space G} (hxy : (x,y) ∈ (diagonal (fun i => (h i : ℂ))).graph) :
    ∃ z, (SymmetricOperator.flow T hs t x,z) ∈ (diagonal (fun i => (h i : ℂ))).graph ∧
      ‖z‖ ≤ Real.exp (‖F‖*|t|)*‖y‖ := by
  obtain ⟨B,hB,hbound⟩ := SymmetricOperator.flow_regularizer_factor T hs _ E F
    (inverseEnergy_selfAdjoint h hh) (inverseEnergy_dense h hh) hg hdef t
  refine ⟨B y,?_,B.le_of_opNorm_le hbound y⟩
  have he := congrArg (fun A : Space G →L[ℂ] Space G => A y) hB
  change SymmetricOperator.flow T hs t (inverseEnergy h hh y) = inverseEnergy h hh (B y) at he
  rw [inverseEnergy_on_graph h hh hxy] at he
  rw [he]
  exact inverseEnergy_graph h hh (B y)

end StronglyRationalVOA.HilbertScale

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

lemma physicalMode_power_commutator_bound {a : V} {d p : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    (r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)-A.physicalMode a d n ((A.energyShift^r) v)‖ ≤
      (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖ := by
  induction r generalizing v with
  | zero => simp only [pow_zero,Module.End.one_apply,sub_self,norm_zero,Nat.cast_zero,mul_zero,zero_mul,le_refl]
  | succ r ih =>
    have he : (A.energyShift^(r+1)) (A.physicalMode a d n v)-
          A.physicalMode a d n ((A.energyShift^(r+1)) v) =
        (-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)+
          ((A.energyShift^r) (A.physicalMode a d n (A.energyShift v))-
            A.physicalMode a d n ((A.energyShift^r) (A.energyShift v))) := by
      have hc := congrArg (A.energyShift^r) (A.energyShift_physical_commutator ha n v)
      rw [map_sub,map_smul] at hc
      simp only [pow_succ,Module.End.mul_apply]
      rw [← hc]
      abel
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hpower : (A.energyShift^r) (A.energyShift v) = (A.energyShift^(r+1)) v := by
      rw [pow_succ,Module.End.mul_apply]
    have hs := U.physicalMode_sobolev_bound (k := 1) ha hC (by simpa only [pow_one] using hb) r n v
    rw [Nat.add_comm 1 r] at hs
    have hbase : 1 ≤ 1+|(n : ℝ)| := by have := abs_nonneg (n : ℝ); linarith
    have hbase0 : 0 ≤ 1+|(n : ℝ)| := zero_le_one.trans hbase
    rw [he]
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖+
        ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))-
          A.physicalMode a d n ((A.energyShift^r) (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖)+
        (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖ := by
          rw [norm_smul,hn]
          exact add_le_add (mul_le_mul_of_nonneg_left hs (abs_nonneg _)) (by simpa only [hpower] using ih (A.energyShift v))
      _ ≤ (1+|(n : ℝ)|)*(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖)+
        (1+|(n : ℝ)|)*((C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(r+1)) v‖) := by
          apply add_le_add
          · gcongr; linarith
          · exact le_mul_of_one_le_left (by positivity) hbase
      _ = _ := by rw [Nat.cast_succ,show p+Nat.succ r=p+r+1 by omega,pow_succ]; ring

include U in
lemma energyShift_pow_adjoint (r : ℕ) (x y : V) :
    inner ℂ ((A.energyShift^r) x) y = inner ℂ x ((A.energyShift^r) y) := by
  induction r generalizing x y with
  | zero => simp only [pow_zero,Module.End.one_apply]
  | succ r ih =>
    rw [pow_succ,Module.End.mul_apply,ih,U.energyShift_adjoint,← Module.End.mul_apply,← pow_succ']
    rfl

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def smearedPowerCommutator {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) :
    V →ₗ[ℂ] Completion V :=
  U.weightedSmearedMap ha he hf r - (A.smearedMap a d he f hf).comp (A.energyShift^r)

lemma smearedPowerCommutator_apply {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    U.smearedPowerCommutator ha he hf r v =
      ∑' n : ℤ, f n • (((A.energyShift^r) (A.physicalMode a d n v)-
        A.physicalMode a d n ((A.energyShift^r) v) : V) : Completion V) := by
  simp only [smearedPowerCommutator,LinearMap.sub_apply,LinearMap.comp_apply,
    weightedSmearedMap_apply,smearedMap_apply]
  rw [← (U.summable_norm_sobolevSmear ha he hf r v).of_norm.tsum_sub
    (A.summable_norm_physicalSmear he d hf ((A.energyShift^r) v)).of_norm]
  apply tsum_congr
  intro n
  change f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) _ -
    f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) _ =
      f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (_-_)
  rw [map_sub,smul_sub]

lemma smearedPowerCommutator_bound {a : V} {d p : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    ‖U.smearedPowerCommutator ha he hf r v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*(C*r))*‖(A.energyShift^r) v‖ := by
  let D (n : ℤ) : V →ₗ[ℂ] Completion V :=
    (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n) - (A.physicalMode a d n).comp (A.energyShift^r))
  have hd (n : ℤ) : ‖D n v‖ ≤ (C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖ := by
    simpa only [D,LinearMap.comp_apply,LinearMap.sub_apply,LinearIsometry.coe_toLinearMap,
      LinearIsometry.norm_map] using U.physicalMode_power_commutator_bound ha hC hb r n v
  have hsum := hf.summable_norm_smul D v hd
  rw [U.smearedPowerCommutator_apply ha he hf r v]
  change ‖∑' n : ℤ, f n • D n v‖ ≤ _
  apply (norm_tsum_le_tsum_norm hsum).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^(p+r))*((C*r)*‖(A.energyShift^r) v‖) := by
      apply Summable.tsum_le_tsum _ hsum ((hf (p+r)).mul_right _)
      intro n
      rw [norm_smul]
      calc
        _ ≤ ‖f n‖*((C*r)*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^r) v‖) :=
          mul_le_mul_of_nonneg_left (hd n) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

lemma weightedSmearedMap_inner {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (x y : V) :
    inner ℂ (U.weightedSmearedMap ha he hf r x) (y : Completion V) =
      inner ℂ (A.smearedMap a d he f hf x) ((A.energyShift^r) y : Completion V) := by
  rw [weightedSmearedMap_apply,smearedMap_apply,
    inner_tsum_left (U.summable_norm_sobolevSmear ha he hf r x).of_norm,
    inner_tsum_left (A.summable_norm_physicalSmear he d hf x).of_norm]
  apply tsum_congr
  intro n
  simp only [inner_smul_left,Completion.inner_coe,U.energyShift_pow_adjoint]

lemma smearedPowerCommutator_pairing {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a) (he : A.PolynomialEnergyBound a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hreal : ∀ n, star (f n) = f (-n))
    (r : ℕ) (x y : V) :
    inner ℂ (A.smearedMap a d he f hf x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (A.smearedMap a d he f hf y) =
    inner ℂ (U.smearedPowerCommutator ha he hf r x) (y : Completion V) := by
  simp only [smearedPowerCommutator,LinearMap.sub_apply,LinearMap.comp_apply,inner_sub_left]
  rw [U.weightedSmearedMap_inner,U.smearedMap_symmetric ha hq hh he hf hreal ((A.energyShift^r) x) y]

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open scoped Topology
open Filter MeasureTheory
namespace StronglyRationalVOA.StrongLimit
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

lemma tendsto_of_denseRange {ι E : Type*} {l : Filter ι}
    (S : E → H) (hSd : DenseRange S) (F : ι → H →L[ℂ] H) (L : H →L[ℂ] H)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ᶠ i in l, ‖F i‖ ≤ C)
    (hcore : ∀ x, Tendsto (fun i => F i (S x)) l (𝓝 (L (S x)))) (x : H) :
    Tendsto (fun i => F i x) l (𝓝 (L x)) := by
  classical
  let G (i : ι) : H →L[ℂ] H := if ‖F i‖ ≤ C then F i else 0
  have hg : ∀ i, ‖G i‖ ≤ C := by
    intro i
    dsimp [G]
    split_ifs with hi
    · exact hi
    · simpa only [norm_zero] using hC
  have he : ∀ᶠ i in l, G i = F i := hF.mono fun i hi => ite_eq_left hi
  have hclosed := (equicontinuous_of_norm_bound G hg).isClosed_setOfPred_tendsto
    (l := l) L.continuous
  have hlim : Tendsto (fun i => G i x) l (𝓝 (L x)) := by
    apply hSd.induction_on (p := fun x => Tendsto (fun i => G i x) l (𝓝 (L x))) x hclosed
    intro v
    exact (hcore v).congr' (he.mono fun i hi => congrArg (fun Q : H →L[ℂ] H => Q (S v)) hi.symm)
  exact hlim.congr' (he.mono fun i hi => congrArg (fun Q : H →L[ℂ] H => Q x) hi)
end StronglyRationalVOA.StrongLimit

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma selfAdjoint_injective_of_denseRange (S : H →L[ℂ] H)
    (hS : IsSelfAdjoint S) (hSd : DenseRange S) : Function.Injective S := by
  apply S.toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  change S x = 0 at hx
  apply ext_inner_left ℂ
  intro y
  have he : ∀ y : H, inner ℂ y x = 0 := by
    intro y
    apply hSd.induction_on (p := fun y => inner ℂ y x = 0)
    · exact isClosed_eq (continuous_id.inner continuous_const) continuous_const
    · intro z
      rw [← ContinuousLinearMap.adjoint_inner_right]
      change inner ℂ z (S.adjoint x) = 0
      rw [show S.adjoint = S from hS,hx,inner_zero_right]
  simpa only [inner_zero_right] using he y

 

lemma regularizer_factor_continuous_zero (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|)) (x : H) :
    Tendsto (fun t => B t x) (𝓝 0) (𝓝 x) := by
  have ha (t : ℝ) : (B t).adjoint.comp S = S.comp (flow T hs (-t)) := by
    have h := congrArg ContinuousLinearMap.adjoint (hB t)
    rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
      show S.adjoint = S from hS,flow_adjoint] at h
    exact h.symm
  have hbound : ∀ᶠ t in 𝓝 (0 : ℝ), ‖(B t).adjoint‖ ≤ Real.exp K := by
    filter_upwards [Ioo_mem_nhds (show (-1 : ℝ)<0 by norm_num) (show (0 : ℝ)<1 by norm_num)] with t ht
    rw [LinearIsometryEquiv.norm_map]
    apply (hb t).trans
    apply Real.exp_le_exp.mpr
    have ht' : |t| ≤ 1 := abs_le.mpr ⟨ht.1.le,ht.2.le⟩
    nlinarith
  have hc (v : H) : Tendsto (fun t => (B t).adjoint (S v)) (𝓝 0) (𝓝 (S v)) := by
    have he (t : ℝ) : (B t).adjoint (S v) = S (flow T hs (-t) v) :=
      congrArg (fun Q : H →L[ℂ] H => Q v) (ha t)
    simp_rw [he]
    have h := S.continuous.continuousAt.tendsto.comp
      (((flow_continuous T hs v).comp continuous_neg).tendsto 0)
    simpa only [Function.comp_def,neg_zero,flow_zero,one_apply_eq_self] using h
  have hc' (v : H) : Tendsto (fun t => (B t).adjoint v) (𝓝 0) (𝓝 v) := by
    exact StrongLimit.tendsto_of_denseRange S hSd (fun t => (B t).adjoint) 1
      (Real.exp_pos K).le hbound (by simpa only [one_apply_eq_self] using hc) v
  have hip : Tendsto (fun t => (inner ℂ (B t x) x).re) (𝓝 0) (𝓝 (‖x‖^2)) := by
    have h : Tendsto (fun t => inner ℂ x ((B t).adjoint x)) (𝓝 0) (𝓝 (inner ℂ x x)) :=
      tendsto_const_nhds.inner (hc' x)
    have h' := Complex.continuous_re.continuousAt.tendsto.comp h
    have heq : (inner ℂ x x).re = ‖x‖^2 := by
      exact inner_self_eq_norm_sq (𝕜 := ℂ) x
    simpa only [Function.comp_def,ContinuousLinearMap.adjoint_inner_right,heq] using h'
  have hupper : Tendsto (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2+‖x‖^2-
      2*(inner ℂ (B t x) x).re) (𝓝 0) (𝓝 0) := by
    have he : Tendsto (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2) (𝓝 0) (𝓝 (‖x‖^2)) := by
      have hec : Continuous (fun t : ℝ => (Real.exp (K*|t|)*‖x‖)^2) := by fun_prop
      simpa only [abs_zero,mul_zero,Real.exp_zero,one_mul] using hec.tendsto (0 : ℝ)
    have hh := (he.add_const (‖x‖^2)).sub (hip.const_mul 2)
    have hz : ‖x‖^2+‖x‖^2-2*‖x‖^2 = 0 := by ring
    simpa only [hz] using hh
  have hsquare : Tendsto (fun t => ‖B t x-x‖^2) (𝓝 0) (𝓝 0) := by
    apply squeeze_zero (fun t => sq_nonneg _) _ hupper
    intro t
    rw [norm_sub_sq (𝕜 := ℂ)]
    change ‖B t x‖^2-2*(inner ℂ (B t x) x).re+‖x‖^2 ≤ _
    have hn := (B t).le_of_opNorm_le (hb t) x
    nlinarith [norm_nonneg (B t x), show 0 ≤ Real.exp (K*|t|)*‖x‖ by positivity]
  have hn : Tendsto (fun t => ‖B t x-x‖) (𝓝 0) (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn
end StronglyRationalVOA.SymmetricOperator

end

end OAI
