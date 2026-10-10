import OAI.RepresentationTheory.VertexAlgebra.MobiusStandardAction

namespace OAI

noncomputable section
open Set Filter
open scoped MatrixGroups Topology ContDiff
namespace StronglyRationalVOA.CircleMobiusGeometry
lemma continuous_entry (i j : Fin 2) : Continuous (fun M : SL(2,ℝ) => M i j) :=
  (continuous_apply_apply i j).comp continuous_subtype_val
lemma constant_continuous : Continuous constant := by
  change Continuous (fun M : SL(2,ℝ) => (M 0 0^2+M 0 1^2+M 1 0^2+M 1 1^2)/2)
  fun_prop
lemma cosine_continuous : Continuous cosine := by
  change Continuous (fun M : SL(2,ℝ) => (M 1 0^2+M 1 1^2-M 0 0^2-M 0 1^2)/2)
  fun_prop
lemma sine_continuous : Continuous sine := by
  change Continuous (fun M : SL(2,ℝ) => -(M 0 0*M 1 0+M 0 1*M 1 1))
  fun_prop
lemma density_smooth_standard (M : SL(2,ℝ)) : ContDiff ℝ ∞ (density M) := by
  simp only [funext (density_trigonometric M)]
  exact (contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).add
    (contDiff_const.mul Real.contDiff_sin)
lemma density_derivative_continuous (k : ℕ) :
    Continuous (fun p : SL(2,ℝ) × ℝ => iteratedDeriv k (density p.1) p.2) := by
  have he (M : SL(2,ℝ)) (x : ℝ) : iteratedDeriv k (density M) x=
      (if k=0 then constant M else 0)+cosine M*iteratedDeriv k Real.cos x+
        sine M*iteratedDeriv k Real.sin x := by
    rw [funext (density_trigonometric M)]
    change iteratedDeriv k ((fun x => constant M+cosine M*Real.cos x) +
      (fun x => sine M*Real.sin x)) x = _
    rw [iteratedDeriv_add (n := k) (x := x) (f := fun x => constant M+cosine M*Real.cos x) (g := fun x => sine M*Real.sin x) ((contDiff_const.add (contDiff_const.mul Real.contDiff_cos)).contDiffAt)
      (contDiff_const.mul Real.contDiff_sin).contDiffAt]
    change iteratedDeriv k ((fun _ => constant M)+(fun x => cosine M*Real.cos x)) x+
      iteratedDeriv k (fun x => sine M*Real.sin x) x = _
    rw [iteratedDeriv_add (n := k) (x := x) (f := fun _ => constant M) (g := fun x => cosine M*Real.cos x) contDiff_const.contDiffAt (contDiff_const.mul Real.contDiff_cos).contDiffAt]
    rw [iteratedDeriv_const_mul _ Real.contDiff_cos.contDiffAt,
      iteratedDeriv_const_mul _ Real.contDiff_sin.contDiffAt,iteratedDeriv_const]
  simp only [he]
  exact (((constant_continuous.comp continuous_fst).if_const _ continuous_const).add
    ((cosine_continuous.comp continuous_fst).mul
      (((Real.contDiff_cos (n := ∞)).continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))).comp continuous_snd))).add
    ((sine_continuous.comp continuous_fst).mul
      (((Real.contDiff_sin (n := ∞)).continuous_iteratedDeriv k (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))).comp continuous_snd))
 

lemma continuous_of_implements {P : Type*} [TopologicalSpace P] (M : P → SL(2,ℝ))
    (F : P → SmoothCircleLift) (hM : Continuous M)
    (hF : Continuous (fun p : P × ℝ => F p.1 p.2))
    (hrel : ∀ p, Implements (M p) (F p)) : Continuous F := by
  have hj (k : ℕ) : Continuous (fun p : P × ℝ => iteratedDeriv k (F p.1) p.2) := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      cases k with
      | zero => exact hF
      | succ k =>
        have he (p : P × ℝ) : iteratedDeriv (k+1) (F p.1) p.2=
            ∑ c : OrderedFinpartition k,
              iteratedDeriv c.length (density (M p.1)) (F p.1 p.2)*
                ∏ j, iteratedDeriv (c.partSize j) (F p.1) p.2 := by
          rw [iteratedDeriv_succ']
          have hd : deriv (F p.1)=density (M p.1) ∘ (F p.1) :=
            funext (derivative_density (M p.1) (F p.1) (hrel p.1))
          rw [hd]
          exact iteratedDeriv_comp_eq_sum_orderedFinpartition
            (density_smooth_standard _).contDiffAt (F p.1).smooth.contDiffAt (by exact_mod_cast (le_top : (k:ℕ∞)≤⊤))
        simp only [he]
        apply continuous_finsetSum
        intro c _
        apply Continuous.mul
        · exact (density_derivative_continuous c.length).comp
            ((hM.comp continuous_fst).prodMk hF)
        · apply continuous_finsetProd
          intro j _
          exact ih _ (Nat.lt_succ_of_le (c.partSize_le j))
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro k
  exact ContinuousMap.continuous_of_continuous_uncurry _ (hj k)

 

def positiveMatrices : Set (SL(2,ℝ)) := {M | ∀ x, 0 < dot M x}
lemma positiveLift_continuous : Continuous (fun M : positiveMatrices => positiveLift M M.property) := by
  apply continuous_of_implements (fun M : positiveMatrices => M.val) _ continuous_subtype_val _
    (fun M => implements_positiveLift M M.property)
  change Continuous (fun p : positiveMatrices × ℝ => positiveLiftFun p.1 p.2)
  dsimp only [positiveLiftFun]
  apply continuous_snd.add
  apply continuous_const.mul
  apply Real.continuous_arctan.comp
  apply Continuous.div
  · dsimp only [cross]
    fun_prop
  · dsimp only [dot]
    fun_prop
  · intro p; exact (p.1.property p.2).ne'
lemma dot_continuous : Continuous (fun p : SL(2,ℝ) × ℝ => dot p.1 p.2) := by
  dsimp only [dot]
  fun_prop
lemma dot_periodic (M : SL(2,ℝ)) : Function.Periodic (dot M) (2*Real.pi) := by
  intro x
  dsimp only [dot]
  rw [show (x+2*Real.pi)/2=x/2+Real.pi by ring,Real.cos_add_pi,Real.sin_add_pi]
  ring
lemma dot_one (x : ℝ) : dot (1:SL(2,ℝ)) x=1 := by
  simp only [dot,Matrix.SpecialLinearGroup.coe_one,Matrix.one_apply]
  norm_num only [Fin.zero_eta,Fin.isValue,show (0:Fin 2) ≠ 1 by decide,
    show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false,one_mul,zero_mul,add_zero,zero_add]
  nlinarith [cos_sq_add_sin_sq (x/2)]
lemma one_mem_positiveMatrices : (1:SL(2,ℝ)) ∈ positiveMatrices := by
  intro x; rw [dot_one]; norm_num
lemma positiveMatrices_mem_nhds_one : positiveMatrices ∈ 𝓝 (1:SL(2,ℝ)) := by
  have hh : ∀ᶠ M : SL(2,ℝ) in 𝓝 1, ∀ x ∈ Icc (0:ℝ) (2*Real.pi), 0 < dot M x := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro x _
    apply (isOpen_lt continuous_const dot_continuous).mem_nhds
    simp [dot_one]
  filter_upwards [hh] with M hM
  intro x
  let n : ℤ := ⌊x/(2*Real.pi)⌋
  have hp : 0 < 2*Real.pi := by positivity
  have hlow := mul_le_mul_of_nonneg_right (Int.floor_le (x/(2*Real.pi))) hp.le
  have hupp := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x/(2*Real.pi))) hp
  rw [div_mul_cancel₀ _ hp.ne'] at hlow hupp
  have hin : x-(n:ℝ)*(2*Real.pi) ∈ Icc (0:ℝ) (2*Real.pi) := by
    change (n:ℝ)*(2*Real.pi) ≤ x at hlow
    change x < ((n:ℝ)+1)*(2*Real.pi) at hupp
    constructor <;> linarith
  have he := (dot_periodic M).sub_int_mul_eq (x := x) n
  rw [← he]
  exact hM _ hin
lemma standardAction_continuousAt_one : ContinuousAt standardAction 1 := by
  have hc : Continuous (positiveMatrices.domRestrict standardAction) := by
    have he : positiveMatrices.domRestrict standardAction =
        (fun M : positiveMatrices => QuotientGroup.mk
          (⟨positiveLift M M.property, M, implements_positiveLift M M.property⟩ : lifts)) := by
      funext M
      exact standardAction_eq_mk (implements_positiveLift M M.property)
    rw [he]
    exact (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous.comp
      (positiveLift_continuous.subtype_mk _)
  exact ((continuousWithinAt_iff_continuousAt_domRestrict standardAction one_mem_positiveMatrices).mpr
    hc.continuousAt).continuousAt positiveMatrices_mem_nhds_one
lemma group_continuous_mul_right (G : Group) : Continuous (fun F : Group => F*G) := by
  induction G using QuotientGroup.induction_on with
  | H G =>
    apply (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous_iff.mpr
    exact (QuotientGroup.isQuotientMap_mk (SmoothCircleLift.circleAction.comp lifts.subtype).ker).continuous.comp
      (((SmoothCircleLift.continuous_mul_right (G:SmoothCircleLift)).comp continuous_subtype_val).subtype_mk _)
 

lemma standardAction_continuous : Continuous standardAction := by
  apply continuous_iff_continuousAt.mpr
  intro M
  have hnear : Tendsto (fun N : SL(2,ℝ) => N*M⁻¹) (𝓝 M) (𝓝 1) := by
    simpa using (continuous_mul_const M⁻¹).tendsto M
  have h := standardAction_continuousAt_one.tendsto.comp hnear
  have hpost := (group_continuous_mul_right (standardAction M)).tendsto (standardAction 1)
  have H := hpost.comp h
  change Tendsto standardAction (𝓝 M) (𝓝 (standardAction M))
  simpa only [Function.comp_def,map_mul,map_inv,map_one,one_mul,mul_assoc,inv_mul_cancel,mul_one] using H
lemma projectiveStandardAction_continuous : Continuous projectiveStandardAction := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center (SL(2,ℝ)))).continuous_iff.mpr
  exact standardAction_continuous
end StronglyRationalVOA.CircleMobiusGeometry

end

end OAI
