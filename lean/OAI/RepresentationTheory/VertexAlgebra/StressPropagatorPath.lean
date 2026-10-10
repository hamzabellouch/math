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
open UniformSpace Set Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressPropagator_path_difference (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : StressPath) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2 ≤ ε)
    (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc g t x-U.stressPropagator hc f t x‖ ≤
      (ε*(1+A.centralCharge.re))*Real.exp ((g.bound 3*(1+A.centralCharge.re))*|t|)*
        ‖U.smoothEnergyPower 1 x‖*|t| := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hB := mul_nonneg hε hC
  have hb (p : StressPath) (n : ℕ) : 0 ≤ (p.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) :=
    mul_nonneg (mul_nonneg (p.bound_nonneg 2) hC) (by positivity)
  apply le_of_tendsto ((U.stressPropagator_limit hc g t x).sub
    (U.stressPropagator_limit hc f t x)).norm
  apply Filter.Eventually.of_forall
  intro n
  apply TimeOrdered.duhamel_bound
    (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (U.stressCutoff_continuous hc n g.rapid g.continuous)
    (hb f n) (hb g n) (U.stressPath_cutoff_bound hc f n)
    (U.stressPath_cutoff_bound hc g n)
    (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
  intro s hs
  let y := U.stressCutoffEvolutionSmooth hc g n s x
  have hn : ‖(U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s))*U.inverseSobolev 1‖ ≤
      ε*(1+A.centralCharge.re) := by
    calc
      _ ≤ coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2*
          (1+A.centralCharge.re) := by
        rw [sub_mul,U.stressCutoff_normalized hc n (g.rapid s) le_rfl,
          U.stressCutoff_normalized hc n (f.rapid s) le_rfl,
          ← smul_sub,← sub_mul,← mul_sub,norm_smul,Complex.norm_I,one_mul]
        calc
          _ ≤ (‖U.energyCutoff n‖*
              ‖U.stressNormalized hc (g.rapid s) 1-U.stressNormalized hc (f.rapid s) 1‖)*
              ‖U.energyCutoff n‖ :=
            (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          _ ≤ (1*‖U.stressNormalized hc (g.rapid s) 1-
              U.stressNormalized hc (f.rapid s) 1‖)*1 := by
            gcongr <;> exact U.energyCutoff_norm n
          _ ≤ _ := by
            simpa only [one_mul,mul_one] using
              U.stressNormalized_difference hc (g.rapid s) (f.rapid s) le_rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right (hd s hs) hC
  have h1 : ‖(U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s)) y‖ ≤
      (ε*(1+A.centralCharge.re))*‖U.smoothEnergyPower 1 y‖ := by
    rw [← U.inverseSobolev_smoothEnergyPower 1 y]
    exact ((U.stressCutoff hc n (g.rapid s)-U.stressCutoff hc n (f.rapid s))*U.inverseSobolev 1).le_of_opNorm_le hn _
  have hst : |s| ≤ |t| := by
    rcases le_total 0 t with ht | ht
    · rw [uIcc_of_le ht] at hs
      rw [abs_of_nonneg hs.1,abs_of_nonneg ht]
      exact hs.2
    · rw [uIcc_of_ge ht] at hs
      rw [abs_of_nonpos hs.2,abs_of_nonpos ht]
      exact neg_le_neg hs.1
  have h2 : ‖U.smoothEnergyPower 1 y‖ ≤
      Real.exp ((g.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 x‖ := by
    apply (U.stressCutoffEvolutionSmooth_bound hc g le_rfl n s x).trans
    simp only [Nat.cast_one,mul_one]
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hst (mul_nonneg (g.bound_nonneg 3) hC))) (norm_nonneg _)
  exact (h1.trans (mul_le_mul_of_nonneg_left h2 hB)).trans_eq (by ring)
 

lemma stressPropagator_path_tendsto (hc : A.toVertexAlgebra.C2Cofinite)
    {ι : Type*} {l : Filter ι} (f : StressPath) (g : ι → StressPath) (t : ℝ)
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hε0 : Tendsto ε l (𝓝 0))
    {K : ℝ} (hK : ∀ᶠ i in l, (g i).bound 3 ≤ K)
    (hd : ∀ᶠ i in l, ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => (g i).coefficients s k-f.coefficients s k) 2 ≤ ε i)
    (x : Completion V) :
    Tendsto (fun i => U.stressPropagator hc (g i) t x) l (𝓝 (U.stressPropagator hc f t x)) := by
  apply StrongLimit.tendsto_of_denseRange (fun y : U.smoothEnergySpace => (y : Completion V))
    U.smoothEnergySpace_dense.denseRange_val (fun i => U.stressPropagator hc (g i) t)
    (U.stressPropagator hc f t) (C := 1) (by norm_num) _ _ x
  · exact Filter.Eventually.of_forall (fun i => (U.stressPropagator hc (g i) t).opNorm_le_bound (by norm_num)
      (fun vector => by simpa only [one_mul] using
        (ContinuousLinearMap.norm_map_of_mem_unitary
          (U.stressPropagator_unitary hc (g i) t) vector).le))
  intro y
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun i => (ε i*(1+A.centralCharge.re))*
      Real.exp ((K*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 y‖*|t|) l (𝓝 0) := by
    simpa only [zero_mul] using (((hε0.mul_const (1+A.centralCharge.re)).mul_const
      (Real.exp ((K*(1+A.centralCharge.re))*|t|))).mul_const ‖U.smoothEnergyPower 1 y‖).mul_const |t|
  apply squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) _ hz
  filter_upwards [hK,hd] with i hi he
  apply (U.stressPropagator_path_difference hc f (g i) t (hε i) he y).trans
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  gcongr
  exact mul_nonneg (hε i) hC
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure


end

end OAI
