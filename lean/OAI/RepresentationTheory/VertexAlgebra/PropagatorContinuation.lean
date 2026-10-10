import OAI.RepresentationTheory.VertexAlgebra.GeometryContinuation

namespace OAI

noncomputable section
open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

lemma stressPropagator_path_difference_fixed (hc : A.toVertexAlgebra.C2Cofinite)
    (f g : StressPath) (t : ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hd : ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => g.coefficients s k-f.coefficients s k) 2 ≤ ε)
    (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc g t x-U.stressPropagator hc f t x‖ ≤
      (ε*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*
        ‖U.smoothEnergyPower 1 x‖*|t| := by
  rw [norm_sub_rev]
  apply U.stressPropagator_path_difference hc g f t hε
  intro s hs
  convert hd s hs using 1
  unfold coefficientSeminorm
  congr 1
  funext k
  rw [norm_sub_rev]

 
lemma stressPropagator_path_tendsto_fixed (hc : A.toVertexAlgebra.C2Cofinite)
    {ι : Type*} {l : Filter ι} (f : StressPath) (g : ι → StressPath) (t : ℝ)
    (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) (hε0 : Tendsto ε l (𝓝 0))
    (hd : ∀ᶠ i in l, ∀ s ∈ uIcc (0:ℝ) t,
      coefficientSeminorm (fun k => (g i).coefficients s k-f.coefficients s k) 2 ≤ ε i)
    (x : Completion V) :
    Tendsto (fun i => U.stressPropagator hc (g i) t x) l (𝓝 (U.stressPropagator hc f t x)) := by
  apply StrongLimit.tendsto_of_denseRange (fun y : U.smoothEnergySpace => (y : Completion V))
    U.smoothEnergySpace_dense.denseRange_val (fun i => U.stressPropagator hc (g i) t)
    (U.stressPropagator hc f t) (C := 1) (by norm_num) _ _ x
  · exact Filter.Eventually.of_forall (fun i => (U.stressPropagator hc (g i) t).opNorm_le_bound (by norm_num)
      (fun y => by simpa only [one_mul,U.stressPropagatorEquiv_apply] using (U.stressPropagatorEquiv hc (g i) t).norm_map y |>.le))
  intro y
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hz : Tendsto (fun i => (ε i*(1+A.centralCharge.re))*
      Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 y‖*|t|) l (𝓝 0) := by
    simpa only [zero_mul] using (((hε0.mul_const (1+A.centralCharge.re)).mul_const
      (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|))).mul_const ‖U.smoothEnergyPower 1 y‖).mul_const |t|
  apply squeeze_zero' (Filter.Eventually.of_forall (fun i => norm_nonneg _)) _ hz
  filter_upwards [hd] with i he
  exact U.stressPropagator_path_difference_fixed hc f (g i) t (hε i) he y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
