import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.EnergyCutoffNorm

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
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma stressCutoff_normalized (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    U.stressCutoff hc n hf*U.inverseSobolev r =
      Complex.I • (U.energyCutoff n*U.stressNormalized hc hf r*U.energyCutoff n) := by
  rw [stressCutoff,smul_mul_assoc]
  congr 1
  exact SymmetricOperator.cutoff_normalized (U.closedSmearedOperator hc A.conformalVector 2 f hf)
    _ _ _ _ (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
    (U.stressNormalized_graph hc hf hr) (U.energyCutoff_inverseSobolev n r)

lemma stressCutoff_continuous (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ)
    {f : ℝ → ℤ → ℂ} (hf : ∀ t, RapidCoefficients (f t))
    (hl : ∀ t, Tendsto (fun s => coefficientSeminorm (fun m => f s m-f t m) 2) (𝓝 t) (𝓝 0)) :
    Continuous (fun t => U.stressCutoff hc n (hf t)) := by
  unfold stressCutoff
  exact (continuous_const (y := Complex.I)).smul (continuous_const.mul
    ((U.stressNormalized_continuous hc hf hl le_rfl).mul continuous_const))

lemma stressCutoff_commutator (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) (hr : ∀ m, star (f m)=f (-m)) {r : ℕ} (hr' : 1 ≤ r) :
    ∃ G : Completion V →L[ℂ] Completion V,
      U.inverseSobolev r*U.stressCutoff hc n hf-U.stressCutoff hc n hf*U.inverseSobolev r = G*U.inverseSobolev r ∧
      ‖G‖ ≤ coefficientSeminorm f (2+r)*((1+A.centralCharge.re)*r) := by
  obtain ⟨F,hF,hFn⟩ := U.stressNormalized_defect hc hf hr hr'
  refine ⟨Complex.I • (U.energyCutoff n*F.adjoint*U.energyCutoff n),?_,
    (SymmetricOperator.cutoff_commutator_bound _ _ (U.energyCutoff_norm n)).trans hFn⟩
  exact SymmetricOperator.cutoff_commutator (U.closedSmearedOperator hc A.conformalVector 2 f hf)
    (U.stressCore_formalAdjoint hc hf hr) _ _ _ _ _ (U.energyCutoff_selfAdjoint n)
    (U.inverseSobolev_selfAdjoint r)
    (U.energyCutoff_graph 1 (U.stressCore hc hf) (U.stressCore_bound hc hf le_rfl)
      (U.smearedCore_closable hc A.conformal_mem hf) n)
    (U.stressNormalized_graph hc hf hr') (U.energyCutoff_inverseSobolev n r) hF

lemma stressCutoff_error (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖U.stressCutoff hc n hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2‖ ≤
      (1+(n:ℝ))⁻¹*((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re)) := by
  obtain ⟨B,hB,hBn,hE⟩ := U.stressNormalized_two_factor hc hf
  rw [U.stressCutoff_normalized hc n hf (by norm_num : 1 ≤ 2),← smul_sub,norm_smul,Complex.norm_I,one_mul]
  exact (SymmetricOperator.cutoff_error (U.energyCutoff n) (U.inverseSobolev 1)
    (U.stressNormalized hc hf 2) B (U.stressNormalized hc hf 1) (U.energyCutoff_norm n) hB hE
    (U.energyCutoff_inverseSobolev n 1) (U.energyCutoff_tail_inverse n)).trans (by
      have hn := U.stressNormalized_norm hc hf le_rfl
      have hc' : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
      calc
        _ ≤ (1+(n:ℝ))⁻¹*(coefficientSeminorm f 3*(1+A.centralCharge.re)+
            coefficientSeminorm f 2*(1+A.centralCharge.re)) := by gcongr
        _ = _ := by ring)

lemma stressCutoff_difference (hc : A.toVertexAlgebra.C2Cofinite) (n m : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) :
    ‖(U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2‖ ≤
      ((1+(n:ℝ))⁻¹+(1+(m:ℝ))⁻¹)*((coefficientSeminorm f 3+coefficientSeminorm f 2)*(1+A.centralCharge.re)) := by
  have he : (U.stressCutoff hc n hf-U.stressCutoff hc m hf)*U.inverseSobolev 2 =
      (U.stressCutoff hc n hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2)-
      (U.stressCutoff hc m hf*U.inverseSobolev 2-Complex.I • U.stressNormalized hc hf 2) := by noncomm_ring
  rw [he]
  exact (norm_sub_le _ _).trans ((add_le_add (U.stressCutoff_error hc n hf)
    (U.stressCutoff_error hc m hf)).trans_eq (by ring))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

structure StressPath where
  coefficients : ℝ → ℤ → ℂ
  rapid : ∀ t, RapidCoefficients (coefficients t)
  real : ∀ t n, star (coefficients t n)=coefficients t (-n)
  continuous : ∀ t, Tendsto (fun s => coefficientSeminorm
    (fun n => coefficients s n-coefficients t n) 2) (𝓝 t) (𝓝 0)
  bound : ℕ → ℝ
  bound_nonneg : ∀ r, 0 ≤ bound r
  seminorm_bound : ∀ t r, coefficientSeminorm (coefficients t) r ≤ bound r

lemma stressPath_cutoff_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) :
    ‖U.stressCutoff hc n (f.rapid t)‖ ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) := by
  exact (U.stressCutoff_norm hc n (f.rapid t)).trans (by
    gcongr
    · linarith [U.centralCharge_nonneg]
    · exact f.seminorm_bound t 2)

lemma stressPath_cutoff_commutator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) :
    ∃ G : ℕ → ℝ → Completion V →L[ℂ] Completion V,
      (∀ n t, U.inverseSobolev r*U.stressCutoff hc n (f.rapid t)-
        U.stressCutoff hc n (f.rapid t)*U.inverseSobolev r = G n t*U.inverseSobolev r) ∧
      ∀ n t, ‖G n t‖ ≤ f.bound (2+r)*((1+A.centralCharge.re)*r) := by
  choose G hG hGn using fun n t => U.stressCutoff_commutator hc n (f.rapid t) (f.real t) hr
  refine ⟨G,hG,fun n t => (hGn n t).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (f.seminorm_bound t (2+r))
    (mul_nonneg (by linarith [U.centralCharge_nonneg]) (Nat.cast_nonneg r))

lemma stressPath_cutoff_difference (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n m : ℕ) (t : ℝ) :
    ‖(U.stressCutoff hc n (f.rapid t)-U.stressCutoff hc m (f.rapid t))*U.inverseSobolev 2‖ ≤
      (1+(n:ℝ))⁻¹*((f.bound 3+f.bound 2)*(1+A.centralCharge.re))+
      (1+(m:ℝ))⁻¹*((f.bound 3+f.bound 2)*(1+A.centralCharge.re)) := by
  apply (U.stressCutoff_difference hc n m (f.rapid t)).trans
  calc
    _ ≤ ((1+(n:ℝ))⁻¹+(1+(m:ℝ))⁻¹)*((f.bound 3+f.bound 2)*(1+A.centralCharge.re)) := by
      gcongr
      · linarith [U.centralCharge_nonneg]
      · exact f.seminorm_bound t 3
      · exact f.seminorm_bound t 2
    _ = _ := by ring

 

lemma exists_stressPropagator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    ∃ L : Completion V →L[ℂ] Completion V, L ∈ unitary (Completion V →L[ℂ] Completion V) ∧
      (∀ x, Tendsto (fun n => TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)
        atTop (𝓝 (L x))) ∧
      (∀ x, Tendsto (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t) x)
        atTop (𝓝 (star L x))) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f (by norm_num : 1 ≤ 2)
  let C := (f.bound 3+f.bound 2)*(1+A.centralCharge.re)
  have hC : 0 ≤ C := mul_nonneg (add_nonneg (f.bound_nonneg 3) (f.bound_nonneg 2))
    (by linarith [U.centralCharge_nonneg])
  apply TimeOrdered.exists_unitary_evolution_limit
    (fun n s => U.stressCutoff hc n (f.rapid s))
    (fun n => U.stressCutoff_continuous hc n f.rapid f.continuous)
    (fun n => (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)))
    (fun n => mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f) (fun n s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev 2) (U.inverseSobolev_selfAdjoint 2) (U.inverseSobolev_dense 2)
    G hG hGn (mul_nonneg (f.bound_nonneg _) (mul_nonneg (by linarith [U.centralCharge_nonneg]) (by norm_num)))
    (fun n => (1+(n:ℝ))⁻¹*C) _ _ (U.stressPath_cutoff_difference hc f) t
  · intro n m hnm
    exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hnm 1)) hC
  · have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [one_div,add_comm,zero_mul] using h.mul_const C

 def stressPropagator (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    Completion V →L[ℂ] Completion V := (U.exists_stressPropagator hc f t).choose

lemma stressPropagator_unitary (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.stressPropagator hc f t ∈ unitary (Completion V →L[ℂ] Completion V) :=
  (U.exists_stressPropagator hc f t).choose_spec.1

lemma stressPropagator_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    Tendsto (fun n => TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)
      atTop (𝓝 (U.stressPropagator hc f t x)) := (U.exists_stressPropagator hc f t).choose_spec.2.1 x

lemma stressPropagator_star_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) (x : Completion V) :
    Tendsto (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t) x)
      atTop (𝓝 (star (U.stressPropagator hc f t) x)) := (U.exists_stressPropagator hc f t).choose_spec.2.2 x

lemma stressPropagator_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      U.stressPropagator hc f t*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  exact TimeOrdered.regularizer_factor_of_limits _ _ (U.stressPropagator_star_limit hc f t)
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (Real.exp_pos _).le (fun n x => TimeOrdered.evolution_star_energy_bound
      (U.stressCutoff_continuous hc n f.rapid f.continuous)
      (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
        exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
      (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
      (U.inverseSobolev r) (G n) (hG n) (hGn n) t x)

lemma stressPropagator_star_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      star (U.stressPropagator hc f t)*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  apply TimeOrdered.regularizer_factor_of_limits
    (fun n => star (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t)) _
    (by simpa only [star_star] using U.stressPropagator_limit hc f t)
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r) (Real.exp_pos _).le
  intro n x
  simp only [star_star]
  exact TimeOrdered.evolution_energy_bound (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev r) (G n) (hG n) (hGn n) t x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma inverseSobolev_injective (r : ℕ) : Function.Injective (U.inverseSobolev r) :=
  SymmetricOperator.selfAdjoint_injective_of_denseRange _
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)

lemma inverseSobolev_zero : U.inverseSobolev 0=1 := by
  ext x
  exact U.inverseSobolev_on_graph 0 (U.energyPower_zero_graph x)

lemma sobolev_interpolation_bound (r n : ℕ) {x p q : Completion V}
    (hp : U.inverseSobolev r p=x) (hq : U.inverseSobolev 1 q=p) :
    ‖p‖ ≤ (1+(n:ℝ))^r*‖x‖+(1+(n:ℝ))⁻¹*‖q‖ := by
  have he : U.energyCutoff n p=U.truncatedEnergyPower n r x := by
    apply U.inverseSobolev_injective r
    calc
      _ = U.energyCutoff n (U.inverseSobolev r p) :=
        congrArg (fun B : Completion V →L[ℂ] Completion V => B p) (U.energyCutoff_inverseSobolev n r).eq.symm
      _ = U.energyCutoff n x := by rw [hp]
      _ = _ := (congrArg (fun B : Completion V →L[ℂ] Completion V => B x) (U.inverseSobolev_truncated n r)).symm
  calc
    ‖p‖ ≤ ‖U.energyCutoff n p‖+‖p-U.energyCutoff n p‖ := by
      simpa only [add_sub_cancel] using norm_add_le (U.energyCutoff n p) (p-U.energyCutoff n p)
    _ ≤ (1+(n:ℝ))^r*‖x‖+(1+(n:ℝ))⁻¹*‖q‖ := by
      apply add_le_add
      · rw [he]
        exact (U.truncatedEnergyPower n r).le_of_opNorm_le (U.truncatedEnergyPower_norm n r) x
      · simpa only [mul_apply_eq_comp,sub_apply,one_apply_eq_self,hq] using
          ((1-U.energyCutoff n)*U.inverseSobolev 1).le_of_opNorm_le (U.energyCutoff_tail_inverse n) q

 

lemma tendsto_sobolev_of_extra_bound {ι : Type*} {l : Filter ι}
    (r : ℕ) (x p q : ι → Completion V)
    (hp : ∀ i, U.inverseSobolev r (p i)=x i)
    (hq : ∀ i, U.inverseSobolev 1 (q i)=p i)
    (hx : Tendsto x l (𝓝 0)) {C : ℝ} (hb : ∀ᶠ i in l, ‖q i‖ ≤ C) :
    Tendsto p l (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => (1+(n:ℝ))⁻¹*C) atTop (𝓝 0) := by
    simpa only [one_div,add_comm,zero_mul] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const C
  obtain ⟨n,hn⟩ := (ht.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))).exists
  have ht' : Tendsto (fun i => (1+(n:ℝ))^r*‖x i‖) l (𝓝 0) := by
    simpa only [norm_zero,mul_zero] using hx.norm.const_mul ((1+(n:ℝ))^r)
  filter_upwards [hb,ht'.eventually (gt_mem_nhds (by linarith : (0:ℝ)<ε/2))] with i hi hi'
  rw [dist_zero_right]
  have h := U.sobolev_interpolation_bound r n (hp i) (hq i)
  have h2 := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (1+(n:ℝ))⁻¹)
  linarith

lemma smoothEnergyPower_inverse_next (r : ℕ) (x : U.smoothEnergySpace) :
    U.inverseSobolev 1 (U.smoothEnergyPower (r+1) x)=U.smoothEnergyPower r x := by
  apply U.inverseSobolev_injective r
  change (U.inverseSobolev r*U.inverseSobolev 1) (U.smoothEnergyPower (r+1) x)=_
  rw [U.inverseSobolev_mul,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]

lemma smoothEnergyPower_sub (r : ℕ) (x y : U.smoothEnergySpace) :
    U.smoothEnergyPower r (x-y)=U.smoothEnergyPower r x-U.smoothEnergyPower r y := by
  apply U.inverseSobolev_injective r
  rw [map_sub,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower]
  rfl

lemma tendsto_smoothEnergyPower {ι : Type*} {l : Filter ι} (r : ℕ)
    (x : ι → U.smoothEnergySpace) (y : U.smoothEnergySpace)
    (hx : Tendsto (fun i => (x i : Completion V)) l (𝓝 (y : Completion V)))
    {C : ℝ} (hb : ∀ᶠ i in l, ‖U.smoothEnergyPower (r+1) (x i)‖ ≤ C) :
    Tendsto (fun i => U.smoothEnergyPower r (x i)) l (𝓝 (U.smoothEnergyPower r y)) := by
  have hb' : ∀ᶠ i in l,
      ‖U.smoothEnergyPower (r+1) (x i)-U.smoothEnergyPower (r+1) y‖ ≤
        C+‖U.smoothEnergyPower (r+1) y‖ := by
    filter_upwards [hb] with i hi
    have h1 := norm_sub_le (U.smoothEnergyPower (r+1) (x i)) (U.smoothEnergyPower (r+1) y)
    linarith
  apply tendsto_sub_nhds_zero_iff.mp
  exact U.tendsto_sobolev_of_extra_bound r
    (fun i => (x i : Completion V)-(y : Completion V))
    (fun i => U.smoothEnergyPower r (x i)-U.smoothEnergyPower r y)
    (fun i => U.smoothEnergyPower (r+1) (x i)-U.smoothEnergyPower (r+1) y)
    (fun i => by rw [map_sub,U.inverseSobolev_smoothEnergyPower,U.inverseSobolev_smoothEnergyPower])
    (fun i => by rw [map_sub,U.smoothEnergyPower_inverse_next,U.smoothEnergyPower_inverse_next])
    (tendsto_sub_nhds_zero_iff.mpr hx) hb'
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma preserves_smoothEnergySpace_of_factor (Q : Completion V →L[ℂ] Completion V)
    (hQ : ∀ r : ℕ, 1 ≤ r → ∃ B : Completion V →L[ℂ] Completion V,
      Q*U.inverseSobolev r=U.inverseSobolev r*B)
    {x : Completion V} (hx : x ∈ U.smoothEnergySpace) : Q x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  have hg : ∃ y, (Q x,y) ∈ (U.energyPower r).graph := by
    by_cases hr : r=0
    · subst r
      exact ⟨Q x,U.energyPower_zero_graph (Q x)⟩
    · obtain ⟨B,hB⟩ := hQ r (by omega)
      let y := U.energyPower r ⟨x,hx r⟩
      have hy : (x,y) ∈ (U.energyPower r).graph := (U.energyPower r).mem_graph_iff.mpr ⟨_,rfl,rfl⟩
      have he := congrArg (fun Q : Completion V →L[ℂ] Completion V => Q y) hB
      change Q (U.inverseSobolev r y)=U.inverseSobolev r (B y) at he
      rw [U.inverseSobolev_on_graph r hy] at he
      exact ⟨B y,he.symm ▸ U.inverseSobolev_graph r (B y)⟩
  obtain ⟨y,hy⟩ := hg
  obtain ⟨z,hz,_⟩ := (U.energyPower r).mem_graph_iff.mp hy
  dsimp only [Prod.fst] at hz
  rw [← hz]
  exact z.property

lemma smoothEnergyPower_eq_of_factor (Q B : Completion V →L[ℂ] Completion V) (r : ℕ)
    (hB : Q*U.inverseSobolev r=U.inverseSobolev r*B)
    (x y : U.smoothEnergySpace) (hy : (y : Completion V)=Q x) :
    U.smoothEnergyPower r y=B (U.smoothEnergyPower r x) := by
  apply U.inverseSobolev_injective r
  rw [U.inverseSobolev_smoothEnergyPower]
  change _ = (U.inverseSobolev r*B) _
  rw [← hB]
  change _ = Q (U.inverseSobolev r (U.smoothEnergyPower r x))
  rw [U.inverseSobolev_smoothEnergyPower,hy]

lemma stressPropagator_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    U.stressPropagator hc f t x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressPropagator_factor hc f hr t
  exact ⟨B,hB⟩

lemma stressPropagator_star_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    star (U.stressPropagator hc f t) x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressPropagator_star_factor hc f hr t
  exact ⟨B,hB⟩

 def stressPropagatorSmooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath) (t : ℝ) :
    U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  ((U.stressPropagator hc f t).toLinearMap.comp U.smoothEnergySpace.subtype).codRestrict
    U.smoothEnergySpace (fun x => U.stressPropagator_smooth hc f t x.property)

lemma stressPropagatorSmooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x)‖ ≤
      Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|)*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨B,hB,hBn⟩ := U.stressPropagator_factor hc f hr t
  rw [U.smoothEnergyPower_eq_of_factor _ B r hB x (U.stressPropagatorSmooth hc f t x) rfl]
  exact B.le_of_opNorm_le hBn _

lemma stressCutoff_evolution_factor (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (n : ℕ) (t : ℝ) :
    ∃ B : Completion V →L[ℂ] Completion V,
      TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t*U.inverseSobolev r=U.inverseSobolev r*B ∧
      ‖B‖ ≤ Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|) := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  obtain ⟨G,hG,hGn⟩ := U.stressPath_cutoff_commutator hc f hr
  exact TimeOrdered.evolution_regularizer_factor (U.stressCutoff_continuous hc n f.rapid f.continuous)
    (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
      exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
    (U.stressPath_cutoff_bound hc f n) (fun s => U.stressCutoff_skew hc n (f.rapid s) (f.real s))
    (U.inverseSobolev r) (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r) (G n) (hG n) (hGn n) t

lemma stressCutoff_evolution_smooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x ∈ U.smoothEnergySpace := by
  apply U.preserves_smoothEnergySpace_of_factor _ _ hx
  intro r hr
  obtain ⟨B,hB,_⟩ := U.stressCutoff_evolution_factor hc f hr n t
  exact ⟨B,hB⟩

 def stressCutoffEvolutionSmooth (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) : U.smoothEnergySpace →ₗ[ℂ] U.smoothEnergySpace :=
  ((TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t).toLinearMap.comp
    U.smoothEnergySpace.subtype).codRestrict U.smoothEnergySpace
      (fun x => U.stressCutoff_evolution_smooth hc f n t x.property)

lemma stressCutoffEvolutionSmooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {r : ℕ} (hr : 1 ≤ r) (n : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.smoothEnergyPower r (U.stressCutoffEvolutionSmooth hc f n t x)‖ ≤
      Real.exp ((f.bound (2+r)*((1+A.centralCharge.re)*r))*|t|)*‖U.smoothEnergyPower r x‖ := by
  obtain ⟨B,hB,hBn⟩ := U.stressCutoff_evolution_factor hc f hr n t
  rw [U.smoothEnergyPower_eq_of_factor _ B r hB x (U.stressCutoffEvolutionSmooth hc f n t x) rfl]
  exact B.le_of_opNorm_le hBn _

lemma stressCutoffEvolutionSmooth_limit (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (r : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    Tendsto (fun n => U.smoothEnergyPower r (U.stressCutoffEvolutionSmooth hc f n t x)) atTop
      (𝓝 (U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x))) := by
  apply U.tendsto_smoothEnergyPower r _ _ (U.stressPropagator_limit hc f t x)
  exact Filter.Eventually.of_forall (fun n => U.stressCutoffEvolutionSmooth_bound hc f (by omega : 1 ≤ r+1) n t x)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma stressCutoff_normalized_norm (hc : A.toVertexAlgebra.C2Cofinite) (n : ℕ) {f : ℤ → ℂ}
    (hf : RapidCoefficients f) {r : ℕ} (hr : 1 ≤ r) :
    ‖U.stressCutoff hc n hf*U.inverseSobolev r‖ ≤ coefficientSeminorm f 2*(1+A.centralCharge.re) := by
  rw [U.stressCutoff_normalized hc n hf hr,norm_smul,Complex.norm_I,one_mul]
  calc
    _ ≤ (‖U.energyCutoff n‖*‖U.stressNormalized hc hf r‖)*‖U.energyCutoff n‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1*‖U.stressNormalized hc hf r‖)*1 := by
      gcongr <;> exact U.energyCutoff_norm n
    _ ≤ _ := by simpa only [one_mul,mul_one] using U.stressNormalized_norm hc hf hr

lemma stressCutoff_smooth_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) (t : ℝ) (x : U.smoothEnergySpace) :
    ‖U.stressCutoff hc n (f.rapid t) x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*‖U.smoothEnergyPower 1 x‖ := by
  rw [← U.inverseSobolev_smoothEnergyPower 1 x]
  have hn : ‖U.stressCutoff hc n (f.rapid t)*U.inverseSobolev 1‖ ≤ f.bound 2*(1+A.centralCharge.re) :=
    (U.stressCutoff_normalized_norm hc n (f.rapid t) le_rfl).trans
      (mul_le_mul_of_nonneg_right (f.seminorm_bound t 2) (by linarith [U.centralCharge_nonneg]))
  exact (U.stressCutoff hc n (f.rapid t)*U.inverseSobolev 1).le_of_opNorm_le hn _

lemma stressCutoff_derivative_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) {R t : ℝ} (ht : |t| ≤ R) (x : U.smoothEnergySpace) :
    ‖U.stressCutoff hc n (f.rapid t)
      (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t x)‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖ := by
  have h1 := U.stressCutoff_smooth_bound hc f n t (U.stressCutoffEvolutionSmooth hc f n t x)
  have h2 := U.stressCutoffEvolutionSmooth_bound hc f le_rfl n t x
  change ‖U.stressCutoff hc n (f.rapid t) (TimeOrdered.evolution (fun s => U.stressCutoff hc n (f.rapid s)) t (x : Completion V))‖ ≤ _ at h1
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hB := mul_nonneg (f.bound_nonneg 2) hC
  have hD := mul_nonneg (f.bound_nonneg 3) hC
  calc
    _ ≤ (f.bound 2*(1+A.centralCharge.re))*
        (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)*‖U.smoothEnergyPower 1 x‖) := by
      apply h1.trans
      exact mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one,mul_one] using h2) hB
    _ ≤ _ := by
      have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht hD)
      exact (le_of_eq (mul_assoc (f.bound 2*(1+A.centralCharge.re))
        (Real.exp ((f.bound 3*(1+A.centralCharge.re))*|t|)) ‖U.smoothEnergyPower 1 x‖).symm).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB) (norm_nonneg _))

lemma stressCutoff_evolution_sub_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (n : ℕ) {R s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R)
    (x : U.smoothEnergySpace) :
    ‖TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) t x-
      TimeOrdered.evolution (fun q => U.stressCutoff hc n (f.rapid q)) s x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖*‖t-s‖ := by
  let : Nontrivial V := nontrivial_of_ne A.vacuum 0 A.vacuum_ne_zero
  let : Nontrivial (Completion V) := (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective.nontrivial
  apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun q _ => (TimeOrdered.evolution_apply_derivative
      (U.stressCutoff_continuous hc n f.rapid f.continuous)
      (show 0 ≤ (f.bound 2*(1+A.centralCharge.re))*(1+(n:ℝ)) by
        exact mul_nonneg (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (by positivity))
      (U.stressPath_cutoff_bound hc f n) q (x : Completion V)).hasDerivWithinAt)
    (fun q hq => U.stressCutoff_derivative_bound hc f n (abs_le.mpr hq) x)
    (convex_Icc _ _) hs ht

lemma stressPropagator_sub_bound (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    {R s t : ℝ} (hs : s ∈ Icc (-R) R) (ht : t ∈ Icc (-R) R) (x : U.smoothEnergySpace) :
    ‖U.stressPropagator hc f t x-U.stressPropagator hc f s x‖ ≤
      (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
        ‖U.smoothEnergyPower 1 x‖*‖t-s‖ := by
  exact le_of_tendsto ((U.stressPropagator_limit hc f t x).sub
    (U.stressPropagator_limit hc f s x)).norm
    (Filter.Eventually.of_forall (fun n => U.stressCutoff_evolution_sub_bound hc f n hs ht x))

lemma stressPropagator_smooth_continuous (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (x : U.smoothEnergySpace) : Continuous (fun t => U.stressPropagator hc f t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  let R := |s|+1
  let C := (f.bound 2*(1+A.centralCharge.re))*Real.exp ((f.bound 3*(1+A.centralCharge.re))*R)*
    ‖U.smoothEnergyPower 1 x‖
  have hC : 0 ≤ C := mul_nonneg (mul_nonneg
    (mul_nonneg (f.bound_nonneg 2) (by linarith [U.centralCharge_nonneg])) (Real.exp_pos _).le) (norm_nonneg _)
  have hL : LipschitzOnWith ⟨C,hC⟩ (fun t => U.stressPropagator hc f t x) (Icc (-R) R) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro t ht q hq
    rw [dist_eq_norm,dist_eq_norm]
    change ‖U.stressPropagator hc f t x-U.stressPropagator hc f q x‖ ≤ C*‖t-q‖
    exact U.stressPropagator_sub_bound hc f hq ht x
  exact hL.continuousOn.continuousAt (Icc_mem_nhds (by dsimp [R]; linarith [neg_abs_le s])
    (by dsimp [R]; linarith [le_abs_self s]))

lemma stressPropagatorSmooth_continuous_power (hc : A.toVertexAlgebra.C2Cofinite) (f : StressPath)
    (r : ℕ) (x : U.smoothEnergySpace) :
    Continuous (fun t => U.smoothEnergyPower r (U.stressPropagatorSmooth hc f t x)) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply U.tendsto_smoothEnergyPower r (fun t => U.stressPropagatorSmooth hc f t x)
    (U.stressPropagatorSmooth hc f s x) (U.stressPropagator_smooth_continuous hc f x).continuousAt
    (C := Real.exp ((f.bound (2+(r+1))*((1+A.centralCharge.re)*(r+1)))*(|s|+1))*
      ‖U.smoothEnergyPower (r+1) x‖)
  have hne : ∀ᶠ t in 𝓝 s, |t| < |s|+1 := continuous_abs.continuousAt.eventually
    (gt_mem_nhds (by linarith : |s| < |s|+1))
  filter_upwards [hne] with t ht
  apply (U.stressPropagatorSmooth_bound hc f (by omega : 1 ≤ r+1) t x).trans
  have hC : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hD : 0 ≤ f.bound (2+(r+1))*((1+A.centralCharge.re)*(r+1)) :=
    mul_nonneg (f.bound_nonneg _) (mul_nonneg hC (by positivity))
  simpa only [Nat.cast_add,Nat.cast_one] using
    mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.le hD))
      (norm_nonneg (U.smoothEnergyPower (r+1) x))
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace Filter Set MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
