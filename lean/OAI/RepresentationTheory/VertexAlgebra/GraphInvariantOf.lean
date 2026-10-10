import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.Locality

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
namespace StronglyRationalVOA.ClosedGraphData
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma graph_invariant_of_entry_commutes (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (Q : H →L[ℂ] H) (hQ : ∀ i j, Q * entry T hT i j = entry T hT i j * Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  let z : Double H := WithLp.toLp 2 (x,y)
  let : IsClosed (graph T : Set (Double H)) := graph_closed hT
  have hz : z ∈ graph T := hxy
  have hp : projection T hT z = z := Submodule.starProjection_eq_self_iff.mpr hz
  have hh := congrArg (fun L : Double H →L[ℂ] Double H => L z)
    (projection_commutes_of_entry_commutes T hT Q hQ)
  change diagonalAction Q (projection T hT z) = projection T hT (diagonalAction Q z) at hh
  rw [hp] at hh
  have hm := (graph T).starProjection_apply_mem (diagonalAction Q z)
  change projection T hT (diagonalAction Q z) ∈ graph T at hm
  rw [← hh] at hm
  exact hm
lemma entry_commutes_iff_graph_reduces (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (Q : H →L[ℂ] H) :
    (∀ i j, Q * entry T hT i j = entry T hT i j * Q) ↔
      (∀ x y : H, (x,y) ∈ T.graph → (Q x,Q y) ∈ T.graph) ∧
      (∀ x y : H, (x,y) ∈ T.graph → (Q.adjoint x,Q.adjoint y) ∈ T.graph) := by
  constructor
  · intro h
    refine ⟨fun x y xy => graph_invariant_of_entry_commutes T hT Q h xy, ?_⟩
    intro x y xy
    apply graph_invariant_of_entry_commutes T hT Q.adjoint _ xy
    intro i j
    have he := congrArg star (h j i)
    rw [star_mul, star_mul, star_entry] at he
    exact he.symm
  · rintro ⟨h,ha⟩
    exact entry_commutes_of_graph_invariant T hT Q h ha
end StronglyRationalVOA.ClosedGraphData

open UniformSpace Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
lemma flow_eigenvector (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {x : H} (μ : ℝ)
    (hg : (x,(μ : ℂ) • x) ∈ T.graph) (t : ℝ) :
    flow T hs t x = Complex.exp ((t*μ : ℝ)*Complex.I) • x := by
  let z : ℂ := (μ : ℂ)*Complex.I
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => Complex.exp (-(r : ℂ)*z) • flow T hs r x) 0 s := by
    have he : HasDerivAt (fun r : ℝ => Complex.exp (-(r : ℂ)*z))
        (Complex.exp (-(s : ℂ)*z)*(-z)) s := by
      convert (((hasDerivAt_id s).ofReal_comp.neg).mul_const z).cexp using 1 <;> simp
    have h := he.smul (flow_derivative T hs hg s)
    convert h using 1
    rw [map_smul,map_smul,smul_smul,smul_smul,← add_smul]
    dsimp only [z]
    convert (zero_smul ℂ (flow T hs s x)).symm using 1
    ring_nf
  have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simp only [Complex.ofReal_zero,neg_zero,zero_mul,Complex.exp_zero,flow_zero,
    one_apply_eq_self,one_smul] at he
  have h := congrArg (fun v : H => Complex.exp ((t : ℂ)*z) • v) he
  have hm : Complex.exp ((t : ℂ)*z)*Complex.exp (-(t : ℂ)*z)=1 := by
    rw [← Complex.exp_add,← add_mul,add_neg_cancel,zero_mul,Complex.exp_zero]
  rw [smul_smul,hm,one_smul] at h
  convert h using 1
  dsimp only [z]
  push_cast
  ring_nf
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma rotation_eq_hamiltonianFlow (t : ℝ) : U.rotation t =
    SymmetricOperator.flow U.conformalHamiltonian (U.energyOperator_selfAdjoint (fun d => d)) t := by
  apply ContinuousLinearMap.ext
  intro x
  refine Completion.denseRange_coe.induction_on x ?_ ?_
  · exact isClosed_eq (U.rotation t).continuous (SymmetricOperator.flow _ _ t).continuous
  · intro v
    apply A.homogeneous_induction (P := fun v => U.rotation t (v : Completion V) =
      SymmetricOperator.flow U.conformalHamiltonian (U.energyOperator_selfAdjoint (fun d => d)) t (v : Completion V))
    · simp only [Completion.coe_zero,map_zero]
    · intro e v hv
      rw [U.rotation_grade t ⟨v,hv⟩]
      symm
      apply SymmetricOperator.flow_eigenvector
      exact U.conformalHamiltonian.mem_graph_iff.mpr
        ⟨⟨(v : Completion V),U.coe_mem_energyOperator (fun d => d) v⟩,rfl,U.energyOperator_grade _ ⟨v,hv⟩⟩
    · intro a b ha hb
      simp only [Completion.coe_add,map_add,ha,hb]
lemma rotation_derivative {x y : Completion V} (hxy : (x,y) ∈ U.conformalHamiltonian.graph) (t : ℝ) :
    HasDerivAt (fun s : ℝ => U.rotation s x) (U.rotation t (Complex.I • y)) t := by
  simp_rw [U.rotation_eq_hamiltonianFlow]
  exact SymmetricOperator.flow_derivative _ _ hxy t
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma energyOperator_graph_iff (w : ℕ → ℝ) (x y : Completion V) :
    (x,y) ∈ (U.energyOperator w).graph ↔
      ∀ d, U.energyCoordinates y d = (w d : ℂ) • U.energyCoordinates x d := by
  rw [energyOperator,OperatorTransport.mem_graph_iff,HilbertScale.mem_graph_iff]
lemma energyPower_graph_iff_inverse (k : ℕ) (x y : Completion V) :
    (x,y) ∈ (U.energyPower k).graph ↔ U.inverseSobolev k y=x := by
  constructor
  · exact U.inverseSobolev_on_graph k
  · intro h
    simpa only [h] using U.inverseSobolev_graph k y
lemma energyPower_add_graph (k l : ℕ) (x z : Completion V) :
    (x,z) ∈ (U.energyPower (k+l)).graph ↔
      ∃ y, (x,y) ∈ (U.energyPower k).graph ∧ (y,z) ∈ (U.energyPower l).graph := by
  simp_rw [U.energyPower_graph_iff_inverse]
  constructor
  · intro h
    refine ⟨U.inverseSobolev l z,?_,rfl⟩
    change (U.inverseSobolev k*U.inverseSobolev l) z=x
    rwa [U.inverseSobolev_mul]
  · rintro ⟨y,hxy,hyz⟩
    rw [← U.inverseSobolev_mul]
    change U.inverseSobolev k (U.inverseSobolev l z)=x
    rw [hyz,hxy]
lemma energyPower_domain_le {k l : ℕ} (hkl : k ≤ l) :
    (U.energyPower l).domain ≤ (U.energyPower k).domain := by
  intro x hx
  have h : (x,(U.energyPower l) ⟨x,hx⟩) ∈ (U.energyPower l).graph :=
    (U.energyPower l).mem_graph_iff.mpr ⟨⟨x,hx⟩,rfl,rfl⟩
  have h' : (x,(U.energyPower l) ⟨x,hx⟩) ∈ (U.energyPower (k+(l-k))).graph := by
    simpa only [Nat.add_sub_of_le hkl] using h
  rw [U.energyPower_add_graph] at h'
  obtain ⟨y,hy,_⟩ := h'
  exact LinearPMap.mem_domain_of_mem_graph hy
lemma energyOne_graph_iff (x y : Completion V) :
    (x,y) ∈ (U.energyPower 1).graph ↔ (x,y-x) ∈ U.conformalHamiltonian.graph := by
  change (x,y) ∈ (U.energyOperator (fun d => (1+(d:ℝ))^1)).graph ↔
    (x,y-x) ∈ (U.energyOperator (fun d => d)).graph
  rw [U.energyOperator_graph_iff,U.energyOperator_graph_iff]
  simp only [pow_one,map_sub,lp.coeFn_sub,Pi.sub_apply,Complex.ofReal_add,
    Complex.ofReal_one,Complex.ofReal_natCast]
  constructor
  · intro h d
    rw [h d,add_smul,one_smul]
    abel
  · intro h d
    have hh := h d
    rw [add_smul,one_smul]
    exact eq_add_of_sub_eq' hh
lemma smoothEnergyPower_mem (k : ℕ) (x : U.smoothEnergySpace) :
    U.smoothEnergyPower k x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf]
  intro l
  have h := U.smoothEnergyPower_graph (k+l) x
  rw [U.energyPower_add_graph] at h
  obtain ⟨y,hy,hyz⟩ := h
  have he : y=U.smoothEnergyPower k x :=
    (U.energyPower k).mem_graph_snd_inj hy (U.smoothEnergyPower_graph k x) rfl
  rw [← he]
  exact LinearPMap.mem_domain_of_mem_graph hyz
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
def conjugation (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) : H →L[ℂ] H :=
  flow T hs t * Q * flow T hs (-t)
lemma conjugation_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) (x : H) :
    ‖conjugation T hs Q t x‖ ≤ ‖Q‖*‖x‖ := by
  change ‖flow T hs t (Q (flow T hs (-t) x))‖ ≤ _
  rw [flow_norm]
  simpa only [flow_norm] using Q.le_opNorm (flow T hs (-t) x)
lemma conjugation_opNorm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) :
    ‖conjugation T hs Q t‖ ≤ ‖Q‖ :=
  (conjugation T hs Q t).opNorm_le_bound (norm_nonneg _) (conjugation_norm T hs Q t)
lemma conjugation_continuous (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (x : H) :
    Continuous (fun t : ℝ => conjugation T hs Q t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact StrongLimit.apply_tendsto (fun s => flow T hs s) (flow T hs t)
    (flow_opNorm T hs) (fun x => (flow_continuous T hs x).tendsto t)
    (Q.continuous.tendsto _ |>.comp (((flow_continuous T hs x).comp continuous_neg).tendsto t))
lemma conjugation_inner (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) (x y : H) :
    inner ℂ x (conjugation T hs Q t y) = inner ℂ (flow T hs (-t) x) (Q (flow T hs (-t) y)) := by
  change inner ℂ x (flow T hs t (Q (flow T hs (-t) y))) = _
  rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
lemma conjugation_matrix_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    {u v x y : H} (huv : (u,v) ∈ T.graph) (hxy : (x,y) ∈ T.graph) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ u (conjugation T hs Q s x))
      (Complex.I*inner ℂ v (conjugation T hs Q t x) -
        Complex.I*inner ℂ u (conjugation T hs Q t y)) t := by
  have hv := (flow_derivative T hs huv (-t)).scomp t (hasDerivAt_neg t)
  have hx := (flow_derivative T hs hxy (-t)).scomp t (hasDerivAt_neg t)
  have h := HasDerivAt.inner ℂ hv ((Q.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hx)
  change HasDerivAt (fun s : ℝ => inner ℂ (flow T hs (-s) u) (Q (flow T hs (-s) x)))
    (inner ℂ (flow T hs (-t) u) (Q ((-1 : ℝ) • flow T hs (-t) (Complex.I • y))) +
      inner ℂ ((-1 : ℝ) • flow T hs (-t) (Complex.I • v)) (Q (flow T hs (-t) x))) t at h
  simp only [neg_one_smul,map_neg,map_smul,inner_neg_left,inner_neg_right,
    inner_smul_left,inner_smul_right,Complex.conj_I,neg_mul,neg_neg] at h
  simpa only [conjugation_inner,sub_eq_add_neg,add_comm] using h
 

def conjugationIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t in a..b, f t • conjugation T hs Q t x
      map_add' := fun x y => by
        simp only [map_add,smul_add]
        exact intervalIntegral.integral_add
          ((hf.smul (conjugation_continuous T hs Q x)).intervalIntegrable a b)
          ((hf.smul (conjugation_continuous T hs Q y)).intervalIntegrable a b)
      map_smul' := fun c x => by
        simp only [map_smul,smul_comm (f _) c]
        exact intervalIntegral.integral_smul c _ }
    (C*‖Q‖*|b-a|) (fun x => by
      change ‖∫ t in a..b, f t • conjugation T hs Q t x‖ ≤ _
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
      calc
        _ ≤ (C*‖Q‖*‖x‖)*|b-a| := intervalIntegral.norm_integral_le_of_norm_le_const (fun t _ => by
          rw [norm_smul]
          calc
            _ ≤ C*(‖Q‖*‖x‖) := mul_le_mul (hC t) (conjugation_norm T hs Q t x) (norm_nonneg _) hC0
            _ = _ := by ring)
        _ = _ := by ring)
lemma conjugationIntegral_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) (x : H) :
    conjugationIntegral T hs Q a b f hf C hC x = ∫ t in a..b, f t • conjugation T hs Q t x := rfl
lemma inner_conjugationIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C) (u x : H) :
    inner ℂ u (conjugationIntegral T hs Q a b f hf C hC x) =
      ∫ t in a..b, f t * inner ℂ u (conjugation T hs Q t x) := by
  have h := (innerSL ℂ u).intervalIntegral_comp_comm (μ := volume)
    ((hf.smul (conjugation_continuous T hs Q x)).intervalIntegrable a b)
  change (∫ t in a..b, inner ℂ u (f t • conjugation T hs Q t x)) =
    inner ℂ u (conjugationIntegral T hs Q a b f hf C hC x) at h
  simpa only [inner_smul_right] using h.symm
 

lemma conjugationIntegral_generator_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (a b : ℝ) (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (Cf Cg : ℝ) (hCf : ∀ t, ‖f t‖ ≤ Cf) (hCg : ∀ t, ‖g t‖ ≤ Cg)
    (hd : ∀ t, HasDerivAt f (g t) t) (hfa : f a=0) (hfb : f b=0)
    {x y : H} (hxy : (x,y) ∈ T.graph) :
    (conjugationIntegral T hs Q a b f hf Cf hCf x,
      conjugationIntegral T hs Q a b f hf Cf hCf y +
        Complex.I • conjugationIntegral T hs Q a b g hg Cg hCg x) ∈ T.graph := by
  rw [show T.graph = T.adjoint.graph from congrArg LinearPMap.graph hs.symm,
    LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have hh (t : ℝ) := (hd t).mul (conjugation_matrix_derivative T hs Q huv hxy t)
  let D : ℝ → ℂ := fun t => Complex.I*(f t * inner ℂ v (conjugation T hs Q t x)) -
    Complex.I*(f t * inner ℂ u (conjugation T hs Q t y)) + g t*inner ℂ u (conjugation T hs Q t x)
  have he (t : ℝ) : HasDerivAt (fun s => f s * inner ℂ u (conjugation T hs Q s x)) (D t) t := by
    exact (hh t).congr_deriv (by dsimp only [D]; ring)
  have hc1 : Continuous (fun t => f t*inner ℂ v (conjugation T hs Q t x)) :=
    hf.mul (continuous_const.inner (conjugation_continuous T hs Q x))
  have hc2 : Continuous (fun t => f t*inner ℂ u (conjugation T hs Q t y)) :=
    hf.mul (continuous_const.inner (conjugation_continuous T hs Q y))
  have hc3 : Continuous (fun t => g t*inner ℂ u (conjugation T hs Q t x)) :=
    hg.mul (continuous_const.inner (conjugation_continuous T hs Q x))
  have hdc : Continuous D := ((continuous_const.mul hc1).sub (continuous_const.mul hc2)).add hc3
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => he t) (hdc.intervalIntegrable a b)
  simp only [hfa,hfb,zero_mul,sub_zero] at h
  dsimp only [D] at h
  have hi1 : IntervalIntegrable (fun t => Complex.I*(f t*inner ℂ v (conjugation T hs Q t x))) volume a b :=
    (continuous_const.mul hc1).intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t => Complex.I*(f t*inner ℂ u (conjugation T hs Q t y))) volume a b :=
    (continuous_const.mul hc2).intervalIntegrable a b
  rw [intervalIntegral.integral_add (hi1.sub hi2) (hc3.intervalIntegrable a b),
    intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    ← inner_conjugationIntegral T hs Q a b f hf Cf hCf v x,
    ← inner_conjugationIntegral T hs Q a b f hf Cf hCf u y,
    ← inner_conjugationIntegral T hs Q a b g hg Cg hCg u x] at h
  simp only [inner_add_right,inner_smul_right]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) (-Complex.I) * h
 

lemma conjugationIntegral_preserves_graph (T S : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hS : S.IsClosed) (Q : H →L[ℂ] H) (a b : ℝ) (f : ℝ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ t, ‖f t‖ ≤ C)
    (hi : ∀ t, f t ≠ 0 → ∀ x y, (x,y) ∈ S.graph →
      (conjugation T hs Q t x,conjugation T hs Q t y) ∈ S.graph)
    {x y : H} (hxy : (x,y) ∈ S.graph) :
    (conjugationIntegral T hs Q a b f hf C hC x,
      conjugationIntegral T hs Q a b f hf C hC y) ∈ S.graph := by
  have hfc : Continuous (fun t => (f t • conjugation T hs Q t x,f t • conjugation T hs Q t y)) :=
    (hf.smul (conjugation_continuous T hs Q x)).prodMk (hf.smul (conjugation_continuous T hs Q y))
  have h := intervalIntegral_mem_closedSubmodule S.graph hS (hfc.intervalIntegrable a b) (fun t => ?_)
  · have he : (∫ t in a..b,(f t • conjugation T hs Q t x,f t • conjugation T hs Q t y)) =
        (conjugationIntegral T hs Q a b f hf C hC x,
          conjugationIntegral T hs Q a b f hf C hC y) := by
      apply Prod.ext
      · exact ((ContinuousLinearMap.fst ℂ H H).intervalIntegral_comp_comm (hfc.intervalIntegrable a b)).symm
      · exact ((ContinuousLinearMap.snd ℂ H H).intervalIntegral_comp_comm (hfc.intervalIntegrable a b)).symm
    rwa [he] at h
  · by_cases ht : f t=0
    · simp only [ht,zero_smul]
      exact S.graph.zero_mem
    · exact S.graph.smul_mem (f t) (hi t ht x y hxy)
end StronglyRationalVOA.SymmetricOperator

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
 

lemma conjugationIntegral_energy_domain (Q : Completion V →L[ℂ] Completion V)
    (a b : ℝ) (f : ℕ → ℝ → ℂ) (hf : ∀ j, Continuous (f j))
    (C : ℕ → ℝ) (hC : ∀ j t, ‖f j t‖ ≤ C j)
    (hd : ∀ j t, HasDerivAt (f j) (f (j+1) t) t)
    (ha : ∀ j, f j a=0) (hb : ∀ j, f j b=0) :
    ∀ k j (x : Completion V), x ∈ (U.energyPower k).domain →
      SymmetricOperator.conjugationIntegral U.conformalHamiltonian
        (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j) x ∈
          (U.energyPower k).domain := by
  let F (j : ℕ) := SymmetricOperator.conjugationIntegral U.conformalHamiltonian
    (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j)
  intro k
  induction k with
  | zero =>
      intro j x _
      exact LinearPMap.mem_domain_of_mem_graph (U.energyPower_zero_graph (F j x))
  | succ k ih =>
      intro j x hx
      change F j x ∈ (U.energyPower (k+1)).domain
      obtain ⟨z,hxz⟩ := LinearPMap.mem_domain_iff.mp hx
      have hsplit : (x,z) ∈ (U.energyPower (1+k)).graph := by
        simpa only [Nat.add_comm] using hxz
      rw [U.energyPower_add_graph] at hsplit
      obtain ⟨y,hxy,hyz⟩ := hsplit
      have hxk := U.energyPower_domain_le (Nat.le_succ k) hx
      have hyk : y ∈ (U.energyPower k).domain := LinearPMap.mem_domain_of_mem_graph hyz
      have hcomm := SymmetricOperator.conjugationIntegral_generator_graph U.conformalHamiltonian
        (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (f (j+1))
        (hf j) (hf (j+1)) (C j) (C (j+1)) (hC j) (hC (j+1))
        (hd j) (ha j) (hb j) ((U.energyOne_graph_iff x y).mp hxy)
      change (F j x,F j (y-x)+Complex.I • F (j+1) x) ∈ U.conformalHamiltonian.graph at hcomm
      have h1 : (F j x,F j y+Complex.I • F (j+1) x) ∈ (U.energyPower 1).graph := by
        rw [U.energyOne_graph_iff]
        simpa only [map_sub,sub_add_eq_add_sub] using hcomm
      have hu : F j y+Complex.I • F (j+1) x ∈ (U.energyPower k).domain :=
        (U.energyPower k).domain.add_mem (ih j y hyk)
          ((U.energyPower k).domain.smul_mem Complex.I (ih (j+1) x hxk))
      obtain ⟨w,huw⟩ := LinearPMap.mem_domain_iff.mp hu
      have hfull := (U.energyPower_add_graph 1 k (F j x) w).mpr ⟨_,h1,huw⟩
      apply LinearPMap.mem_domain_of_mem_graph
      simpa only [Nat.add_comm] using hfull
lemma conjugationIntegral_smooth (Q : Completion V →L[ℂ] Completion V)
    (a b : ℝ) (f : ℕ → ℝ → ℂ) (hf : ∀ j, Continuous (f j))
    (C : ℕ → ℝ) (hC : ∀ j t, ‖f j t‖ ≤ C j)
    (hd : ∀ j t, HasDerivAt (f j) (f (j+1) t) t)
    (ha : ∀ j, f j a=0) (hb : ∀ j, f j b=0)
    (j : ℕ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.conjugationIntegral U.conformalHamiltonian
      (U.energyOperator_selfAdjoint (fun d => d)) Q a b (f j) (hf j) (C j) (hC j) x ∈
        U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  exact fun k => U.conjugationIntegral_energy_domain Q a b f hf C hC hd ha hb k j x (hx k)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Filter
open scoped Topology ContDiff
namespace StronglyRationalVOA.SmoothRotationKernel
def bump (ε : ℝ) (hε : 0 < ε) : ContDiffBump (0 : ℝ) :=
  ⟨ε/2,ε,by linarith,by linarith⟩
def kernel (ε : ℝ) (hε : 0 < ε) : ℝ → ℝ := (bump ε hε).normed volume
lemma nonneg (ε : ℝ) (hε : 0 < ε) (t : ℝ) : 0 ≤ kernel ε hε t :=
  (bump ε hε).nonneg_normed t
lemma integral (ε : ℝ) (hε : 0 < ε) : (∫ t, kernel ε hε t)=1 :=
  (bump ε hε).integral_normed
lemma continuous (ε : ℝ) (hε : 0 < ε) : Continuous (kernel ε hε) :=
  (bump ε hε).continuous_normed
lemma support (ε : ℝ) (hε : 0 < ε) : Function.support (kernel ε hε)=Metric.ball 0 ε :=
  (bump ε hε).support_normed_eq
lemma tsupport (ε : ℝ) (hε : 0 < ε) : tsupport (kernel ε hε)=Metric.closedBall 0 ε :=
  (bump ε hε).tsupport_normed_eq
lemma normed_smooth (ε : ℝ) (hε : 0 < ε) : ContDiff ℝ ∞ (fun t => (kernel ε hε t : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (bump ε hε).contDiff_normed
def jet (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ℝ → ℂ :=
  iteratedDeriv j (fun t => (kernel ε hε t : ℂ))
lemma jet_zero (ε : ℝ) (hε : 0 < ε) (t : ℝ) : jet ε hε 0 t=(kernel ε hε t : ℂ) := rfl
lemma jet_continuous (ε : ℝ) (hε : 0 < ε) (j : ℕ) : Continuous (jet ε hε j) :=
  (normed_smooth ε hε).continuous_iteratedDeriv j (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
lemma jet_derivative (ε : ℝ) (hε : 0 < ε) (j : ℕ) (t : ℝ) :
    HasDerivAt (jet ε hε j) (jet ε hε (j+1) t) t := by
  change HasDerivAt (iteratedDeriv j _) (iteratedDeriv (j+1) _ t) t
  rw [iteratedDeriv_succ]
  exact ((normed_smooth ε hε).differentiable_iteratedDeriv j (by exact_mod_cast ENat.natCast_lt_top j) t).hasDerivAt
lemma jet_support (ε : ℝ) (hε : 0 < ε) (j : ℕ) :
    _root_.tsupport (jet ε hε j) ⊆ Metric.closedBall 0 ε := by
  induction j with
  | zero =>
      change _root_.tsupport (fun t => (kernel ε hε t : ℂ)) ⊆ _
      rw [← tsupport ε hε]
      apply closure_mono
      intro t ht
      exact fun h => ht (by simp only [h,Complex.ofReal_zero])
  | succ j ih =>
      change _root_.tsupport (iteratedDeriv (j+1) _) ⊆ _
      rw [iteratedDeriv_succ]
      change _root_.tsupport (deriv (jet ε hε j)) ⊆ _
      exact tsupport_deriv_subset.trans ih
lemma jet_compactSupport (ε : ℝ) (hε : 0 < ε) (j : ℕ) : HasCompactSupport (jet ε hε j) :=
  (isCompact_closedBall (0 : ℝ) ε).of_isClosed_subset isClosed_closure (jet_support ε hε j)
lemma jet_bounded (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ∃ C : ℝ, ∀ t, ‖jet ε hε j t‖ ≤ C := by
  obtain ⟨C,hC⟩ := ((jet_compactSupport ε hε j).isCompact_range
    (jet_continuous ε hε j)).isBounded.exists_norm_le
  exact ⟨C,fun t => hC _ ⟨t,rfl⟩⟩
def bound (ε : ℝ) (hε : 0 < ε) (j : ℕ) : ℝ := (jet_bounded ε hε j).choose
lemma norm_le_bound (ε : ℝ) (hε : 0 < ε) (j : ℕ) (t : ℝ) :
    ‖jet ε hε j t‖ ≤ bound ε hε j := (jet_bounded ε hε j).choose_spec t
lemma jet_vanish (ε : ℝ) (hε : 0 < ε) (j : ℕ) {t : ℝ} (ht : ε < |t|) : jet ε hε j t=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hh := jet_support ε hε j h
  simp only [Metric.mem_closedBall,Real.dist_eq,sub_zero] at hh
  exact ht.not_ge hh
end StronglyRationalVOA.SmoothRotationKernel

open MeasureTheory Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SmoothRotationKernel
 
def smoothConjugate (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) : H →L[ℂ] H :=
  conjugationIntegral T hs Q (-2*ε) (2*ε) (jet ε hε 0)
    (jet_continuous ε hε 0) (bound ε hε 0) (norm_le_bound ε hε 0)
lemma smoothConjugate_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x : H) :
    smoothConjugate T hs Q ε hε x = ∫ t, kernel ε hε t • conjugation T hs Q t x := by
  change (∫ t in (-2*ε)..(2*ε), (kernel ε hε t : ℂ) • conjugation T hs Q t x)=_
  simp_rw [Complex.coe_smul]
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro t ht
  have hk : kernel ε hε t ≠ 0 := fun h => ht (by simp only [h,zero_smul])
  have hb := (support ε hε).le hk
  simp only [Metric.mem_ball,Real.dist_eq,sub_zero] at hb
  exact ⟨by linarith [(abs_lt.mp hb).1],by linarith [(abs_lt.mp hb).2]⟩
lemma smoothConjugate_norm_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x : H) : ‖smoothConjugate T hs Q ε hε x‖ ≤ ‖Q‖*‖x‖ := by
  rw [smoothConjugate_apply]
  apply (norm_integral_le_integral_norm _).trans
  calc
    _ ≤ ∫ t, kernel ε hε t*(‖Q‖*‖x‖) := integral_mono_of_nonneg
      (Eventually.of_forall (fun t => norm_nonneg _))
      ((bump ε hε).integrable_normed.mul_const _) (Eventually.of_forall (fun t => by
        change ‖kernel ε hε t • conjugation T hs Q t x‖ ≤ kernel ε hε t*(‖Q‖*‖x‖)
        rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (nonneg ε hε t)]
        exact mul_le_mul_of_nonneg_left (conjugation_norm T hs Q t x) (nonneg ε hε t)))
    _ = _ := by rw [integral_mul_const,SmoothRotationKernel.integral,one_mul]
lemma smoothConjugate_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) : ‖smoothConjugate T hs Q ε hε‖ ≤ ‖Q‖ :=
  (smoothConjugate T hs Q ε hε).opNorm_le_bound (norm_nonneg _) (smoothConjugate_norm_apply T hs Q ε hε)
lemma smoothConjugate_strong (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => smoothConjugate T hs Q (r n) (hr n) x) atTop (𝓝 (Q x)) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) (φ := fun n => bump (r n) (hr n)) hl
    ((conjugation_continuous T hs Q x).comp continuous_neg) (0 : ℝ)
  simp only [convolution_def,Function.comp_apply,zero_sub,neg_neg,ContinuousLinearMap.lsmul_apply] at h
  simpa only [smoothConjugate_apply,kernel,conjugation,neg_zero,flow_zero,mul_one,one_mul] using h
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace SmoothRotationKernel
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma smoothConjugate_smooth (Q : Completion V →L[ℂ] Completion V) (ε : ℝ) (hε : 0 < ε)
    {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.smoothConjugate U.conformalHamiltonian
      (U.energyOperator_selfAdjoint (fun d => d)) Q ε hε x ∈ U.smoothEnergySpace := by
  exact U.conjugationIntegral_smooth Q (-2*ε) (2*ε) (jet ε hε)
    (jet_continuous ε hε) (bound ε hε) (norm_le_bound ε hε) (jet_derivative ε hε)
    (fun j => jet_vanish ε hε j (by rw [abs_mul,abs_of_pos hε]; norm_num; linarith))
    (fun j => jet_vanish ε hε j (by rw [abs_mul,abs_of_pos hε]; norm_num; linarith)) 0 hx
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open MeasureTheory Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
open SmoothRotationKernel
lemma conjugation_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H) (t : ℝ) :
    (conjugation T hs Q t).adjoint = conjugation T hs Q.adjoint t := by
  simpa only [conjugation,ContinuousLinearMap.star_eq_adjoint,flow_adjoint,neg_neg,mul_assoc] using
    (star_mul (flow T hs t * Q) (flow T hs (-t))).trans
      (congrArg (fun x : H →L[ℂ] H => star (flow T hs (-t)) * x) (star_mul (flow T hs t) Q))
lemma smoothConjugate_integrable (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x : H) :
    Integrable (fun t => kernel ε hε t • conjugation T hs Q t x) := by
  exact ((continuous ε hε).smul (conjugation_continuous T hs Q x)).integrable_of_hasCompactSupport
    ((bump ε hε).hasCompactSupport_normed.smul_right)
lemma smoothConjugate_inner_right (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (Q : H →L[ℂ] H)
    (ε : ℝ) (hε : 0 < ε) (x y : H) :
    inner ℂ x (smoothConjugate T hs Q ε hε y) =
      ∫ t, (kernel ε hε t : ℂ) * inner ℂ x (conjugation T hs Q t y) := by
  rw [smoothConjugate_apply]
  have h := ((innerSL ℂ x).restrictScalars ℝ).integral_comp_comm
    (smoothConjugate_integrable T hs Q ε hε y)
  change (∫ t, inner ℂ x (kernel ε hε t • conjugation T hs Q t y)) =
    inner ℂ x (∫ t, kernel ε hε t • conjugation T hs Q t y) at h
  simp_rw [← Complex.coe_smul,inner_smul_right] at h
  exact h.symm
end StronglyRationalVOA.SymmetricOperator

end

end OAI
