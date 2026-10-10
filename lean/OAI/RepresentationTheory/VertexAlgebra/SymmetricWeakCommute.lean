import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.TimeAverageGraph

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
open MeasureTheory
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
omit [CompleteSpace H] in
lemma symmetric_weak_commute (D : Submodule ℂ H) (P Q : Module.End ℂ D)
    (hP : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hQ : ∀ x y : D, inner ℂ (Q x:H) (y:H) = inner ℂ (x:H) (Q y:H))
    (hw : ∀ x y : D, inner ℂ (P x:H) (Q y:H) = inner ℂ (Q x:H) (P y:H)) :
    P*Q = Q*P := by
  apply LinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (P (Q x):H) (y:H) = inner ℂ (Q (P x):H) (y:H)
  calc
    inner ℂ (P (Q x):H) (y:H) = inner ℂ (Q x:H) (P y:H) := hP (Q x) y
    _ = inner ℂ (P x:H) (Q y:H) := (hw x y).symm
    _ = inner ℂ (Q (P x):H) (y:H) := (hQ (P x) y).symm

 

lemma graph_entries_commute_of_local_energy
    (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P Q τ : Module.End ℂ D) (M T N : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hMs : M.IsFormalAdjoint M) (hs : IsSelfAdjoint T) (hN : N.IsClosable)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hNcore : N.graph = (D.subtype.prod (D.subtype.comp Q)).range)
    (hPQ : P*Q = Q*P)
    (hflowM : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (hflowN : ∀ t x y, (x,y) ∈ N.closure.graph →
      (flow T hs t x,flow T hs t y) ∈ N.closure.graph)
    (hinv : ∀ r, 0 < r → ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖)
    (i j a b : Bool) :
    ClosedGraphData.entry M hM i j * ClosedGraphData.entry N.closure hN.closure_isClosed a b =
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * ClosedGraphData.entry M hM i j := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hPs (x y : D) : inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H) :=
    formalAdjoint_graph_pairing hMs (hP x) (hP y)
  choose B hB hc hg using fun n => local_energy_regularization D hD P τ M T hM hs hP hτ hPs
    hflowM (r n) (hr n) (hinv (r n) (hr n)) k hC hb
  have hself : IsSelfAdjoint M := selfAdjoint_of_local_energy D hD P τ M T hM hMs hs hP hτ
    hflowM hinv k hC hb
  have hQ (x : D) : ((x:H),(Q x:H)) ∈ N.closure.graph := by
    apply LinearPMap.le_graph_of_le (LinearPMap.le_closure N)
    rw [hNcore]
    exact ⟨x,rfl⟩
  have hreg (n : ℕ) (x y : H) (hxy : (x,y) ∈ M.graph) :
      B n x = ((timeAverage T hs (r n))^k) y := by
    have h := regularizer_adjoint hself.dense_domain _ (B n)
      ((timeAverage_selfAdjoint T hs (r n)).pow k) (hg n)
      (by rwa [show M.adjoint = M from hself])
    rwa [show (B n).adjoint = B n from hB n] at h
  have hBc (n : ℕ) (a b : Bool) :
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * B n =
        B n * ClosedGraphData.entry N.closure hN.closure_isClosed a b := by
    symm
    apply ClosedGraphData.entry_commutes_of_graph_invariant N.closure hN.closure_isClosed (B n) ?_ ?_ a b
    · apply regularization_preserves_closure D P Q
        ((restricted D (timeAverage T hs (r n)) (hinv (r n) (hr n)))^k) (B n)
        (hc n) hPQ
      · apply Commute.pow_left
        exact (restricted_commutes_of_graph D Q _ _ N.closure hQ
          (fun _ _ hxy => timeAverage_preserves_graph T N.closure hs hN.closure_isClosed hflowN (r n) hxy)).symm
      · exact hN
      · exact hNcore
    · rw [show (B n).adjoint = B n from hB n]
      apply regularization_preserves_closure D P Q
        ((restricted D (timeAverage T hs (r n)) (hinv (r n) (hr n)))^k) (B n)
        (hc n) hPQ
      · apply Commute.pow_left
        exact (restricted_commutes_of_graph D Q _ _ N.closure hQ
          (fun _ _ hxy => timeAverage_preserves_graph T N.closure hs hN.closure_isClosed hflowN (r n) hxy)).symm
      · exact hN
      · exact hNcore
  have hRc (n : ℕ) (a b : Bool) :
      ClosedGraphData.entry N.closure hN.closure_isClosed a b * (timeAverage T hs (r n))^k =
        (timeAverage T hs (r n))^k * ClosedGraphData.entry N.closure hN.closure_isClosed a b := by
    apply Commute.pow_right
    apply timeAverage_commutes T hs
    intro t
    symm
    apply ClosedGraphData.entry_commutes_of_graph_invariant N.closure hN.closure_isClosed (flow T hs t)
      (hflowN t) ?_ a b
    rw [flow_adjoint]
    exact hflowN (-t)
  exact graph_entries_commute_of_regularizers M N.closure hM hN.closure_isClosed
    (fun n => (timeAverage T hs (r n))^k) B hg
    (timeAverage_pow_strong_one T hs r hr hl k) hreg hRc hBc i j a b

end StronglyRationalVOA.SymmetricOperator

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def PrimaryLocalEnergyEstimate (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (f : SmoothCircleFunction) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : U.smoothEnergySpace,
    ‖(U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients x : Completion V)‖ ≤
      C*∑ j ∈ Finset.range d,
        ‖(((U.smoothSmear hc A.conformal_mem f.rapid_coefficients)^j) x : Completion V)‖

include U in
lemma stress_physical_bound (n : ℤ) (v : V) :
    ‖A.physicalMode A.conformalVector 2 n v‖ ≤
      (1+A.centralCharge.re)*(1+|(n : ℝ)|)^2*‖A.energyShift v‖ := by
  simpa only [physicalMode,virasoroMode,Nat.cast_ofNat,show n+(2 : ℤ)-1=n+1 by omega]
    using U.virasoro_linear_energy n v

lemma stress_hermitian : U.IsHermitian 2 A.conformalVector := by
  simp [IsHermitian,U.pct_conformal]

lemma stress_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {f : SmoothCircleFunction} (hf : f.IsReal) :
    IsSelfAdjoint (U.closedSmoothField hc A.conformalVector 2 f) :=
  U.smearedCore_essentialSelfAdjoint A.conformal_mem A.conformal_quasiPrimary U.stress_hermitian
    (U.polynomialEnergyBounds hc A.conformalVector) U.stress_physical_bound f.rapid_coefficients
    (SmoothCircleFunction.coefficient_real hf)

lemma closedSmoothField_symmetric (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a)
    (hh : U.IsHermitian d a) {f : SmoothCircleFunction} (hf : f.IsReal) :
    (U.closedSmoothField hc a d f).IsFormalAdjoint (U.closedSmoothField hc a d f) := by
  exact SymmetricOperator.formalAdjoint_closure (U.smoothSmearedField_closable hc ha f)
    (U.smoothSmearedField_closable hc ha f)
    (HilbertCore.formalAdjoint (U.smearedMap_symmetric ha hq hh
      (U.polynomialEnergyBounds hc a) f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)))

lemma primary_power_graph_stressFlow (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d)
    {f : SmoothCircleFunction} (hf : f.IsReal) (t : ℝ)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d (f.power (d-1))).graph) :
    (SymmetricOperator.flow (U.closedSmoothField hc A.conformalVector 2 f)
        (U.stress_selfAdjoint hc hf) t x,
      SymmetricOperator.flow (U.closedSmoothField hc A.conformalVector 2 f)
        (U.stress_selfAdjoint hc hf) t y) ∈
      (U.closedSmoothField hc a d (f.power (d-1))).graph := by
  exact U.highField_graph_invariant_firstOrderFlow_of_weak hc ha A.conformal_mem
    (hp 1 (by norm_num)) A.conformal_quasiPrimary hh U.stress_hermitian
    (by linarith [U.centralCharge_nonneg]) U.stress_physical_bound
    (SmoothCircleFunction.power_real hf (d-1)) hf
    (fun v w => (U.primary_stress_weakCommutation hc ha hp hh hd hf v w).symm) t hxy

lemma stress_timeAverage_smooth (hc : A.toVertexAlgebra.C2Cofinite)
    {f : SmoothCircleFunction} (hf : f.IsReal) (r : ℝ) {x : Completion V}
    (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.timeAverage (U.closedSmoothField hc A.conformalVector 2 f)
      (U.stress_selfAdjoint hc hf) r x ∈ U.smoothEnergySpace := by
  exact U.firstOrderSmear_timeAverage_smoothEnergySpace A.conformal_mem
    A.conformal_quasiPrimary U.stress_hermitian (U.polynomialEnergyBounds hc A.conformalVector)
    (by linarith [U.centralCharge_nonneg]) U.stress_physical_bound f.rapid_coefficients
    (SmoothCircleFunction.coefficient_real hf) r hx

 

theorem primary_power_selfAdjoint_of_localEstimate (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d)
    {f : SmoothCircleFunction} (hf : f.IsReal)
    (hlocal : U.PrimaryLocalEnergyEstimate hc ha f) :
    IsSelfAdjoint (U.closedSmoothField hc a d (f.power (d-1))) := by
  obtain ⟨C,hC,hb⟩ := hlocal
  apply SymmetricOperator.selfAdjoint_of_local_energy U.smoothEnergySpace U.smoothEnergySpace_dense
    (U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients)
    (U.smoothSmear hc A.conformal_mem f.rapid_coefficients)
    _ _ (U.closedSmoothField_isClosed hc ha _) 
    (U.closedSmoothField_symmetric hc ha (hp 1 (by norm_num)) hh
      (SmoothCircleFunction.power_real hf (d-1))) (U.stress_selfAdjoint hc hf)
    (U.smoothSmear_graph hc ha _) (U.smoothSmear_graph hc A.conformal_mem _)
    (fun t _ _ hxy => U.primary_power_graph_stressFlow hc ha hp hh hd hf t hxy)
    (fun r _ x => U.stress_timeAverage_smooth hc hf r x.property) (d-1) hC
  simpa only [Nat.sub_add_cancel hd] using hb
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction
lemma power_tsupport_subset (f : SmoothCircleFunction) {k : ℕ} (hk : k ≠ 0) :
    tsupport (f.power k) ⊆ tsupport f := by
  apply closure_mono
  intro t ht
  contrapose! ht
  simp only [Function.mem_support, ne_eq, not_not] at ht ⊢
  simpa only [power_apply,ht] using zero_pow hk
end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_core_closable (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha hf)).IsClosable := by
  apply (U.smearedCore_closable hc ha hf).closure_isClosed.isClosable.leIsClosable
  apply LinearPMap.le_of_le_graph
  intro p hp
  obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
  have he : ((x : Completion V),(U.smoothSmear hc ha hf x : Completion V)) = p := Prod.ext hx hy
  rw [← he]
  exact U.smoothSmear_graph hc ha hf x

 

theorem primary_power_graph_locality_of_localEstimate (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hp : A.IsPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b) (hd : 2 ≤ d)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g))
    (hlocal : U.PrimaryLocalEnergyEstimate hc ha f) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j *
      ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l =
    ClosedGraphData.entry (U.closedSmoothField hc b e g)
        (U.closedSmoothField_isClosed hc hb _) k l *
      ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
        (U.closedSmoothField_isClosed hc ha _) i j := by
  obtain ⟨C,hC,hbound⟩ := hlocal
  have hfp := SmoothCircleFunction.power_real hf (d-1)
  have hsupport : Disjoint (tsupport (f.power (d-1))) (tsupport g) :=
    hfg.mono_left (SmoothCircleFunction.power_tsupport_subset f (by omega))
  let Q := U.smoothSmear hc hb g.rapid_coefficients
  let N := SymmetricOperator.onSubmodule U.smoothEnergySpace Q
  have hN : N.IsClosable := U.smoothSmear_core_closable hc hb g.rapid_coefficients
  have hNeq : N.closure = U.closedSmoothField hc b e g := U.smoothSmear_core hc hb g.rapid_coefficients
  have hPQ := SymmetricOperator.symmetric_weak_commute U.smoothEnergySpace
    (U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients) Q
    (U.smoothSmear_symmetric hc ha (hp 1 (by norm_num)) hha _ (SmoothCircleFunction.coefficient_real hfp))
    (U.smoothSmear_symmetric hc hb hqb hhb _ (SmoothCircleFunction.coefficient_real hg))
    (U.smoothSmear_weakCommutation hc ha hb (hp 1 (by norm_num)) hqb hha hhb hfp hg hsupport)
  have he := SymmetricOperator.graph_entries_commute_of_local_energy U.smoothEnergySpace
    U.smoothEnergySpace_dense (U.smoothSmear hc ha (f.power (d-1)).rapid_coefficients) Q
    (U.smoothSmear hc A.conformal_mem f.rapid_coefficients)
    (U.closedSmoothField hc a d (f.power (d-1))) (U.closedSmoothField hc A.conformalVector 2 f) N
    (U.closedSmoothField_isClosed hc ha _)
    (U.closedSmoothField_symmetric hc ha (hp 1 (by norm_num)) hha hfp)
    (U.stress_selfAdjoint hc hf) hN (U.smoothSmear_graph hc ha _)
    (U.smoothSmear_graph hc A.conformal_mem _) (SymmetricOperator.onSubmodule_graph _ Q) hPQ
    (fun t _ _ hxy => U.primary_power_graph_stressFlow hc ha hp hha (by omega) hf t hxy)
    (fun t x y hxy => by
      rw [hNeq] at hxy ⊢
      exact U.highField_graph_invariant_firstOrderFlow hc hb A.conformal_mem hqb
        A.conformal_quasiPrimary hhb U.stress_hermitian (by linarith [U.centralCharge_nonneg])
        U.stress_physical_bound hg hf hfg.symm t hxy)
    (fun r _ x => U.stress_timeAverage_smooth hc hf r x.property) (d-1) hC
    (by simpa only [Nat.sub_add_cancel (show 1 ≤ d by omega)] using hbound) i j k l
  simpa only [hNeq] using he
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.LocalCovariance
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

 

lemma shifted_power_graph_bound (T : Module.End ℂ E) (c : ℂ) {M : ℝ}
    (hc : ‖c‖ ≤ M) (k : ℕ) (x : E) :
    ‖((T+c • (1 : Module.End ℂ E))^k) x‖ ≤
      (1+M)^k*∑ j ∈ Finset.range (k+1), ‖(T^j) x‖ := by
  have hM : 0 ≤ M := (norm_nonneg _).trans hc
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have hshift : (∑ j ∈ Finset.range (k+1), ‖(T^j) (T x)‖) ≤
        ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖ := by
      have he (j : ℕ) : (T^j) (T x) = (T^(j+1)) x := by rw [pow_succ]; rfl
      simp_rw [he]
      rw [Finset.sum_range_succ' (fun j => ‖(T^j) x‖) (k+1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    have hold : (∑ j ∈ Finset.range (k+1), ‖(T^j) x‖) ≤
        ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖ := by
      rw [Finset.sum_range_succ (fun j => ‖(T^j) x‖) (k+1)]
      exact le_add_of_nonneg_right (norm_nonneg _)
    let S := ∑ j ∈ Finset.range (k+2), ‖(T^j) x‖
    have hs : 0 ≤ S := Finset.sum_nonneg fun _ _ => norm_nonneg _
    have he : ((T+c • (1 : Module.End ℂ E))^(k+1)) x =
        ((T+c • (1 : Module.End ℂ E))^k) (T x) +
          c • ((T+c • (1 : Module.End ℂ E))^k) x := by
      rw [pow_succ]
      change ((T+c • (1 : Module.End ℂ E))^k) (T x+c • x) = _
      rw [map_add,map_smul]
    rw [he]
    calc
      _ ≤ ‖((T+c • (1 : Module.End ℂ E))^k) (T x)‖ +
          ‖c • ((T+c • (1 : Module.End ℂ E))^k) x‖ := norm_add_le _ _
      _ ≤ (1+M)^k*S + M*((1+M)^k*S) := by
        rw [norm_smul]
        apply add_le_add
        · exact (ih (T x)).trans (mul_le_mul_of_nonneg_left hshift (by positivity))
        · exact mul_le_mul hc ((ih x).trans (mul_le_mul_of_nonneg_left hold (by positivity)))
            (norm_nonneg _) hM
      _ = (1+M)^(k+1)*S := by rw [pow_succ]; ring

 

lemma bound_of_unitary_covariance (e : E ≃ₗᵢ[ℂ] E)
    (P P₀ T L : Module.End ℂ E) (k : ℕ) {α β C M : ℝ}
    (hC : 0 ≤ C) (hs : |α-β| ≤ M)
    (hglobal : ∀ x, ‖P₀ x‖ ≤ C*‖(((1 : Module.End ℂ E)+L)^k) x‖)
    (hP : ∀ x, e (P x) = ((α:ℂ)^k) • P₀ (e x))
    (hT : ∀ x, e (T x) = (α:ℂ) • L (e x) + (β:ℂ) • e x) (x : E) :
    ‖P x‖ ≤ C*(1+M)^k*∑ j ∈ Finset.range (k+1), ‖(T^j) x‖ := by
  let K : Module.End ℂ E := T+((α-β:ℝ):ℂ) • 1
  have hK (z : E) : e (K z) = (α:ℂ) • (((1 : Module.End ℂ E)+L) (e z)) := by
    change e (T z+((α-β:ℝ):ℂ) • z) = _
    rw [map_add,map_smul,hT]
    simp only [LinearMap.add_apply,Module.End.one_apply,Complex.ofReal_sub,smul_add,sub_smul]
    module
  have hpow (j : ℕ) (z : E) : e ((K^j) z) = (α:ℂ)^j • ((((1 : Module.End ℂ E)+L)^j) (e z)) := by
    induction j generalizing z with
    | zero => simp
    | succ j ih =>
      rw [pow_succ',Module.End.mul_apply,hK,ih,map_smul]
      simp only [pow_succ',Module.End.mul_apply,mul_smul]
  have hn : ‖P x‖ ≤ C*‖(K^k) x‖ := by
    rw [← e.norm_map (P x),hP,norm_smul,← e.norm_map ((K^k) x),hpow,norm_smul]
    calc
      _ ≤ ‖(α:ℂ)^k‖*(C*‖(((1 : Module.End ℂ E)+L)^k) (e x)‖) :=
        mul_le_mul_of_nonneg_left (hglobal (e x)) (norm_nonneg _)
      _ = _ := by ring
  have hc : ‖((α-β:ℝ):ℂ)‖ ≤ M := by simpa only [Complex.norm_real,Real.norm_eq_abs] using hs
  exact hn.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left (shifted_power_graph_bound T ((α-β:ℝ):ℂ) hc k x) hC)
end StronglyRationalVOA.LocalCovariance

open MeasureTheory Set
open scoped ContDiff
namespace StronglyRationalVOA.PositiveCircleGeometry

 

structure Field (T : ℝ) where
  toFun : ℝ → ℝ
  periodic : Function.Periodic toFun T
  smooth : ContDiff ℝ ∞ toFun
  positive : ∀ x, 0 < toFun x
instance {T : ℝ} : CoeFun (Field T) (fun _ => ℝ → ℝ) := ⟨Field.toFun⟩
namespace Field
variable {T : ℝ} (f : Field T)

def totalTime : ℝ := ∫ t in 0..T, (f t)⁻¹

def normalizedCoordinate (x : ℝ) : ℝ := (totalTime f)⁻¹ * ∫ t in 0..T*x, (f t)⁻¹

lemma inverse_continuous : Continuous (fun t => (f t)⁻¹) :=
  f.smooth.continuous.inv₀ (fun t => ne_of_gt (f.positive t))

lemma totalTime_pos (hT : 0 < T) : 0 < totalTime f := by
  apply intervalIntegral.integral_pos hT f.inverse_continuous.continuousOn
    (fun t _ => (inv_pos.mpr (f.positive t)).le)
  exact ⟨0,⟨le_rfl,hT.le⟩,inv_pos.mpr (f.positive 0)⟩

lemma coordinate_hasDerivAt (x : ℝ) :
    HasDerivAt (normalizedCoordinate f)
      ((totalTime f)⁻¹ * ((f (T*x))⁻¹ * T)) x := by
  have hi := intervalIntegral.integral_hasDerivAt_right
    (f.inverse_continuous.intervalIntegrable 0 (T*x))
    f.inverse_continuous.stronglyMeasurable.stronglyMeasurableAtFilter f.inverse_continuous.continuousAt
  convert (hi.comp x ((hasDerivAt_id x).const_mul T)).const_mul (totalTime f)⁻¹ using 1 <;> first | rfl | simp only [mul_one]

lemma coordinate_derivative_pos (hT : 0 < T) (x : ℝ) :
    0 < (totalTime f)⁻¹ * ((f (T*x))⁻¹ * T) := by
  exact mul_pos (inv_pos.mpr (f.totalTime_pos hT)) (mul_pos (inv_pos.mpr (f.positive _)) hT)

lemma coordinate_strictMono (hT : 0 < T) : StrictMono (normalizedCoordinate f) :=
  strictMono_of_deriv_pos fun x => by
    rw [(f.coordinate_hasDerivAt x).deriv]
    exact f.coordinate_derivative_pos hT x

lemma coordinate_add_one (hT : 0 < T) (x : ℝ) :
    normalizedCoordinate f (x+1) = normalizedCoordinate f x+1 := by
  have hp : Function.Periodic (fun t => (f t)⁻¹) T := fun _ => congrArg Inv.inv (f.periodic _)
  have he := hp.intervalIntegral_add_eq_add 0 (T*x)
    (fun a b => f.inverse_continuous.intervalIntegrable a b)
  simp only [zero_add] at he
  dsimp only [normalizedCoordinate]
  rw [mul_add,mul_one,he,mul_add,← totalTime,inv_mul_cancel₀ (ne_of_gt (f.totalTime_pos hT))]

def circleLift (hT : 0 < T) : CircleDeg1Lift where
  toFun := normalizedCoordinate f
  monotone' := (f.coordinate_strictMono hT).monotone
  map_add_one' := f.coordinate_add_one hT

lemma coordinate_smooth : ContDiff ℝ ∞ (normalizedCoordinate f) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (f.coordinate_hasDerivAt x).differentiableAt,?_⟩
  have he : deriv (normalizedCoordinate f) =
      fun x => (totalTime f)⁻¹*((f (T*x))⁻¹*T) := funext fun x => (f.coordinate_hasDerivAt x).deriv
  rw [he]
  exact contDiff_const.mul (((f.smooth.comp (contDiff_const.mul contDiff_id)).inv (fun x => ne_of_gt (f.positive (T*x)))).mul contDiff_const)

lemma coordinate_surjective (hT : 0 < T) : Function.Surjective (normalizedCoordinate f) :=
  (f.circleLift hT).continuous_iff_surjective.mp f.coordinate_smooth.continuous

def coordinateOrderIso (hT : 0 < T) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfRightInverse (normalizedCoordinate f) (f.coordinate_strictMono hT)
    (Function.surjInv (f.coordinate_surjective hT))
    (Function.rightInverse_surjInv (f.coordinate_surjective hT))

@[simp] lemma coordinateOrderIso_apply (hT : 0 < T) (x : ℝ) :
    f.coordinateOrderIso hT x = normalizedCoordinate f x := rfl

lemma inverse_coordinate_smooth (hT : 0 < T) : ContDiff ℝ ∞ (f.coordinateOrderIso hT).symm := by
  apply (f.coordinateOrderIso hT).toHomeomorph.contDiff_symm_deriv
    (fun x => ne_of_gt (f.coordinate_derivative_pos hT x)) (f.coordinate_hasDerivAt)
  exact f.coordinate_smooth
end Field
end StronglyRationalVOA.PositiveCircleGeometry

namespace StronglyRationalVOA.PositiveCircleGeometry.Field
variable {T : ℝ} (f : Field T)

def frequency : ℝ := T / f.totalTime
lemma frequency_pos (hT : 0 < T) : 0 < f.frequency := div_pos hT (f.totalTime_pos hT)

lemma frequency_le (hT : 0 < T) {M : ℝ} (hM : 0 < M)
    (hb : ∀ x ∈ Icc 0 T, f x ≤ M) : f.frequency ≤ M := by
  have hI : T/M ≤ f.totalTime := by
    have h := intervalIntegral.integral_mono_on (μ := volume) hT.le
      (continuous_const.intervalIntegrable 0 T) (f.inverse_continuous.intervalIntegrable 0 T)
      (fun x hx => (inv_anti₀ (f.positive x) (hb x hx)))
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,div_eq_mul_inv,one_div,totalTime] using h
  apply (div_le_iff₀ (f.totalTime_pos hT)).mpr
  have h := (div_le_iff₀ hM).mp hI
  simpa only [mul_comm] using h

 

lemma flatten_identity (hT : 0 < T) (x : ℝ) :
    deriv f.normalizedCoordinate x * f (T*x) = f.frequency := by
  rw [(f.coordinate_hasDerivAt x).deriv]
  dsimp only [frequency]
  field_simp [ne_of_gt (f.positive (T*x)),ne_of_gt (f.totalTime_pos hT)]

 

def stressScalar (c : ℝ) : ℝ :=
  c/24*((T⁻¹*∫ x in 0..T,f x)-f.frequency-
    T⁻¹*∫ x in 0..T,(deriv f x)^2/f x)

end StronglyRationalVOA.PositiveCircleGeometry.Field

namespace StronglyRationalVOA.PositiveCircleGeometry
variable {T : ℝ} {g : ℝ → ℝ}

 
def quadraticField (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g) {ε : ℝ} (hε : 0 < ε) : Field T where
  toFun := fun x => g x^2+ε
  periodic := fun _ => by dsimp only; rw [hp]
  smooth := (hs.pow 2).add contDiff_const
  positive := fun x => by nlinarith [sq_nonneg (g x)]

lemma quadratic_derivative (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    deriv (quadraticField hp hs hε) x = 2*g x*deriv g x := by
  have h := (((hs.differentiable (by norm_num)).differentiableAt (x := x)).hasDerivAt.pow 2).add_const ε
  simpa only [Nat.cast_ofNat,show 2-1=1 from rfl,pow_one,Pi.pow_apply,quadraticField] using h.deriv

lemma quadratic_logDerivative_bound (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g)
    {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    (deriv (quadraticField hp hs hε) x)^2 / quadraticField hp hs hε x ≤
      4*(deriv g x)^2 := by
  rw [quadratic_derivative]
  apply (div_le_iff₀ ((quadraticField hp hs hε).positive x)).mpr
  change (2*g x*deriv g x)^2 ≤ 4*(deriv g x)^2*(g x^2+ε)
  nlinarith [mul_nonneg hε.le (sq_nonneg (deriv g x))]

lemma quadratic_frequency_bound (hp : Function.Periodic g T) (hs : ContDiff ℝ ∞ g)
    (hT : 0 < T) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {M : ℝ}
    (hM : ∀ x ∈ Icc 0 T, ‖g x‖ ≤ M) :
    (quadraticField hp hs hε).frequency ≤ M^2+1 := by
  apply Field.frequency_le _ hT (by positivity)
  intro x hx
  have he : (g x)^2 ≤ M^2 := by
    have hh := hM x hx
    rw [Real.norm_eq_abs] at hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) ((abs_nonneg _).trans hh)).mpr hh
    simpa only [sq_abs] using hsq
  change g x^2+ε ≤ M^2+1
  linarith
end StronglyRationalVOA.PositiveCircleGeometry

open MeasureTheory Set Filter
open scoped Topology Interval
namespace StronglyRationalVOA.TimeOrdered
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

 
def term (K : ℝ → A) : ℕ → ℝ → A
  | 0, _ => 1
  | n+1, t => ∫ s in 0..t, K s*term K n s
end StronglyRationalVOA.TimeOrdered

end

end OAI
