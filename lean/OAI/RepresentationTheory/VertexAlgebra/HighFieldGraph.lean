import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.CoefficientDifferentiated
import OAI.RepresentationTheory.VertexAlgebra.RegularizerFactorAdd

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
theorem highField_graph_invariant_firstOrderFlow (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (t : ℝ)
    {x y : Completion V} (hxy : (x,y) ∈ (U.closedSmoothField hc a d f).graph) :
    let hs := U.smearedCore_essentialSelfAdjoint hb hqb hhb (U.polynomialEnergyBounds hc b)
      hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    (SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t x,
      SymmetricOperator.flow (U.closedSmoothField hc b e g) hs t y) ∈
        (U.closedSmoothField hc a d f).graph := by
  classical
  dsimp only
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  let T := (HilbertCore.operator N).closure
  let hs : IsSelfAdjoint T := U.smearedCore_essentialSelfAdjoint hb hqb hhb
    (U.polynomialEnergyBounds hc b) hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
  obtain ⟨C,hC,q,k,hmb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let r := k+1
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^q)*C)*‖(A.energyShift^r) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hmb v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^p)*D)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hbnd
    exact (A.smearedMap_bound _ g.rapid_coefficients hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : 1 ≤ r) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD))
  let K := U.smearedPowerCommutator hb (U.polynomialEnergyBounds hc b) g.rapid_coefficients r
  have hk := U.smearedPowerCommutator_bound hb (U.polynomialEnergyBounds hc b) hD hbnd g.rapid_coefficients r
  have hpair := U.smearedPowerCommutator_pairing hb hqb hhb (U.polynomialEnergyBounds hc b)
    g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) r
  have hcM := U.smearedCore_closable hc ha f.rapid_coefficients
  have hcN := U.smearedCore_closable hc hb g.rapid_coefficients
  choose B hB hBnd using fun s => SymmetricOperator.flow_regularizer_factor T hs
    (U.inverseSobolev r) (U.sobolevExtension r N) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r N hn hcN)
    (U.sobolevExtension_defect r N K hn hk hpair) s
  have hcore (z : U.smoothEnergySpace) :
      (SymmetricOperator.flow T hs t z,
        SymmetricOperator.flow T hs t (U.smoothSmear hc ha f.rapid_coefficients z : Completion V)) ∈
          (U.closedSmoothField hc a d f).graph := by
    exact SymmetricOperator.regularized_commutation_on_dense_core
      (U.closedSmoothField hc a d f) T hs U.smoothEnergySpace U.smoothEnergySpace_dense
      (U.smoothSmear hc ha f.rapid_coefficients) (U.smoothSmear hc hb g.rapid_coefficients)
      (U.smoothSmear_graph hc ha f.rapid_coefficients) (U.smoothSmear_graph hc hb g.rapid_coefficients)
      (U.smoothSmear_symmetric hc ha hqa hha f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf))
      (U.smoothSmear_weakCommutation hc ha hb hqa hqb hha hhb hf hg hfg)
      (U.inverseSobolev r) (U.sobolevExtension r M)
      (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
      (fun z => ⟨U.smoothEnergyPower r z,U.inverseSobolev_smoothEnergyPower r z⟩)
      (U.sobolevExtension_inverse_graph r M hm hcM) B hB (norm_nonneg _) hBnd
      (fun s z => U.firstOrderSmear_flow_smoothEnergySpace hb hqb hhb (U.polynomialEnergyBounds hc b)
        hD hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg) s z.property) t z
  apply SymmetricOperator.graph_invariant_of_core (HilbertCore.operator M) hcM
    (SymmetricOperator.flow T hs t) ?_ hxy
  intro u v huv
  obtain ⟨w,hw,hMw⟩ := (HilbertCore.operator M).mem_graph_iff.mp huv
  obtain ⟨z,rfl⟩ := (HilbertCore.equiv V).surjective w
  have hh := hcore ⟨(z : Completion V),U.core_le_smoothEnergySpace (HilbertCore.equiv V z).property⟩
  rw [U.smoothSmear_coe] at hh
  dsimp only [Prod.fst,Prod.snd] at hw hMw
  rw [← hw,← hMw]
  simpa only [M, closedSmoothField, smoothSmearedField, HilbertCore.operator_apply, HilbertCore.equiv_coe] using hh
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma graph_invariant_of_commutes_flow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  rw [← show T.adjoint = T from hs,LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have h1 := flow_derivative T hs huv 0
  have h2 := (Q.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 (flow_derivative T hs hxy 0)
  have hd := HasDerivAt.inner ℂ h1 h2
  have he (s : ℝ) : inner ℂ (flow T hs s u) (Q (flow T hs s x)) = inner ℂ u (Q x) := by
    have hc := congrArg (fun R : H →L[ℂ] H => R x) (hQ s)
    change Q (flow T hs s x) = flow T hs s (Q x) at hc
    rw [hc,← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
    change inner ℂ u ((flow T hs (-s)*flow T hs s) (Q x)) = _
    rw [← flow_add,neg_add_cancel,flow_zero,one_apply_eq_self]
  simp only [Function.comp_apply, he] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (inner ℂ u (Q x)))
  simp only [flow_zero,one_apply_eq_self] at hz
  change inner ℂ u (Q (Complex.I • y)) + inner ℂ (Complex.I • v) (Q x) = 0 at hz
  rw [map_smul Q,inner_smul_right,inner_smul_left,starRingEnd_apply,Complex.star_def,Complex.conj_I] at hz
  have hi : Complex.I * (inner ℂ u (Q y)-inner ℂ v (Q x)) = 0 := by linear_combination hz
  have heq := (mul_eq_zero.mp hi).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mpr (sub_eq_zero.mp heq).symm

 

lemma graph_entries_commute_of_flow_invariant (A T : H →ₗ.[ℂ] H)
    (hA : A.IsClosed) (hs : IsSelfAdjoint T)
    (hF : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (i j k l : Bool) :
    ClosedGraphData.entry A hA i j * ClosedGraphData.entry T hs.isClosed k l =
      ClosedGraphData.entry T hs.isClosed k l * ClosedGraphData.entry A hA i j := by
  have hC (i j : Bool) (t : ℝ) := ClosedGraphData.entry_commutes_of_graph_invariant A hA
    (flow T hs t) (hF t) (by rw [flow_adjoint]; exact hF (-t)) i j
  have hG (i j : Bool) : ∀ x y, (x,y) ∈ T.graph →
      (ClosedGraphData.entry A hA i j x,ClosedGraphData.entry A hA i j y) ∈ T.graph := by
    intro x y hxy
    exact graph_invariant_of_commutes_flow T hs _ (fun t => (hC i j t).symm) hxy
  apply ClosedGraphData.entry_commutes_of_graph_invariant T hs.isClosed _ (hG i j) ?_ k l
  change ∀ x y, (x,y) ∈ T.graph →
    (star (ClosedGraphData.entry A hA i j) x,star (ClosedGraphData.entry A hA i j) y) ∈ T.graph
  rw [ClosedGraphData.star_entry]
  exact hG j i
end StronglyRationalVOA.SymmetricOperator
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem highField_firstOrder_graph_entries_commute (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j *
        ClosedGraphData.entry (U.closedSmoothField hc b e g) (U.closedSmoothField_isClosed hc hb g) k l =
      ClosedGraphData.entry (U.closedSmoothField hc b e g) (U.closedSmoothField_isClosed hc hb g) k l *
        ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j := by
  let hs := U.smearedCore_essentialSelfAdjoint hb hqb hhb (U.polynomialEnergyBounds hc b)
    hbnd g.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
  exact SymmetricOperator.graph_entries_commute_of_flow_invariant _ _
    (U.closedSmoothField_isClosed hc ha f) hs
    (fun t x y hxy => U.highField_graph_invariant_firstOrderFlow hc ha hb hqa hqb hha hhb
      hD hbnd hf hg hfg t hxy) i j k l

 

theorem highField_stress_graph_entries_commute (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hqa : A.IsQuasiPrimary a) (hha : U.IsHermitian d a)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hfg : Disjoint (tsupport f) (tsupport g)) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j *
        ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 g)
          (U.closedSmoothField_isClosed hc A.conformal_mem g) k l =
      ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 g)
          (U.closedSmoothField_isClosed hc A.conformal_mem g) k l *
        ClosedGraphData.entry (U.closedSmoothField hc a d f) (U.closedSmoothField_isClosed hc ha f) i j := by
  have hn : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian,U.pct_conformal]
  apply U.highField_firstOrder_graph_entries_commute hc ha A.conformal_mem hqa
    A.conformal_quasiPrimary hha hh (p := 2) hn ?_ hf hg hfg i j k l
  intro n v
  simpa only [physicalMode,virasoroMode,Nat.cast_ofNat,show n+(2 : ℤ)-1=n+1 by omega] using U.virasoro_linear_energy n v
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

 

theorem virasoro_primary_physical_commutator {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) (hp : A.IsPrimary a) (m n : ℤ) (v : V) :
    A.virasoroMode m (A.physicalMode a d n v)-
      A.physicalMode a d n (A.virasoroMode m v) =
        (((d : ℂ)-1)*m-n) • A.physicalMode a d (m+n) v := by
  have h := A.toVertexAlgebra.mode_commutator A.conformalVector a v (m+1) (n+d-1)
  have htail (j : ℕ) (hj : 2 ≤ j) : mode A.fields A.conformalVector j a = 0 := by
    have hj1 : ((j-1 : ℕ) : ℤ)+1 = j := by omega
    simpa only [virasoroMode,hj1] using hp (j-1) (by omega)
  have hsum : (∑ᶠ j : ℕ, Ring.choose ((m+1 : ℤ) : ℂ) j •
      mode A.fields (mode A.fields A.conformalVector j a) ((m+1)+(n+d-1)-j) v) =
      ∑ j ∈ Finset.range 2, Ring.choose ((m+1 : ℤ) : ℂ) j •
      mode A.fields (mode A.fields A.conformalVector j a) ((m+1)+(n+d-1)-j) v := by
    apply finsum_eq_sum_of_support_subset
    intro j hj
    simp only [Finset.coe_range,Set.mem_Iio]
    by_contra H
    apply hj
    simp only [htail j (by omega),mode_zero,LinearMap.zero_apply,smul_zero]
  rw [hsum] at h
  have h0 : mode A.fields A.conformalVector 0 a = A.toVertexAlgebra.translation a := by
    rw [A.conformal_translation]
  have h1 : mode A.fields A.conformalVector 1 a = (d : ℂ) • a := A.virasoro_zero_on_grade ha
  have ht := congrArg (fun L : Module.End ℂ V => L v)
    (A.translation_covariance a (m+n+d))
  simp only [LinearMap.smul_apply] at ht
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Ring.choose_zero_right,
    Ring.choose_one_right,one_smul, Nat.cast_zero, Nat.cast_one,h0,h1,mode_smul,LinearMap.smul_apply] at h
  rw [show (m+1)+(n+(d : ℤ)-1)-0 = m+n+d by omega,ht] at h
  change mode A.fields A.conformalVector (m+1) (mode A.fields a (n+d-1) v)-
    mode A.fields a (n+d-1) (mode A.fields A.conformalVector (m+1) v) = _
  rw [h]
  simp only [show (m+1)+(n+(d : ℤ)-1)-1=m+n+d-1 by omega,physicalMode]
  push_cast
  module
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

 

def primarySpace (d : ℕ) : Submodule ℂ V where
  carrier := {a | a ∈ A.grade d ∧ A.IsPrimary a}
  zero_mem' := ⟨(A.grade d).zero_mem,fun _ _ => map_zero _⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨(A.grade d).add_mem ha.1 hb.1,fun n hn => by rw [map_add,ha.2 n hn,hb.2 n hn,add_zero]⟩
  smul_mem' := by
    intro c a ha
    exact ⟨(A.grade d).smul_mem c ha.1,fun n hn => by rw [map_smul,ha.2 n hn,smul_zero]⟩

namespace UnitaryStructure
variable {A} (U : A.UnitaryStructure)
lemma pct_primary {a : V} (ha : A.IsPrimary a) : A.IsPrimary (U.pct a) := by
  intro n hn
  rw [← U.pct_virasoro,ha n hn,map_zero]

 
theorem exists_hermitian_primary_spanning (d : ℕ) :
    ∃ S : Finset V,
      (∀ a ∈ S, a ∈ A.grade d ∧ A.IsPrimary a ∧ U.IsHermitian d a) ∧
      (∀ a ∈ A.grade d, A.IsPrimary a → a ∈ Submodule.span ℂ (S : Set V)) := by
  classical
  let E := A.primarySpace d
  let J := U.hermitianConjugation d
  let H := {a : V | a ∈ E ∧ J a = a}
  have hJin (a : V) (ha : a ∈ E) : J a ∈ E := by
    refine ⟨(A.grade d).smul_mem _ (U.pct_mem_grade ha.1),?_⟩
    intro n hn
    change A.virasoroMode n (((-1 : ℂ)^d) • U.pct a) = 0
    rw [map_smul,U.pct_primary ha.2 n hn,smul_zero]
  have hJ (a : V) : J (J a) = a := U.hermitianConjugation_involutive d a
  have hfix (a : V) (ha : a ∈ E) : a+J a ∈ H := by
    refine ⟨E.add_mem ha (hJin a ha),?_⟩
    rw [map_add,hJ,add_comm]
  have hspan : E ≤ Submodule.span ℂ H := by
    intro a ha
    have hx := Submodule.subset_span (R := ℂ) (hfix a ha)
    have hy := Submodule.subset_span (R := ℂ) (hfix (Complex.I • a) (E.smul_mem _ ha))
    have he : a = (2 : ℂ)⁻¹ • (a+J a) +
        (-Complex.I/2 : ℂ) • (Complex.I • a+J (Complex.I • a)) := by
      rw [map_smulₛₗ,show starRingEnd ℂ Complex.I = -Complex.I from Complex.conj_I]
      simp only [smul_add,smul_smul]
      have hI : (-Complex.I/2 : ℂ)*Complex.I = (2 : ℂ)⁻¹ := by
        rw [div_mul_eq_mul_div,neg_mul,Complex.I_mul_I]
        norm_num
      rw [hI,mul_neg,hI]
      module
    rw [he]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hx) (Submodule.smul_mem _ _ hy)
  let := A.grade_finite d
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le (show E ≤ A.grade d from fun _ h => h.1)
  obtain ⟨T,hT⟩ := Submodule.FG.of_finite (N := E)
  have hTspan : (T : Set V) ⊆ Submodule.span ℂ H := by
    intro a ha
    exact hspan (hT ▸ Submodule.subset_span ha)
  obtain ⟨S,hSH,hTS⟩ := Submodule.subset_span_finite_of_subset_span hTspan
  refine ⟨S,?_,?_⟩
  · intro a ha
    have h := hSH ha
    exact ⟨h.1.1,h.1.2,h.2⟩
  · intro a ha hp
    have hle : E ≤ Submodule.span ℂ (S : Set V) := by
      rw [← hT]
      exact Submodule.span_le.mpr hTS
    exact hle ⟨ha,hp⟩

include U in
 

theorem grade_le_primaryGeneratorFiltration (D : ℕ) (S : ℕ → Set V)
    (hν : A.conformalVector ∈ S 2)
    (hsmall : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsPrimary a → a ∈ Submodule.span ℂ (S d))
    (hcut : ∀ d, D < d → A.grade d ≤ A.toVertexAlgebra.c2) :
    ∀ d, A.grade d ≤ A.generatorFiltration S d := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro a ha
    by_cases hd0 : d=0
    · subst d
      rw [A.grade_zero] at ha
      obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact Submodule.smul_mem _ c (A.vacuum_mem_generatorFiltration S 0)
    by_cases hdD : d ≤ D
    · obtain ⟨q,hq,hp,y,hy,rfl⟩ := U.primary_decomposition ha
      apply Submodule.add_mem
      · have hl : Submodule.span ℂ (S d) ≤ A.generatorFiltration S d := by
          apply Submodule.span_le.mpr
          intro x hx
          change x ∈ A.generatorFiltration S d
          simpa only [A.creation,Nat.add_zero] using
            A.generator_mode_mem hx (A.vacuum_mem_generatorFiltration S 0) (-1)
        exact hl (hsmall d (by omega) hdD q hq hp)
      · have hL : A.lowerVirasoroSpace d ≤ A.generatorFiltration S d := by
          apply iSup_le
          intro n x hx
          obtain ⟨b,hb,rfl⟩ := Submodule.mem_map.mp hx
          have hi := ih (d-(n.val+1)) (by have := n.isLt; omega) hb
          by_cases hn : n.val=0
          · have he : (-(n.val+1 : ℤ)) = -1 := by omega
            rw [he]
            exact A.generatorFiltration_mono S (by omega) (A.translation_mem_generatorFiltration hi)
          · have hgen := A.generator_mode_mem hν hi (-(n.val : ℤ))
            have he : A.virasoroMode (-(n.val+1 : ℤ)) b = mode A.fields A.conformalVector (-(n.val : ℤ)) b := by
              unfold virasoroMode
              rw [show -(n.val+1 : ℤ)+1=-(n.val : ℤ) by omega]
            rw [he]
            exact A.generatorFiltration_mono S (by omega : 2+(d-(n.val+1)) ≤ d) hgen
        exact hL hy
    · have hc : a ∈ A.homogeneousC2 d := by
        rw [A.homogeneousC2_eq]
        exact ⟨hcut d (by omega) ha,ha⟩
      exact A.generatorFiltration_mono S (by omega : d-1 ≤ d)
        (A.homogeneousC2_le_generatorFiltration d ih hc)
 

theorem exists_primary_generating_filtration (hc : A.toVertexAlgebra.C2Cofinite) :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ S : ℕ → Finset V,
      (∀ d, d = 0 ∨ D < d → S d = ∅) ∧
      (∀ d, ∀ a ∈ S d, 1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        (A.IsPrimary a ∨ (d = 2 ∧ a = A.conformalVector)) ∧ U.IsHermitian d a) ∧
      (∀ w, A.grade w ≤ A.homogeneousNegativeFiltration (fun d => (S d : Set V)) w w) := by
  classical
  obtain ⟨D,hD,hcut⟩ := A.exists_c2_weight_cutoff hc
  choose R hR hspan using U.exists_hermitian_primary_spanning
  let G : ℕ → Finset V := fun d => if 1 ≤ d ∧ d ≤ D then R d else ∅
  let S : ℕ → Finset V := fun d => G d ∪ if d = 2 then {A.conformalVector} else ∅
  let T : ℕ → Set V := fun d => (S d : Set V)
  have hS (d : ℕ) (a : V) (ha : a ∈ S d) :
      1 ≤ d ∧ d ≤ D ∧ a ∈ A.grade d ∧
        (A.IsPrimary a ∨ (d=2 ∧ a=A.conformalVector)) ∧ U.IsHermitian d a := by
    change a ∈ G d ∪ (if d=2 then {A.conformalVector} else ∅) at ha
    rcases Finset.mem_union.mp ha with hleft | hright
    · dsimp only [G] at hleft
      split_ifs at hleft with hcond
      · have hr := hR d a hleft
        exact ⟨hcond.1,hcond.2,hr.1,Or.inl hr.2.1,hr.2.2⟩
      · simp at hleft
    · split_ifs at hright with htwo
      · subst d
        have hea : a = A.conformalVector := Finset.mem_singleton.mp hright
        subst a
        exact ⟨by omega,hD,A.conformal_mem,Or.inr ⟨rfl,rfl⟩,by simp [IsHermitian,U.pct_conformal]⟩
      · simp at hright
  have hGT : ∀ d, ∀ a ∈ T d, 1 ≤ d ∧ a ∈ A.grade d := by
    intro d a ha
    have h := hS d a ha
    exact ⟨h.1,h.2.2.1⟩
  have hT : ∀ d, ∀ a ∈ T d, a ∈ A.grade d := fun d a ha => (hGT d a ha).2
  have hν : A.conformalVector ∈ T 2 := by simp [T,S]
  have hQ : ∀ d, 1 ≤ d → d ≤ D → ∀ a ∈ A.grade d, A.IsPrimary a → a ∈ Submodule.span ℂ (T d) := by
    intro d hd hdD a ha hp
    apply (Submodule.span_mono (show (R d : Set V) ⊆ T d from ?_)) (hspan d a ha hp)
    intro x hx
    have hg : x ∈ G d := by
      dsimp only [G]
      rw [ite_eq_left ⟨hd,hdD⟩]
      exact hx
    exact Finset.mem_union_left _ hg
  have hgen := U.grade_le_primaryGeneratorFiltration D T hν hQ hcut
  have hEq := A.generatorFiltration_eq_negativeFiltration hGT hgen
  refine ⟨D,hD,S,?_,hS,?_⟩
  · intro d hd
    have hd2 : d ≠ 2 := by omega
    have hdn : ¬ (1 ≤ d ∧ d ≤ D) := by omega
    simp only [S,G,ite_eq_right hd2,ite_eq_right hdn,Finset.union_empty]
  · intro w a ha
    change a ∈ A.homogeneousNegativeFiltration T w w
    rw [A.homogeneousNegativeFiltration_eq hT,← hEq]
    exact ⟨hgen w ha,ha⟩

end UnitaryStructure
end StronglyRationalVOA.CFTTypeVOA

open scoped ContDiff
namespace StronglyRationalVOA.SmoothCircleFunction

 
def power (f : SmoothCircleFunction) (k : ℕ) : SmoothCircleFunction :=
  ⟨fun t => f t^k,fun t => by dsimp only; rw [f.periodic],f.smooth.pow k⟩

@[simp] lemma power_apply (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) : f.power k t = f t^k := rfl

lemma power_real {f : SmoothCircleFunction} (hf : f.IsReal) (k : ℕ) : (f.power k).IsReal := by
  intro t
  change star (f t^k) = f t^k
  rw [star_pow,hf t]

lemma derivative_power_balance (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    (k : ℂ)*deriv f t*(f.power k t) = f t*deriv (f.power k) t := by
  have hd : DifferentiableAt ℝ (f : ℝ → ℂ) t :=
    (f.smooth.differentiable (by norm_num)).differentiableAt
  change (k : ℂ)*deriv f t*f t^k = f t*deriv ((f : ℝ → ℂ)^k) t
  rw [(hd.hasDerivAt.pow k).deriv]
  cases k with
  | zero => simp
  | succ k =>
    simp only [Nat.add_sub_cancel,pow_succ]
    ring

 

lemma hasSum_power_commutator_zero (f : SmoothCircleFunction) (k : ℕ) (r : ℤ) :
    HasSum (fun m : ℤ => ((k : ℂ)*m-(r-m))*f.coefficient m*(f.power k).coefficient (r-m)) 0 := by
  have h1 := ((f.differentiated 1).coefficient_mul (f.power k) r).mul_left (k : ℂ)
  have h2 := f.coefficient_mul ((f.power k).differentiated 1) r
  have he : (k : ℂ)*((f.differentiated 1).mul (f.power k)).coefficient r =
      (f.mul ((f.power k).differentiated 1)).coefficient r := by
    change (k : ℂ)*fourierCoeffOn period_pos _ r = fourierCoeffOn period_pos _ r
    rw [← smul_eq_mul,← fourierCoeffOn.const_smul]
    congr 1
    ext t
    simp only [Pi.smul_apply,smul_eq_mul,mul_apply,differentiated_apply,iteratedDeriv_one]
    simpa only [mul_assoc] using f.derivative_power_balance k t
  have h := (h1.sub h2).mul_left (-Complex.I)
  rw [he,sub_self,mul_zero] at h
  apply h.congr_fun
  intro m
  simp only [coefficient_differentiated,pow_one]
  push_cast
  ring_nf
  norm_num [Complex.I_sq]
  ring
end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (A : CFTTypeVOA V)

lemma hasSum_primary_stress_commutator_zero {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (hp : A.IsPrimary a) (hd : 1 ≤ d) (f : SmoothCircleFunction) (r : ℤ) (x y : V) :
    HasSum (fun m : ℤ => f.coefficient m*(f.power (d-1)).coefficient (r-m)*
      inner ℂ x (A.physicalMode A.conformalVector 2 m (A.physicalMode a d (r-m) y)-
        A.physicalMode a d (r-m) (A.physicalMode A.conformalVector 2 m y))) 0 := by
  have h := (f.hasSum_power_commutator_zero (d-1) r).mul_right
    (inner ℂ x (A.physicalMode a d r y))
  simp only [zero_mul] at h
  apply h.congr_fun
  intro m
  rw [show A.physicalMode A.conformalVector 2 m = A.virasoroMode m by
    unfold physicalMode virasoroMode; congr 1; omega]
  rw [A.virasoro_primary_physical_commutator ha hp,inner_smul_right]
  rw [show m+(r-m)=r by omega]
  rw [Nat.cast_sub hd,Nat.cast_one]
  push_cast
  ring
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smearedMap_weakCommutation_of_convolution {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    (hea : A.PolynomialEnergyBound a) (heb : A.PolynomialEnergyBound b)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hzero : ∀ r : ℤ, ∀ x y : V,
      HasSum (fun m : ℤ => f.coefficient m*g.coefficient (r-m)*
        inner ℂ x (A.physicalMode a d m (A.physicalMode b e (r-m) y)-
          A.physicalMode b e (r-m) (A.physicalMode a d m y))) 0) (x y : V) :
    inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
      (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
    inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
      (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
  have Hhom (D E : ℕ) (x y : V) (hx : x ∈ A.grade D) (hy : y ∈ A.grade E) :
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y) := by
    let r : ℤ := (E : ℤ)-D
    have H1 := U.hasSum_smeared_inner_homogeneous ha hb hx hy hqa hha hea heb
      f.rapid_coefficients g.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)
    have H2 := U.hasSum_smeared_inner_homogeneous hb ha hx hy hqb hhb heb hea
      g.rapid_coefficients f.rapid_coefficients (SmoothCircleFunction.coefficient_real hg)
    let R : ℤ ≃ ℤ :=
      { toFun := fun m => r-m
        invFun := fun m => r-m
        left_inv := fun m => by dsimp; omega
        right_inv := fun m => by dsimp; omega }
    have H2' := R.hasSum_iff.mpr H2
    have Hdiff := H1.sub H2'
    have Hz := hzero r x y
    apply sub_eq_zero.mp
    apply Hdiff.unique
    convert Hz using 1
    ext m
    simp only [Function.comp_def,R,Equiv.coe_fn_mk]
    rw [show (E : ℤ)-D-(r-m) = m by dsimp [r]; omega]
    simp only [inner_sub_right]
    ring
  apply A.homogeneous_induction (P := fun x =>
      inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
  · simp only [map_zero,inner_zero_left]
  · intro D x hx
    apply A.homogeneous_induction (P := fun y =>
        inner ℂ (A.smearedMap a d hea f.coefficient f.rapid_coefficients x)
          (A.smearedMap b e heb g.coefficient g.rapid_coefficients y) =
        inner ℂ (A.smearedMap b e heb g.coefficient g.rapid_coefficients x)
          (A.smearedMap a d hea f.coefficient f.rapid_coefficients y))
    · simp only [map_zero,inner_zero_right]
    · intro E y hy
      exact Hhom D E x y hx hy
    · intro y z hy hz
      simp only [map_add,inner_add_right,hy,hz]
  · intro x z hx hz
    simp only [map_add,inner_add_left,hx,hz]
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
