import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.HighFieldGraph

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section
open scoped Topology
open Filter
open Filter MeasureTheory
open UniformSpace
open scoped ContDiff
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
lemma primary_stress_weakCommutation (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d) {f : SmoothCircleFunction}
    (hf : f.IsReal) (x y : V) :
    inner ℂ (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
      f.coefficient f.rapid_coefficients x)
      (A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.power (d-1)).coefficient (f.power (d-1)).rapid_coefficients y) =
    inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a)
        (f.power (d-1)).coefficient (f.power (d-1)).rapid_coefficients x)
      (A.smearedMap A.conformalVector 2 (U.polynomialEnergyBounds hc A.conformalVector)
        f.coefficient f.rapid_coefficients y) := by
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  exact U.smearedMap_weakCommutation_of_convolution A.conformal_mem ha
    A.conformal_quasiPrimary (hp 1 (by norm_num)) hν hh
    (U.polynomialEnergyBounds hc A.conformalVector) (U.polynomialEnergyBounds hc a)
    hf (SmoothCircleFunction.power_real hf (d-1))
    (fun r x y => A.hasSum_primary_stress_commutator_zero ha hp hd f r x y) x y
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open UniformSpace
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
local instance primaryStressWeakGradeFiniteDimensional :
    ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

lemma smoothSmear_weakCommutation_of_algebraic (hc : A.toVertexAlgebra.C2Cofinite) {a b : V} {d e : ℕ}
    (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    {f g : SmoothCircleFunction}
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients y))
    (x y : U.smoothEnergySpace) :
    inner ℂ (U.smoothSmear hc ha f.rapid_coefficients x : Completion V)
      (U.smoothSmear hc hb g.rapid_coefficients y : Completion V) =
    inner ℂ (U.smoothSmear hc hb g.rapid_coefficients x : Completion V)
      (U.smoothSmear hc ha f.rapid_coefficients y : Completion V) := by
  obtain ⟨C,hC,p,k,hM⟩ := (U.polynomialEnergyBounds hc a).physical A d
  obtain ⟨D,hD,q,l,hN⟩ := (U.polynomialEnergyBounds hc b).physical A e
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients
  let N := A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients
  have hm (v : V) : ‖M v‖ ≤ ((∑' n : ℤ, ‖f.coefficient n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ f.rapid_coefficients hM v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC.le))
  have hn (v : V) : ‖N v‖ ≤ ((∑' n : ℤ, ‖g.coefficient n‖*(1+|(n : ℝ)|)^q)*D)*‖(A.energyShift^(k+l)) v‖ :=
    (A.smearedMap_bound _ g.rapid_coefficients hN v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : l ≤ k+l) v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hD.le))
  let xx : (U.energyPower (k+l)).domain := ⟨x,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) x.property⟩
  let yy : (U.energyPower (k+l)).domain := ⟨y,(iInf_le (fun r => (U.energyPower r).domain) (k+l)) y.property⟩
  have hx : ((x : Completion V),U.energyPower (k+l) xx) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨xx,rfl,rfl⟩
  have hy : ((y : Completion V),U.energyPower (k+l) yy) ∈ (U.energyPower (k+l)).graph :=
    (U.energyPower (k+l)).mem_graph_iff.mpr ⟨yy,rfl,rfl⟩
  rw [U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm x hx,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn y hy,
    U.smoothSmear_eq_extension hc hb g.rapid_coefficients hn x hx,
    U.smoothSmear_eq_extension hc ha f.rapid_coefficients hm y hy]
  exact U.sobolevExtension_weakCommutation (k+l) M N hm hn
    hweak _ _

lemma highField_graph_invariant_firstOrderFlow_of_weak (hc : A.toVertexAlgebra.C2Cofinite)
    {a b : V} {d e p : ℕ} (ha : a ∈ A.grade d) (hb : b ∈ A.grade e)
    (hqa : A.IsQuasiPrimary a) (hqb : A.IsQuasiPrimary b)
    (hha : U.IsHermitian d a) (hhb : U.IsHermitian e b)
    {D : ℝ} (hD : 0 ≤ D)
    (hbnd : ∀ n v, ‖A.physicalMode b e n v‖ ≤ D*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f g : SmoothCircleFunction} (hf : f.IsReal) (hg : g.IsReal)
    (hweak : ∀ x y : V,
      inner ℂ (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients x)
        (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients y) =
      inner ℂ (A.smearedMap b e (U.polynomialEnergyBounds hc b) g.coefficient g.rapid_coefficients x)
        (A.smearedMap a d (U.polynomialEnergyBounds hc a) f.coefficient f.rapid_coefficients y)) (t : ℝ)
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
      (U.smoothSmear_weakCommutation_of_algebraic hc ha hb hweak)
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

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

theorem primary_power_stress_graph_entries_commute (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) (hp : A.IsPrimary a)
    (hh : U.IsHermitian d a) (hd : 1 ≤ d)
    {f : SmoothCircleFunction} (hf : f.IsReal) (i j k l : Bool) :
    ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
        (U.closedSmoothField_isClosed hc ha (f.power (d-1))) i j *
        ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 f)
          (U.closedSmoothField_isClosed hc A.conformal_mem f) k l =
      ClosedGraphData.entry (U.closedSmoothField hc A.conformalVector 2 f)
          (U.closedSmoothField_isClosed hc A.conformal_mem f) k l *
        ClosedGraphData.entry (U.closedSmoothField hc a d (f.power (d-1)))
          (U.closedSmoothField_isClosed hc ha (f.power (d-1))) i j := by
  have hn : 0 ≤ 1+A.centralCharge.re := by linarith [U.centralCharge_nonneg]
  have hν : U.IsHermitian 2 A.conformalVector := by simp [IsHermitian,U.pct_conformal]
  have hbnd (n : ℤ) (v : V) :
      ‖A.physicalMode A.conformalVector 2 n v‖ ≤
        (1+A.centralCharge.re)*(1+|(n : ℝ)|)^2*‖A.energyShift v‖ := by
    simpa only [physicalMode,virasoroMode,Nat.cast_ofNat,show n+(2 : ℤ)-1=n+1 by omega]
      using U.virasoro_linear_energy n v
  let hs := U.smearedCore_essentialSelfAdjoint A.conformal_mem A.conformal_quasiPrimary hν
    (U.polynomialEnergyBounds hc A.conformalVector) hbnd f.rapid_coefficients
    (SmoothCircleFunction.coefficient_real hf)
  exact SymmetricOperator.graph_entries_commute_of_flow_invariant _ _
    (U.closedSmoothField_isClosed hc ha (f.power (d-1))) hs
    (fun t x y hxy => U.highField_graph_invariant_firstOrderFlow_of_weak hc ha A.conformal_mem
      (hp 1 (by norm_num)) A.conformal_quasiPrimary hh hν hn hbnd
      (SmoothCircleFunction.power_real hf (d-1)) hf
      (fun v w => (U.primary_stress_weakCommutation hc ha hp hh hd hf v w).symm) t hxy)
    i j k l
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
 

lemma graph_invariant_of_regularizers (T : H →ₗ.[ℂ] H) (hT : T.IsClosed)
    (R B : ℕ → H →L[ℂ] H)
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hreg : ∀ n x y, (x,y) ∈ T.graph → B n x = R n y)
    (Q : H →L[ℂ] H)
    (hQR : ∀ n, Q * R n = R n * Q) (hQB : ∀ n, Q * B n = B n * Q)
    {x y : H} (hxy : (x,y) ∈ T.graph) : (Q x,Q y) ∈ T.graph := by
  have hgr (n : ℕ) : (Q (R n x),Q (R n y)) ∈ T.graph := by
    have hr := congrArg (fun S : H →L[ℂ] H => S x) (hQR n)
    have hb := congrArg (fun S : H →L[ℂ] H => S x) (hQB n)
    change Q (R n x) = R n (Q x) at hr
    change Q (B n x) = B n (Q x) at hb
    rw [hreg n x y hxy] at hb
    rw [hr,hb]
    exact hg n (Q x)
  exact hT.mem_of_tendsto
    ((Q.continuous.tendsto x |>.comp (hlim x)).prodMk_nhds
      (Q.continuous.tendsto y |>.comp (hlim y)))
    (Eventually.of_forall hgr)

 

lemma selfAdjoint_of_selfAdjoint_regularizers {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (R B : ℕ → H →L[ℂ] H)
    (hR : ∀ n, IsSelfAdjoint (R n)) (hB : ∀ n, IsSelfAdjoint (B n))
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x)) : IsSelfAdjoint T := by
  apply selfAdjoint_of_regularizers hd hT hs R B hR hg hlim
  intro x
  have he (n : ℕ) : (B n - (B n).adjoint) x = 0 := by
    rw [show (B n).adjoint = B n from hB n, sub_self,zero_apply]
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))

 

lemma graph_entries_commute_of_regularizers (T S : H →ₗ.[ℂ] H)
    (hT : T.IsClosed) (hS : S.IsClosed)
    (R B : ℕ → H →L[ℂ] H)
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hreg : ∀ n x y, (x,y) ∈ T.graph → B n x = R n y)
    (hR : ∀ n k l, ClosedGraphData.entry S hS k l * R n = R n * ClosedGraphData.entry S hS k l)
    (hB : ∀ n k l, ClosedGraphData.entry S hS k l * B n = B n * ClosedGraphData.entry S hS k l)
    (i j k l : Bool) :
    ClosedGraphData.entry T hT i j * ClosedGraphData.entry S hS k l =
      ClosedGraphData.entry S hS k l * ClosedGraphData.entry T hT i j := by
  symm
  apply ClosedGraphData.entry_commutes_of_graph_invariant T hT _
    (fun x y hxy => graph_invariant_of_regularizers T hT R B hg hlim hreg _
      (fun n => hR n k l) (fun n => hB n k l) hxy) ?_ i j
  change ∀ x y, (x,y) ∈ T.graph →
    (star (ClosedGraphData.entry S hS k l) x,star (ClosedGraphData.entry S hS k l) y) ∈ T.graph
  rw [ClosedGraphData.star_entry]
  intro x y hxy
  exact graph_invariant_of_regularizers T hT R B hg hlim hreg _
    (fun n => hR n l k) (fun n => hB n l k) hxy
end StronglyRationalVOA.SymmetricOperator

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

def timeIntegral (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ∫ t in a..b, flow T hs t x
      map_add' := fun x y => by
        simp only [map_add]
        exact intervalIntegral.integral_add ((flow_continuous T hs x).intervalIntegrable a b)
          ((flow_continuous T hs y).intervalIntegrable a b)
      map_smul' := fun c x => by
        simp only [map_smul]
        exact intervalIntegral.integral_smul c (fun t => flow T hs t x) }
    |b-a| (fun x => by
      change ‖∫ t in a..b, flow T hs t x‖ ≤ |b-a| * ‖x‖
      simpa only [mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
        (fun t _ => le_of_eq (flow_norm T hs t x)))

lemma timeIntegral_apply (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x : H) :
    timeIntegral T hs a b x = ∫ t in a..b, flow T hs t x := rfl

lemma timeIntegral_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) :
    ‖timeIntegral T hs a b‖ ≤ |b-a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _)
  intro x
  simpa only [timeIntegral_apply,mul_comm] using intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t _ => le_of_eq (flow_norm T hs t x))

lemma flow_matrix_derivative (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {u v : H} (huv : (u,v) ∈ T.graph) (x : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => inner ℂ u (flow T hs s x))
      (Complex.I*inner ℂ v (flow T hs t x)) t := by
  have h := HasDerivAt.inner ℂ
    ((flow_derivative T hs huv (-t)).scomp t (hasDerivAt_neg t)) (hasDerivAt_const t x)
  have he (s : ℝ) : inner ℂ (flow T hs (-s) u) x = inner ℂ u (flow T hs s x) := by
    rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
  have hid : inner ℂ ((-1 : ℝ) • flow T hs (-t) (Complex.I • v)) x =
      Complex.I*inner ℂ v (flow T hs t x) := by
    rw [neg_one_smul,map_smul,inner_neg_left,inner_smul_left]
    change -(star Complex.I * inner ℂ (flow T hs (-t) v) x) = _
    rw [Complex.star_def,Complex.conj_I,neg_mul,neg_neg]
    rw [← ContinuousLinearMap.adjoint_inner_left,flow_adjoint]
  simpa only [Function.comp_apply,he,inner_zero_right,zero_add,hid] using h

 

lemma timeIntegral_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x : H) :
    (timeIntegral T hs a b x,(-Complex.I) • (flow T hs b x-flow T hs a x)) ∈ T.graph := by
  rw [show T.graph = T.adjoint.graph from congrArg LinearPMap.graph hs.symm,
    LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro u v huv
  have hc : Continuous (fun t => Complex.I*inner ℂ v (flow T hs t x)) :=
    continuous_const.mul (continuous_const.inner (flow_continuous T hs x))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => flow_matrix_derivative T hs huv x t) (hc.intervalIntegrable a b)
  have hi := (innerSL ℂ v).intervalIntegral_comp_comm (μ := volume) ((flow_continuous T hs x).intervalIntegrable a b)
  change (∫ t in a..b, inner ℂ v (flow T hs t x)) = inner ℂ v (timeIntegral T hs a b x) at hi
  rw [intervalIntegral.integral_const_mul,hi] at h
  simp only [inner_smul_right,inner_sub_right]
  linear_combination (norm := (ring_nf; simp [Complex.I_sq])) (-Complex.I) * h

lemma timeIntegral_commutes_flow (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b t : ℝ) :
    timeIntegral T hs a b * flow T hs t = flow T hs t * timeIntegral T hs a b := by
  ext x
  change (∫ s in a..b, flow T hs s (flow T hs t x)) =
    flow T hs t (∫ s in a..b, flow T hs s x)
  rw [← (flow T hs t).intervalIntegral_comp_comm ((flow_continuous T hs x).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro s _
  change (flow T hs s * flow T hs t) x = (flow T hs t * flow T hs s) x
  rw [← flow_add,← flow_add,add_comm s t]

lemma inner_timeIntegral_right (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x y : H) :
    inner ℂ x (timeIntegral T hs a b y) = ∫ t in a..b, inner ℂ x (flow T hs t y) := by
  exact ((innerSL ℂ x).intervalIntegral_comp_comm (μ := volume)
    ((flow_continuous T hs y).intervalIntegrable a b)).symm

lemma inner_timeIntegral_left (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) (x y : H) :
    inner ℂ (timeIntegral T hs a b x) y = ∫ t in a..b, inner ℂ (flow T hs t x) y := by
  let L : H →L[ℝ] ℂ := Complex.conjCLE.toContinuousLinearMap.comp ((innerSL ℂ y).restrictScalars ℝ)
  have h := L.intervalIntegral_comp_comm (μ := volume) ((flow_continuous T hs x).intervalIntegrable a b)
  change (∫ t in a..b, (starRingEnd ℂ) (inner ℂ y (flow T hs t x))) =
    (starRingEnd ℂ) (inner ℂ y (∫ t in a..b, flow T hs t x)) at h
  simpa only [inner_conj_symm,timeIntegral_apply] using h.symm

lemma timeIntegral_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (a b : ℝ) :
    (timeIntegral T hs a b).adjoint = timeIntegral T hs (-b) (-a) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_timeIntegral_left,inner_timeIntegral_right]
  simp_rw [← ContinuousLinearMap.adjoint_inner_right,flow_adjoint]
  simpa only [neg_neg] using intervalIntegral.integral_comp_neg
    (fun t => inner ℂ x (flow T hs t y)) (a := -b) (b := -a)

 

def timeAverage (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) : H →L[ℂ] H :=
  ((2*r)⁻¹ : ℝ) • timeIntegral T hs (-r) r

lemma timeAverage_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) :
    IsSelfAdjoint (timeAverage T hs r) := by
  change star (timeAverage T hs r) = timeAverage T hs r
  rw [timeAverage,star_smul,star_trivial]
  change (2*r)⁻¹ • (timeIntegral T hs (-r) r).adjoint = _
  rw [timeIntegral_adjoint,neg_neg]

lemma timeAverage_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {r : ℝ} (hr : 0 < r) :
    ‖timeAverage T hs r‖ ≤ 1 := by
  rw [timeAverage,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hr))]
  calc
    (2*r)⁻¹ * ‖timeIntegral T hs (-r) r‖ ≤ (2*r)⁻¹ * |r-(-r)| :=
      mul_le_mul_of_nonneg_left (timeIntegral_norm T hs (-r) r) (by positivity)
    _ = 1 := by
      rw [show r-(-r)=2*r by ring,abs_of_pos (mul_pos (by norm_num) hr)]
      exact inv_mul_cancel₀ (by positivity)

lemma timeAverage_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) (x : H) :
    (timeAverage T hs r x,((2*r)⁻¹ : ℝ) • ((-Complex.I) • (flow T hs r x-flow T hs (-r) x))) ∈ T.graph := by
  have h := (T.graph.restrictScalars ℝ).smul_mem ((2*r)⁻¹ : ℝ) (timeIntegral_graph T hs (-r) r x)
  simpa only [Submodule.restrictScalars_mem,timeAverage,smul_apply,Prod.smul_mk] using h

lemma timeAverage_initial_bound (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    {x y : H} (hxy : (x,y) ∈ T.graph) {r : ℝ} (hr : 0 < r) :
    ‖timeAverage T hs r x-x‖ ≤ r*‖y‖ := by
  have he : timeAverage T hs r x-x =
      (2*r)⁻¹ • (∫ t in -r..r, (flow T hs t x-x)) := by
    rw [intervalIntegral.integral_sub ((flow_continuous T hs x).intervalIntegrable (-r) r)
      (continuous_const.intervalIntegrable (-r) r),intervalIntegral.integral_const,
      show r-(-r)=2*r by ring,smul_sub,inv_smul_smul₀ (show 2*r ≠ 0 by positivity)]
    rfl
  have hb : ‖∫ t in -r..r, (flow T hs t x-x)‖ ≤ (r*‖y‖)*(2*r) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -r) (b := r)
      (C := r*‖y‖) (f := fun t => flow T hs t x-x) (fun t ht => ?_)
    · simpa only [show r-(-r)=2*r by ring,abs_of_pos (show 0 < 2*r by positivity)] using h
    · rw [Set.uIoc_of_le (by linarith : -r ≤ r)] at ht
      exact (flow_initial_bound T hs hxy t).trans
        (mul_le_mul_of_nonneg_right (abs_le.mpr ⟨ht.1.le,ht.2⟩) (norm_nonneg y))
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) hr))]
  have h := mul_le_mul_of_nonneg_left hb (show 0 ≤ (2*r)⁻¹ by positivity)
  calc
    (2*r)⁻¹ * ‖∫ t in -r..r, (flow T hs t x-x)‖ ≤ (2*r)⁻¹*((r*‖y‖)*(2*r)) := h
    _ = r*‖y‖ := by field_simp

 

lemma timeAverage_strong_one (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (x : H) :
    Tendsto (fun n => timeAverage T hs (r n) x) atTop (𝓝 x) := by
  have hc := (StrongLimit.equicontinuous_of_norm_bound
    (fun n => timeAverage T hs (r n)) (fun n => timeAverage_norm T hs (hr n))).isClosed_setOfPred_tendsto
    (l := atTop) (f := id) continuous_id
  apply (closure_minimal (s := (T.domain : Set H)) (t := {x | Tendsto
    (fun n => timeAverage T hs (r n) x) atTop (𝓝 x)}) ?_ hc) (hs.dense_domain x)
  intro v hv
  let w : T.domain := ⟨v,hv⟩
  change Tendsto _ _ _
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (a := fun n => r n*‖T w‖)
  · exact fun n => timeAverage_initial_bound T hs (T.mem_graph_iff.mpr ⟨w,rfl,rfl⟩) (hr n)
  · simpa only [zero_mul] using hl.mul_const ‖T w‖

end StronglyRationalVOA.SymmetricOperator

open MeasureTheory
open scoped Topology
namespace StronglyRationalVOA

lemma intervalIntegral_mem_closedSubmodule {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] (S : Submodule ℂ E) (hS : IsClosed (S : Set E))
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hm : ∀ t, f t ∈ S) : (∫ t in a..b,f t) ∈ S := by
  let : IsClosed (S : Set E) := hS
  have h := S.mkQL.intervalIntegral_comp_comm hf
  have hz (t : ℝ) : S.mkQL (f t) = 0 := (Submodule.Quotient.mk_eq_zero S).mpr (hm t)
  simp only [hz,intervalIntegral.integral_zero] at h
  exact (Submodule.Quotient.mk_eq_zero S).mp h.symm

namespace SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeIntegral_preserves_graph (T A : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hA : A.IsClosed)
    (hi : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (a b : ℝ) {x y : H} (hxy : (x,y) ∈ A.graph) :
    (timeIntegral T hs a b x,timeIntegral T hs a b y) ∈ A.graph := by
  have hf : IntervalIntegrable (fun t => (flow T hs t x,flow T hs t y)) volume a b :=
    ((flow_continuous T hs x).prodMk (flow_continuous T hs y)).intervalIntegrable a b
  have h := intervalIntegral_mem_closedSubmodule A.graph hA hf (fun t => hi t x y hxy)
  have he : (∫ t in a..b,(flow T hs t x,flow T hs t y)) =
      (timeIntegral T hs a b x,timeIntegral T hs a b y) := by
    apply Prod.ext
    · exact ((ContinuousLinearMap.fst ℂ H H).intervalIntegral_comp_comm hf).symm
    · exact ((ContinuousLinearMap.snd ℂ H H).intervalIntegral_comp_comm hf).symm
  rwa [he] at h

lemma timeAverage_preserves_graph (T A : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (hA : A.IsClosed)
    (hi : ∀ t x y, (x,y) ∈ A.graph → (flow T hs t x,flow T hs t y) ∈ A.graph)
    (r : ℝ) {x y : H} (hxy : (x,y) ∈ A.graph) :
    (timeAverage T hs r x,timeAverage T hs r y) ∈ A.graph := by
  have h := (A.graph.restrictScalars ℝ).smul_mem ((2*r)⁻¹ : ℝ)
    (timeIntegral_preserves_graph T A hs hA hi (-r) r hxy)
  simpa only [Submodule.restrictScalars_mem,timeAverage,smul_apply,Prod.smul_mk] using h
end SymmetricOperator
end StronglyRationalVOA

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeIntegral_commutes (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q) (a b : ℝ) :
    Q*timeIntegral T hs a b = timeIntegral T hs a b*Q := by
  ext x
  change Q (∫ t in a..b,flow T hs t x) = ∫ t in a..b,flow T hs t (Q x)
  rw [← Q.intervalIntegral_comp_comm ((flow_continuous T hs x).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg (fun R : H →L[ℂ] H => R x) (hQ t)

lemma timeAverage_commutes (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (Q : H →L[ℂ] H) (hQ : ∀ t, Q*flow T hs t = flow T hs t*Q) (r : ℝ) :
    Q*timeAverage T hs r = timeAverage T hs r*Q := by
  rw [timeAverage,mul_smul_comm,smul_mul_assoc,timeIntegral_commutes T hs Q hQ]

lemma flow_timeAverage_commutes (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (s r : ℝ) :
    flow T hs s*timeAverage T hs r = timeAverage T hs r*flow T hs s := by
  apply timeAverage_commutes
  intro t
  rw [← flow_add,← flow_add,add_comm s t]

 
def timeDifference (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) : H →L[ℂ] H :=
  ((2*r)⁻¹ : ℝ) • ((-Complex.I) • (flow T hs r-flow T hs (-r)))

lemma timeAverage_graph' (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) (x : H) :
    (timeAverage T hs r x,timeDifference T hs r x) ∈ T.graph := by
  exact timeAverage_graph T hs r x
end StronglyRationalVOA.SymmetricOperator

end

end OAI
