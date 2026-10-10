import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.PrimaryStressWeak

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
lemma timeAverage_graph_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) {x y : H} (hxy : (x,y) ∈ T.graph) :
    timeDifference T hs r x = timeAverage T hs r y := by
  have h := graph_invariant_of_commutes_flow T hs (timeAverage T hs r)
    (fun t => (flow_timeAverage_commutes T hs t r).symm) hxy
  exact T.mem_graph_snd_inj (timeAverage_graph' T hs r x) h rfl

lemma timeAverage_timeDifference_commute (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) :
    timeAverage T hs r*timeDifference T hs r = timeDifference T hs r*timeAverage T hs r := by
  simp only [timeDifference,mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul]
  rw [← flow_timeAverage_commutes T hs r r,← flow_timeAverage_commutes T hs (-r) r]

lemma timeDifference_norm (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) {r : ℝ} (hr : 0 < r) :
    ‖timeDifference T hs r‖ ≤ r⁻¹ := by
  rw [timeDifference,norm_smul,norm_smul,norm_neg,Complex.norm_I,one_mul,
    Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity : 0 < 2*r))]
  calc
    (2*r)⁻¹*‖flow T hs r-flow T hs (-r)‖ ≤ (2*r)⁻¹*(1+1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (norm_sub_le _ _).trans (add_le_add (flow_opNorm T hs r) (flow_opNorm T hs (-r)))
    _ = r⁻¹ := by field_simp; ring

 

def iteratedGraph (T : H →ₗ.[ℂ] H) : ℕ → H → H → Prop
  | 0,x,y => x=y
  | k+1,x,y => ∃ z, (x,z) ∈ T.graph ∧ iteratedGraph T k z y

omit [CompleteSpace H] in
lemma iteratedGraph_regularizer (T : H →ₗ.[ℂ] H)
    (R B : H →L[ℂ] H) (hg : ∀ x, (R x,B x) ∈ T.graph)
    (hc : R*B = B*R) (k : ℕ) (x : H) :
    iteratedGraph T k ((R^k) x) ((B^k) x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    refine ⟨B ((R^k) x),?_,?_⟩
    · simpa only [pow_succ',mul_apply_eq_comp] using hg ((R^k) x)
    · have he : B*R^k = R^k*B := (Commute.symm hc).pow_right k
      have hep := congrArg (fun Q : H →L[ℂ] H => Q x) he
      change B ((R^k) x) = (R^k) (B x) at hep
      rw [hep,pow_succ,mul_apply_eq_comp]
      exact ih (B x)

lemma timeAverage_iterated_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℝ) (k : ℕ) (x : H) :
    iteratedGraph T k (((timeAverage T hs r)^k) x) (((timeDifference T hs r)^k) x) :=
  iteratedGraph_regularizer T _ _ (timeAverage_graph' T hs r)
    (timeAverage_timeDifference_commute T hs r) k x

lemma timeIntegral_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (B : ℝ → H →L[ℂ] H) (hB : ∀ t, (flow T hs t).comp S = S.comp (B t))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ t, ‖B t‖ ≤ Real.exp (K*|t|))
    (a b : ℝ) (x : H) :
    timeIntegral T hs a b (S x) = S (∫ t in a..b,B t x) := by
  rw [← S.intervalIntegral_comp_comm
    ((regularizer_factor_continuous T hs S hS hSd B hB hK hb x).intervalIntegrable a b)]
  apply intervalIntegral.integral_congr
  intro t _
  exact congrArg (fun Q : H →L[ℂ] H => Q x) (hB t)

lemma timeDifference_selfAdjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (r : ℝ) :
    IsSelfAdjoint (timeDifference T hs r) := by
  change star (timeDifference T hs r) = timeDifference T hs r
  rw [timeDifference,star_smul,star_trivial,star_smul,star_sub]
  change (2*r)⁻¹ • ((star (-Complex.I)) • ((flow T hs r).adjoint-(flow T hs (-r)).adjoint)) = _
  rw [star_neg,Complex.star_def,Complex.conj_I,neg_neg,flow_adjoint,flow_adjoint,neg_neg]
  congr 1
  rw [show flow T hs (-r)-flow T hs r = -(flow T hs r-flow T hs (-r)) by abel,
    smul_neg,neg_smul]

omit [CompleteSpace H] in
lemma contraction_pow_initial_bound (R : H →L[ℂ] H) (hR : ‖R‖ ≤ 1) (k : ℕ) (x : H) :
    ‖(R^k) x-x‖ ≤ k*‖R x-x‖ := by
  induction k with
  | zero => simp only [pow_zero,one_apply_eq_self,sub_self,norm_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ k ih =>
    have he : (R^(k+1)) x-x = R ((R^k) x-x)+(R x-x) := by
      rw [pow_succ',mul_apply_eq_comp,map_sub]; abel
    rw [he]
    calc
      ‖R ((R^k) x-x)+(R x-x)‖ ≤ ‖R ((R^k) x-x)‖+‖R x-x‖ := norm_add_le _ _
      _ ≤ ‖(R^k) x-x‖+‖R x-x‖ := by
        exact add_le_add (by simpa only [one_mul] using R.le_of_opNorm_le hR ((R^k) x-x)) le_rfl
      _ ≤ (k:ℝ)*‖R x-x‖+‖R x-x‖ := add_le_add ih le_rfl
      _ = (k+1:ℕ)*‖R x-x‖ := by push_cast; ring

lemma timeAverage_pow_strong_one (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hl : Tendsto r atTop (𝓝 0)) (k : ℕ) (x : H) :
    Tendsto (fun n => ((timeAverage T hs (r n))^k) x) atTop (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    contraction_pow_initial_bound _ (timeAverage_norm T hs (hr n)) k x)
  simpa only [mul_zero] using
    (tendsto_iff_norm_sub_tendsto_zero.mp (timeAverage_strong_one T hs r hr hl x)).const_mul (k:ℝ)

end StronglyRationalVOA.SymmetricOperator

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma bounded_regularization (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (T : H →ₗ.[ℂ] H) (hT : T.IsClosed) (P r : Module.End ℂ D) (R : H →L[ℂ] H)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ T.graph)
    (hr : ∀ x : D, (r x:H) = R x)
    {C : ℝ} (hb : ∀ x : D, ‖(P (r x):H)‖ ≤ C*‖(x:H)‖) :
    ∃ B : H →L[ℂ] H, (∀ x : D, B x = (P (r x):H)) ∧
      ∀ x : H, (R x,B x) ∈ T.graph := by
  let M : D →ₗ[ℂ] H := D.subtype.comp (P.comp r)
  let K := M.mkContinuous C hb
  let B := K.extend D.subtypeL
  have hd : DenseRange D.subtypeL := by
    change Dense (Set.range (D.subtypeL : D → H))
    have he : Set.range (D.subtypeL : D → H) = (D : Set H) := by
      ext x; exact ⟨by rintro ⟨y,rfl⟩; exact y.property,fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
    rwa [he]
  have he : IsUniformInducing D.subtypeL := D.subtypeₗᵢ.isometry.isUniformInducing
  have hc (x : D) : B x = (P (r x):H) := ContinuousLinearMap.extend_eq K hd he x
  refine ⟨B,hc,?_⟩
  have hclosed : IsClosed {x : H | (R x,B x) ∈ T.graph} := hT.preimage (R.continuous.prodMk B.continuous)
  intro x
  apply (closure_minimal (s := (D : Set H)) (t := {x:H | (R x,B x) ∈ T.graph}) ?_ hclosed) (hD x)
  intro y hy
  have h := hP (r ⟨y,hy⟩)
  rw [hr,← hc] at h
  exact h

lemma bounded_symmetric_of_core (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (B : H →L[ℂ] H)
    (hB : ∀ x y : D, inner ℂ (B x) (y:H) = inner ℂ (x:H) (B y)) :
    IsSelfAdjoint B := by
  have he (x : D) (y : H) : inner ℂ (B x) y = inner ℂ (x:H) (B y) := by
    have hc : IsClosed {y : H | inner ℂ (B x) y = inner ℂ (x:H) (B y)} :=
      isClosed_eq (continuous_const.inner continuous_id) (continuous_const.inner B.continuous)
    exact (closure_minimal (fun y hy => hB x ⟨y,hy⟩) hc) (hD y)
  have he' (x y : H) : inner ℂ (B x) y = inner ℂ x (B y) := by
    have hc : IsClosed {x : H | inner ℂ (B x) y = inner ℂ x (B y)} :=
      isClosed_eq (B.continuous.inner continuous_const) (continuous_id.inner continuous_const)
    exact (closure_minimal (fun x hx => he ⟨x,hx⟩ y) hc) (hD x)
  exact ((ContinuousLinearMap.eq_adjoint_iff B B).mpr he').symm

lemma regularization_selfAdjoint (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P r : Module.End ℂ D) (R B : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hr : ∀ x : D, (r x:H) = R x)
    (hB : ∀ x : D, B x = (P (r x):H))
    (hP : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hPr : P*r = r*P) : IsSelfAdjoint B := by
  apply bounded_symmetric_of_core D hD B
  intro x y
  rw [hB,hB,hP,hr,← ContinuousLinearMap.adjoint_inner_right,show R.adjoint = R from hR]
  have hp := congrArg (fun F : Module.End ℂ D => (F y:H)) hPr
  change (P (r y):H) = (r (P y):H) at hp
  rw [hp,hr]

omit [CompleteSpace H] in
 

lemma regularization_preserves_closure (D : Submodule ℂ H)
    (P Q r : Module.End ℂ D) (B : H →L[ℂ] H)
    (hB : ∀ x : D, B x = (P (r x):H))
    (hPQ : P*Q = Q*P) (hrQ : r*Q = Q*r)
    (M : H →ₗ.[ℂ] H) (hc : M.IsClosable)
    (hM : M.graph = (D.subtype.prod (D.subtype.comp Q)).range)
    {x y : H} (hxy : (x,y) ∈ M.closure.graph) : (B x,B y) ∈ M.closure.graph := by
  apply graph_invariant_of_core M hc B ?_ hxy
  intro u v huv
  rw [hM] at huv
  obtain ⟨z,hz⟩ := huv
  change ((z:H),(Q z:H)) = (u,v) at hz
  cases hz
  rw [hB,hB]
  have he : P (r (Q z)) = Q (P (r z)) := by
    have hrq := congrArg (fun F : Module.End ℂ D => F z) hrQ
    have hpq := congrArg (fun F : Module.End ℂ D => F (r z)) hPQ
    change r (Q z) = Q (r z) at hrq
    change P (Q (r z)) = Q (P (r z)) at hpq
    rw [hrq,hpq]
  rw [he]
  apply LinearPMap.le_graph_of_le (LinearPMap.le_closure M)
  rw [hM]
  exact ⟨P (r z),rfl⟩
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

def onSubmodule (D : Submodule ℂ H) (P : Module.End ℂ D) : H →ₗ.[ℂ] H where
  domain := D
  toFun := D.subtype.comp P

lemma onSubmodule_graph (D : Submodule ℂ H) (P : Module.End ℂ D) :
    (onSubmodule D P).graph = (D.subtype.prod (D.subtype.comp P)).range := by
  ext p
  rw [LinearPMap.mem_graph_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨x,Prod.ext hx hy⟩
  · rintro ⟨x,hx⟩
    exact ⟨x,congrArg Prod.fst hx,congrArg Prod.snd hx⟩

lemma onSubmodule_mem_graph (D : Submodule ℂ H) (P : Module.End ℂ D) (x : D) :
    ((x:H),(P x:H)) ∈ (onSubmodule D P).graph :=
  (LinearPMap.mem_graph_iff _).mpr ⟨x,rfl,rfl⟩

lemma closure_eq_of_intermediate (M N : H →ₗ.[ℂ] H) (hM : M.IsClosable)
    (hMN : M ≤ N) (hNM : N ≤ M.closure) : N.closure = M.closure := by
  have hN := hM.closure_isClosed.isClosable.leIsClosable hNM
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro p hp
    rw [← hN.graph_closure_eq_closure_graph] at hp
    exact (closure_minimal (LinearPMap.le_graph_of_le hNM) hM.closure_isClosed) hp
  · exact hN.closure_mono hMN
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma smoothSmear_core (hc : A.toVertexAlgebra.C2Cofinite) {a : V} {d : ℕ}
    (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    (SymmetricOperator.onSubmodule U.smoothEnergySpace (U.smoothSmear hc ha hf)).closure =
      U.closedSmearedOperator hc a d f hf := by
  apply SymmetricOperator.closure_eq_of_intermediate _ _ (U.smearedCore_closable hc ha hf)
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨x,hx,hMx⟩ := (HilbertCore.operator
      (A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf)).mem_graph_iff.mp hp
    obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective x
    let z : U.smoothEnergySpace := ⟨(v:Completion V),U.core_le_smoothEnergySpace
      (HilbertCore.equiv V v).property⟩
    have h := SymmetricOperator.onSubmodule_mem_graph U.smoothEnergySpace (U.smoothSmear hc ha hf) z
    have he : (U.smoothSmear hc ha hf z:Completion V) =
        A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v := U.smoothSmear_coe hc ha hf v
    rw [he] at h
    have hxe : (v:Completion V) = p.1 := hx
    have hye : A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf v = p.2 := by
      simpa only [HilbertCore.operator_apply] using hMx
    simpa only [z,hxe,hye,Prod.mk.eta] using h
  · apply LinearPMap.le_of_le_graph
    intro p hp
    obtain ⟨x,hx,hy⟩ := (LinearPMap.mem_graph_iff _).mp hp
    have he : ((x:Completion V),(U.smoothSmear hc ha hf x:Completion V)) = p := Prod.ext hx hy
    rw [← he]
    exact U.smoothSmear_graph hc ha hf x
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

open Filter MeasureTheory
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma timeAverage_inverse_factor (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSd : DenseRange S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F)
    (r : ℝ) (x : H) : ∃ z, timeAverage T hs r (S x) = S z := by
  choose B hB hb using fun t => flow_regularizer_factor T hs S E F hS hSd hg hdef t
  refine ⟨((2*r)⁻¹ : ℝ) • (∫ t in -r..r,B t x),?_⟩
  rw [show S (((2*r)⁻¹ : ℝ) • (∫ t in -r..r,B t x)) =
      ((2*r)⁻¹ : ℝ) • S (∫ t in -r..r,B t x) from
        (S.restrictScalars ℝ).map_smul _ _,
    timeAverage,smul_apply,timeIntegral_factor T hs S hS hSd B hB (norm_nonneg F) hb]
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

lemma core_timeAverage_energyGraph (r : ℕ) (M K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^r) v‖)
    (hK : ∀ v, ‖K v‖ ≤ D*‖(A.energyShift^r) v‖)
    (hk : ∀ x y : V, inner ℂ (M x) ((A.energyShift^r) y : Completion V)-
      inner ℂ ((A.energyShift^r) x : Completion V) (M y) = inner ℂ (K x) (y : Completion V))
    (hc : (HilbertCore.operator M).IsClosable) (hs : IsSelfAdjoint (HilbertCore.operator M).closure)
    (t : ℝ) {x y : Completion V} (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.timeAverage (HilbertCore.operator M).closure hs t x,z) ∈ (U.energyPower r).graph := by
  obtain ⟨z,hz⟩ := SymmetricOperator.timeAverage_inverse_factor _ hs
    (U.inverseSobolev r) (U.sobolevExtension r M) (U.sobolevExtension r K)
    (U.inverseSobolev_selfAdjoint r) (U.inverseSobolev_dense r)
    (U.sobolevExtension_inverse_graph r M hM hc) (U.sobolevExtension_defect r M K hM hK hk) t y
  rw [U.inverseSobolev_on_graph r hxy] at hz
  refine ⟨z,?_⟩
  rw [hz]
  exact U.inverseSobolev_graph r z

lemma firstOrderSmear_timeAverage_energyGraph {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    {r : ℕ} (hrp : 1 ≤ r) (t : ℝ) {x y : Completion V}
    (hxy : (x,y) ∈ (U.energyPower r).graph) :
    ∃ z, (SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x,z) ∈ (U.energyPower r).graph := by
  have hM (v : V) : ‖A.smearedMap a d he f hf v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C)*‖(A.energyShift^r) v‖ := by
    have hb' : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^1) v‖ := by
      simpa only [pow_one] using hb
    exact (A.smearedMap_bound he hf hb' v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono hrp v)
        (mul_nonneg (tsum_nonneg fun n => by positivity) hC))
  exact U.core_timeAverage_energyGraph r (A.smearedMap a d he f hf)
    (U.smearedPowerCommutator ha he hf r) hM
    (U.smearedPowerCommutator_bound ha he hC hb hf r)
    (U.smearedPowerCommutator_pairing ha hq hh he hf hr r)
    (HilbertCore.closable (U.smearedMap_symmetric ha hq hh he hf hr))
    (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t hxy

lemma firstOrderSmear_timeAverage_smoothEnergySpace {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n))
    (t : ℝ) {x : Completion V} (hx : x ∈ U.smoothEnergySpace) :
    SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
      (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf] at hx ⊢
  intro r
  by_cases hr0 : r = 0
  · subst r
    obtain ⟨v,hv,_⟩ := (U.energyPower 0).mem_graph_iff.mp (U.energyPower_zero_graph
      (SymmetricOperator.timeAverage (HilbertCore.operator (A.smearedMap a d he f hf)).closure
        (U.smearedCore_essentialSelfAdjoint ha hq hh he hb hf hr) t x))
    dsimp only [Prod.fst] at hv
    rw [← hv]
    exact v.property
  · let v : (U.energyPower r).domain := ⟨x,hx r⟩
    obtain ⟨z,hz⟩ := U.firstOrderSmear_timeAverage_energyGraph ha hq hh he hC hb hf hr
      (show 1 ≤ r by omega) t ((U.energyPower r).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
    obtain ⟨w,hw,_⟩ := (U.energyPower r).mem_graph_iff.mp hz
    dsimp only [Prod.fst] at hw
    rw [← hw]
    exact w.property
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SymmetricOperator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma end_pow_bound (P : Module.End ℂ E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x, ‖P x‖ ≤ C*‖x‖) (k : ℕ) (x : E) :
    ‖(P^k) x‖ ≤ C^k*‖x‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      ‖(P^(k+1)) x‖ = ‖P ((P^k) x)‖ := by rw [pow_succ']; rfl
      _ ≤ C*‖(P^k) x‖ := hb _
      _ ≤ C*(C^k*‖x‖) := mul_le_mul_of_nonneg_left ih hC
      _ = C^(k+1)*‖x‖ := by rw [pow_succ']; ring

 

lemma commuting_core_power_bound (T r : Module.End ℂ E) (hc : T*r = r*T)
    {b : ℝ} (hb : 0 ≤ b) (hr : ∀ x, ‖r x‖ ≤ ‖x‖)
    (hTr : ∀ x, ‖T (r x)‖ ≤ b*‖x‖) {j k : ℕ} (hjk : j ≤ k) (x : E) :
    ‖(T^j) ((r^k) x)‖ ≤ b^j*‖x‖ := by
  have he : T^j*r^k = (T*r)^j*r^(k-j) := by
    rw [Commute.mul_pow hc, mul_assoc,← pow_add,Nat.add_sub_of_le hjk]
  have hex := congrArg (fun P : Module.End ℂ E => P x) he
  change (T^j) ((r^k) x) = ((T*r)^j) ((r^(k-j)) x) at hex
  rw [hex]
  calc
    ‖((T*r)^j) ((r^(k-j)) x)‖ ≤ b^j*‖(r^(k-j)) x‖ :=
      end_pow_bound (T*r) hb hTr j _
    _ ≤ b^j*‖x‖ := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hb j)
      simpa only [one_pow,one_mul] using
        end_pow_bound r (by norm_num : (0:ℝ) ≤ 1) (by simpa only [one_mul] using hr) (k-j) x
end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 
def restricted (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) : Module.End ℂ D :=
  (R.toLinearMap.comp D.subtype).codRestrict D hR

@[simp] lemma restricted_coe (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) (x : D) : (restricted D R hR x:H) = R x := rfl

lemma restricted_pow_coe (D : Submodule ℂ H) (R : H →L[ℂ] H)
    (hR : ∀ x : D, R x ∈ D) (k : ℕ) (x : D) :
    (((restricted D R hR)^k) x:H) = (R^k) x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ',pow_succ']
    change R (((restricted D R hR)^k) x:H) = R ((R^k) x)
    rw [ih]

lemma restricted_commutes_of_graph (D : Submodule ℂ H) (P : Module.End ℂ D)
    (R : H →L[ℂ] H) (hR : ∀ x : D, R x ∈ D) (M : H →ₗ.[ℂ] H)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hRM : ∀ x y, (x,y) ∈ M.graph → (R x,R y) ∈ M.graph) :
    P*restricted D R hR = restricted D R hR*P := by
  ext x
  change (P (restricted D R hR x):H) = R (P x)
  exact M.mem_graph_snd_inj (hP (restricted D R hR x)) (hRM _ _ (hP x)) rfl

end StronglyRationalVOA.SymmetricOperator

open Filter
open scoped Topology
namespace StronglyRationalVOA.SymmetricOperator
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

lemma local_energy_regularization (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P τ : Module.End ℂ D) (M T : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hs : IsSelfAdjoint T)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hPs : ∀ x y : D, inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H))
    (hflow : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (r : ℝ) (hr : 0 < r)
    (hinv : ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖) :
    ∃ B : H →L[ℂ] H, IsSelfAdjoint B ∧
      (∀ x : D, B x = (P (((restricted D (timeAverage T hs r) hinv)^k) x):H)) ∧
      ∀ x : H, (((timeAverage T hs r)^k) x,B x) ∈ M.graph := by
  let R := timeAverage T hs r
  let q := restricted D R hinv
  have hRq : ∀ x : D, (q x:H) = R x := fun _ => rfl
  have hqτ : τ*q = q*τ := restricted_commutes_of_graph D τ R hinv T hτ
    (fun _ _ hxy => timeAverage_preserves_graph T T hs hs.isClosed (fun t _ _ h => flow_graph T hs t h) r hxy)
  have hqP : P*q = q*P := restricted_commutes_of_graph D P R hinv M hP
    (fun _ _ hxy => timeAverage_preserves_graph T M hs hM hflow r hxy)
  have hqnorm (x : D) : ‖q x‖ ≤ ‖x‖ := by
    change ‖R x‖ ≤ ‖(x:H)‖
    simpa only [one_mul] using R.le_of_opNorm_le (timeAverage_norm T hs hr) (x:H)
  have htq (x : D) : ‖τ (q x)‖ ≤ r⁻¹*‖x‖ := by
    have he : (τ (q x):H) = timeDifference T hs r x :=
      T.mem_graph_snd_inj (hτ (q x)) (timeAverage_graph' T hs r x) rfl
    change ‖(τ (q x):H)‖ ≤ r⁻¹*‖(x:H)‖
    rw [he]
    exact (timeDifference T hs r).le_of_opNorm_le (timeDifference_norm T hs hr) (x:H)
  have hb' (x : D) : ‖(P ((q^k) x):H)‖ ≤
      (C*(∑ j ∈ Finset.range (k+1), (r⁻¹)^j))*‖(x:H)‖ := by
    calc
      ‖(P ((q^k) x):H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) ((q^k) x):H)‖ := hb _
      _ ≤ C*∑ j ∈ Finset.range (k+1), (r⁻¹)^j*‖(x:H)‖ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply Finset.sum_le_sum
        intro j hj
        exact commuting_core_power_bound τ q hqτ (inv_nonneg.mpr hr.le) hqnorm htq
          (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hj) x
      _ = (C*(∑ j ∈ Finset.range (k+1), (r⁻¹)^j))*‖(x:H)‖ := by
        rw [← Finset.sum_mul,mul_assoc]
  have hqpow (x : D) : ((q^k) x:H) = (R^k) x := restricted_pow_coe D R hinv k x
  obtain ⟨B,hB,hg⟩ := bounded_regularization D hD M hM P (q^k) (R^k) hP hqpow hb'
  refine ⟨B,?_,hB,hg⟩
  apply regularization_selfAdjoint D hD P (q^k) (R^k) B (IsSelfAdjoint.pow (timeAverage_selfAdjoint T hs r) k)
    hqpow hB hPs
  exact Commute.pow_right hqP k

 

lemma selfAdjoint_of_local_energy (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (P τ : Module.End ℂ D) (M T : H →ₗ.[ℂ] H) (hM : M.IsClosed)
    (hMs : M.IsFormalAdjoint M) (hs : IsSelfAdjoint T)
    (hP : ∀ x : D, ((x:H),(P x:H)) ∈ M.graph)
    (hτ : ∀ x : D, ((x:H),(τ x:H)) ∈ T.graph)
    (hflow : ∀ t x y, (x,y) ∈ M.graph → (flow T hs t x,flow T hs t y) ∈ M.graph)
    (hinv : ∀ r, 0 < r → ∀ x : D, timeAverage T hs r x ∈ D)
    (k : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ x : D, ‖(P x:H)‖ ≤ C*∑ j ∈ Finset.range (k+1), ‖((τ^j) x:H)‖) :
    IsSelfAdjoint M := by
  let r : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hr (n : ℕ) : 0 < r n := by dsimp only [r]; positivity
  have hl : Tendsto r atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hPs (x y : D) : inner ℂ (P x:H) (y:H) = inner ℂ (x:H) (P y:H) :=
    formalAdjoint_graph_pairing hMs (hP x) (hP y)
  choose B hB hc hg using fun n => local_energy_regularization D hD P τ M T hM hs hP hτ hPs
    hflow (r n) (hr n) (hinv (r n) (hr n)) k hC hb
  have hdM : Dense (M.domain : Set H) := by
    apply hD.mono
    intro x hx
    obtain ⟨z,hz,_⟩ := M.mem_graph_iff.mp (hP ⟨x,hx⟩)
    change (z:H) = x at hz
    rw [← hz]
    exact z.property
  exact selfAdjoint_of_selfAdjoint_regularizers hdM hM hMs
    (fun n => (timeAverage T hs (r n))^k) B
    (fun n => (timeAverage_selfAdjoint T hs (r n)).pow k) hB hg
    (timeAverage_pow_strong_one T hs r hr hl k)

end StronglyRationalVOA.SymmetricOperator

end

end OAI
