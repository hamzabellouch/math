import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.HilbertRegularization

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u v

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace Filter
open scoped Topology
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
include U in
theorem summable_norm_sobolevSmear {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) (v : V) :
    Summable (fun n : ℤ => ‖f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)‖) := by
  obtain ⟨C,hC,p,k,hb⟩ := he.physical A d
  apply hf.summable_norm_smul
    (fun n => (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n))) v
      (C := C) (K := ‖(A.energyShift^(k+r)) v‖) (p := p+r)
  intro n
  simpa only [LinearMap.comp_apply,LinearIsometry.coe_toLinearMap,LinearIsometry.norm_map] using
    U.physicalMode_sobolev_bound ha hC.le hb r n v

 

theorem smearedMap_energyGraph {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (r : ℕ) (v : V) :
    (A.smearedMap a d he f hf v,
      ∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)) ∈
        (U.energyPower r).graph := by
  have hs := (A.summable_norm_physicalSmear he d hf v).of_norm.hasSum.prodMk
    (U.summable_norm_sobolevSmear ha he hf r v).of_norm.hasSum
  apply (U.energyOperator_closed _).mem_of_tendsto hs
  apply Filter.Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro n _
  have hbase : ((A.physicalMode a d n v : Completion V),
      ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)) ∈ (U.energyPower r).graph :=
    (U.energyPower r).mem_graph_iff.mpr
      ⟨⟨_,U.coe_mem_energyOperator _ _⟩,rfl,U.energyPower_coe _ _⟩
  exact (U.energyPower r).graph.smul_mem (f n) hbase

 
theorem smearedMap_mem_smoothEnergySpace {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (v : V) :
    A.smearedMap a d he f hf v ∈ U.smoothEnergySpace := by
  rw [smoothEnergySpace,Submodule.mem_iInf]
  intro r
  obtain ⟨x,hx,_⟩ := (U.energyPower r).mem_graph_iff.mp (U.smearedMap_energyGraph ha he hf r v)
  dsimp only [Prod.fst] at hx
  rw [← hx]
  exact x.property

include U in
theorem smearedMap_sobolev_bound {a : V} {d k p : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    ‖∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V)‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*C)*‖(A.energyShift^(k+r)) v‖ := by
  apply (norm_tsum_le_tsum_norm (U.summable_norm_sobolevSmear ha he hf r v)).trans
  calc
    _ ≤ ∑' n : ℤ, (‖f n‖*(1+|(n : ℝ)|)^(p+r))*(C*‖(A.energyShift^(k+r)) v‖) := by
      apply Summable.tsum_le_tsum _ (U.summable_norm_sobolevSmear ha he hf r v)
        ((hf (p+r)).mul_right _)
      intro n
      simp only [norm_smul,Completion.norm_coe]
      calc
        _ ≤ ‖f n‖*(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖) :=
          mul_le_mul_of_nonneg_left (U.physicalMode_sobolev_bound ha hC hb r n v) (norm_nonneg _)
        _ = _ := by ring
    _ = _ := by rw [tsum_mul_right]; ring

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 

theorem energyExtension_diagonal_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable)
    (x : (diagonal (G := G) (fun i => (h i : ℂ))).domain) :
    (x.val,energyExtension h M (diagonal (fun i => (h i : ℂ)) x)) ∈
      (coreOperator M).closure.graph := by
  let D := diagonal (G := G) (fun i => (h i : ℂ))
  let E := energyExtension h M
  have hclosed : IsClosed {z : Space G × Space G |
      (z.1,E z.2) ∈ (coreOperator M).closure.graph} :=
    hc.closure_isClosed.preimage (continuous_fst.prodMk (E.continuous.comp continuous_snd))
  have hin : ((D.domRestrict finiteCore).graph : Set (Space G × Space G)) ⊆
      {z | (z.1,E z.2) ∈ (coreOperator M).closure.graph} := by
    intro z hz
    obtain ⟨a,ha,hTa⟩ := (D.domRestrict finiteCore).mem_graph_iff.mp hz
    have hv : a.val ∈ finiteCore (G := G) := a.property.1
    let v : finiteCore (G := G) := ⟨a.val,hv⟩
    have hD : D.domRestrict finiteCore a = coreDiagonal (fun i => (h i : ℂ)) v := rfl
    have hw : E z.2 = M v := by
      rw [← hTa,hD]
      exact energyExtension_weighted h hh M hM v
    change (z.1,E z.2) ∈ (coreOperator M).closure.graph
    rw [hw,← ha]
    exact LinearPMap.le_graph_of_le (coreOperator M).le_closure
      ((coreOperator M).mem_graph_iff.mpr ⟨v,rfl,rfl⟩)
  have hDc : (D.domRestrict finiteCore).IsClosable :=
    (diagonal_closed _).isClosable.leIsClosable LinearPMap.domRestrict_le
  have hz : (x.val,D x) ∈ _root_.closure
      ((D.domRestrict finiteCore).graph : Set (Space G × Space G)) := by
    change (x.val,D x) ∈ (D.domRestrict finiteCore).graph.topologicalClosure
    rw [hDc.graph_closure_eq_closure_graph,(diagonal_hasCore _).closure_eq]
    exact D.mem_graph_iff.mpr ⟨x,rfl,rfl⟩
  exact closure_minimal hin hclosed hz

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 

theorem energyExtension_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M N : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hN : ∀ x, ‖N x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (T : Space G →ₗ.[ℂ] Space G) (hc : T.IsClosed)
    (ht : ∀ x, (M x,N x) ∈ T.graph) (x : Space G) :
    (energyExtension h M x,energyExtension h N x) ∈ T.graph := by
  have hclosed : IsClosed {z : Space G |
      (energyExtension h M z,energyExtension h N z) ∈ T.graph} :=
    hc.preimage ((energyExtension h M).continuous.prodMk (energyExtension h N).continuous)
  have hin : (finiteCore (G := G) : Set (Space G)) ⊆
      {z | (energyExtension h M z,energyExtension h N z) ∈ T.graph} := by
    intro z hz
    change (energyExtension h M z,energyExtension h N z) ∈ T.graph
    rw [energyExtension_core h hh M hM ⟨z,hz⟩,energyExtension_core h hh N hN ⟨z,hz⟩]
    exact ht _
  exact closure_minimal hin hclosed (finiteCore_dense x)

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

@[simp] theorem symm_transport (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    transport E.symm (transport E T) = T := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [mem_graph_iff,mem_graph_iff,E.apply_symm_apply,E.apply_symm_apply]

theorem closable_iff (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    (transport E T).IsClosable ↔ T.IsClosable := by
  constructor
  · intro h
    simpa only [symm_transport] using closable E.symm h
  · exact closable E

end StronglyRationalVOA.OperatorTransport

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

local instance : ∀ d : ℕ, FiniteDimensional ℂ (A.grade d) := A.grade_finite

theorem coreEnergyCoordinates_energyPower (k : ℕ) (a : V) :
    HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))
      (U.coreEnergyCoordinates a) = U.energyCoordinates ((A.energyShift^k) a : Completion V) := by
  have hg : ((a : Completion V),((A.energyShift^k) a : Completion V)) ∈ (U.energyPower k).graph :=
    (U.energyPower k).mem_graph_iff.mpr
      ⟨⟨_,U.coe_mem_energyOperator _ a⟩,rfl,U.energyPower_coe k a⟩
  have h := (OperatorTransport.mem_graph_iff U.energyCoordinates _ _ _).mp hg
  obtain ⟨x,hx,hy⟩ := (HilbertScale.diagonal _).mem_graph_iff.mp h
  have hx' : x = ⟨U.coreEnergyCoordinates a,HilbertScale.finiteCore_le_domain _
      (U.coreEnergyCoordinates a).property⟩ := Subtype.ext hx
  rw [hx'] at hy
  exact hy

 
def sobolevExtension (k : ℕ) (T : V →ₗ[ℂ] Completion V) :
    Completion V →L[ℂ] Completion V :=
  U.energyCoordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^k) (U.spectralCoreMap T)).comp
      U.energyCoordinates.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem sobolevExtension_apply (k : ℕ) (T : V →ₗ[ℂ] Completion V) (x : Completion V) :
    U.sobolevExtension k T x = U.energyCoordinates.symm
      (HilbertScale.energyExtension (fun d : ℕ => (1+(d : ℝ))^k) (U.spectralCoreMap T)
        (U.energyCoordinates x)) := rfl

theorem spectralCoreMap_bound (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖) :
    ∀ x, ‖U.spectralCoreMap T x‖ ≤ C *
      ‖HilbertScale.coreDiagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ)) x‖ := by
  intro x
  obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
  simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyPower,
    LinearIsometryEquiv.norm_map,Completion.norm_coe] using hT v

 

theorem sobolevExtension_energyGraph (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hc : (HilbertCore.operator T).IsClosable) (x : (U.energyPower k).domain) :
    (x.val,U.sobolevExtension k T (U.energyPower k x)) ∈ (HilbertCore.operator T).closure.graph := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hc' : (HilbertScale.coreOperator (U.spectralCoreMap T)).IsClosable := by
    apply (OperatorTransport.closable_iff U.energyCoordinates _).mp
    rwa [U.spectralCoreOperator_transport]
  have hh (d : ℕ) : 1 ≤ (1+(d : ℝ))^k :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hx : U.energyCoordinates x.val ∈
      (HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))).domain := x.property
  have h := HilbertScale.energyExtension_diagonal_graph _ hh _
    (U.spectralCoreMap_bound k T hT) hc' ⟨U.energyCoordinates x.val,hx⟩
  rw [← U.spectralCoreOperator_transport T,OperatorTransport.closure U.energyCoordinates hc',
    OperatorTransport.mem_graph_iff]
  have hDx : U.energyCoordinates (U.energyPower k x) =
      HilbertScale.diagonal (fun d : ℕ => (((1+(d : ℝ))^k : ℝ) : ℂ))
        ⟨U.energyCoordinates x.val,hx⟩ := U.energyCoordinates.apply_symm_apply _
  simpa only [U.sobolevExtension_apply,U.energyCoordinates.apply_symm_apply,hDx] using h

include U in
theorem energyPower_domain_le_coreClosure (k : ℕ) (T : V →ₗ[ℂ] Completion V) {C : ℝ}
    (hT : ∀ v, ‖T v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hc : (HilbertCore.operator T).IsClosable) :
    (U.energyPower k).domain ≤ (HilbertCore.operator T).closure.domain := by
  intro x hx
  obtain ⟨y,hy,_⟩ := (HilbertCore.operator T).closure.mem_graph_iff.mp
    (U.sobolevExtension_energyGraph k T hT hc ⟨x,hx⟩)
  change (y : Completion V) = x at hy
  rw [← hy]
  exact y.property

 
theorem sobolevExtension_graph (k : ℕ) (M N : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hM : ∀ v, ‖M v‖ ≤ C*‖(A.energyShift^k) v‖)
    (hN : ∀ v, ‖N v‖ ≤ D*‖(A.energyShift^k) v‖)
    (T : Completion V →ₗ.[ℂ] Completion V) (hc : T.IsClosed)
    (ht : ∀ v, (M v,N v) ∈ T.graph) (x : Completion V) :
    (U.sobolevExtension k M x,U.sobolevExtension k N x) ∈ T.graph := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hh (d : ℕ) : 1 ≤ (1+(d : ℝ))^k :=
    one_le_pow₀ (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have ht' : ∀ v, (U.spectralCoreMap M v,U.spectralCoreMap N v) ∈
      (OperatorTransport.transport U.energyCoordinates.symm T).graph := by
    intro v
    obtain ⟨a,rfl⟩ := U.coreEnergyCoordinates.surjective v
    rw [OperatorTransport.mem_graph_iff,U.spectralCoreMap_apply,U.spectralCoreMap_apply,
      U.energyCoordinates.symm_apply_apply,U.energyCoordinates.symm_apply_apply]
    exact ht a
  have h := HilbertScale.energyExtension_graph _ hh _ _
    (U.spectralCoreMap_bound k M hM) (U.spectralCoreMap_bound k N hN)
    _ (OperatorTransport.closed U.energyCoordinates.symm hc) ht' (U.energyCoordinates x)
  exact (OperatorTransport.mem_graph_iff U.energyCoordinates.symm T _ _).mp h

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 

def weightedSmearedMap {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) :
    V →ₗ[ℂ] Completion V :=
  SummableLinearFamily.tsumMap
    (fun n => f n • (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap.comp
      ((A.energyShift^r).comp (A.physicalMode a d n)))
    (fun v => (U.summable_norm_sobolevSmear ha he hf r v).of_norm)

@[simp] theorem weightedSmearedMap_apply {a : V} {d : ℕ} (ha : a ∈ A.grade d)
    (he : A.PolynomialEnergyBound a) {f : ℤ → ℂ} (hf : RapidCoefficients f) (r : ℕ) (v : V) :
    U.weightedSmearedMap ha he hf r v =
      ∑' n : ℤ, f n • ((A.energyShift^r) (A.physicalMode a d n v) : Completion V) := rfl

theorem smoothEnergySpace_le_closedSmearedDomain (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f) :
    U.smoothEnergySpace ≤ (U.closedSmearedOperator hc a d f hf).domain := by
  obtain ⟨C,_,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  apply le_trans (iInf_le (fun k => (U.energyPower k).domain) k)
  exact U.energyPower_domain_le_coreClosure k _
    (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb)
    (U.smearedCore_closable hc ha hf)

 

theorem closedSmearedOperator_preserves_smoothEnergySpace (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} {d : ℕ} (ha : a ∈ A.grade d) {f : ℤ → ℂ} (hf : RapidCoefficients f)
    (x : (U.closedSmearedOperator hc a d f hf).domain) (hx : x.val ∈ U.smoothEnergySpace) :
    U.closedSmearedOperator hc a d f hf x ∈ U.smoothEnergySpace := by
  obtain ⟨C,hC,p,k,hb⟩ := (U.polynomialEnergyBounds hc a).physical A d
  let M := A.smearedMap a d (U.polynomialEnergyBounds hc a) f hf
  let K : ℝ := (∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^p)*C
  have hK : 0 ≤ K := mul_nonneg
    (tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)) hC.le
  rw [smoothEnergySpace,Submodule.mem_iInf]
  intro r
  let N := U.weightedSmearedMap ha (U.polynomialEnergyBounds hc a) hf r
  have hm : ∀ v, ‖M v‖ ≤ K*‖(A.energyShift^(k+r)) v‖ := by
    intro v
    exact (A.smearedMap_bound (U.polynomialEnergyBounds hc a) hf hb v).trans
      (mul_le_mul_of_nonneg_left (U.energyShift_pow_norm_mono (by omega : k ≤ k+r) v) hK)
  have hn : ∀ v, ‖N v‖ ≤
      ((∑' n : ℤ, ‖f n‖*(1+|(n : ℝ)|)^(p+r))*C)*‖(A.energyShift^(k+r)) v‖ :=
    U.smearedMap_sobolev_bound ha (U.polynomialEnergyBounds hc a) hC.le hb hf r
  have hx' : x.val ∈ (U.energyPower (k+r)).domain :=
    (iInf_le (fun k => (U.energyPower k).domain) (k+r)) hx
  let y := U.energyPower (k+r) ⟨x.val,hx'⟩
  have hvalue : U.closedSmearedOperator hc a d f hf x = U.sobolevExtension (k+r) M y := by
    have h := U.sobolevExtension_energyGraph (k+r) M hm
      (U.smearedCore_closable hc ha hf) ⟨x.val,hx'⟩
    obtain ⟨z,hz,hz'⟩ := (U.closedSmearedOperator hc a d f hf).mem_graph_iff.mp h
    have hzx : z = x := Subtype.ext hz
    rwa [hzx] at hz'
  have hg := U.sobolevExtension_graph (k+r) M N hm hn (U.energyPower r)
    (U.energyOperator_closed _) (U.smearedMap_energyGraph ha (U.polynomialEnergyBounds hc a) hf r) y
  obtain ⟨z,hz,_⟩ := (U.energyPower r).mem_graph_iff.mp hg
  dsimp only [Prod.fst] at hz
  rw [hvalue,← hz]
  exact z.property

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 

theorem shift_im_lower_bound {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T)
    (z : ℂ) (x : T.domain) : |z.im| *‖(x : H)‖ ≤ ‖shift T z x‖ := by
  have him : (inner ℂ (shift T z x) (x : H)).im = z.im*‖(x : H)‖^2 := by
    rw [shift_apply,inner_sub_left,inner_smul_left,inner_self_eq_norm_sq_to_K]
    change (inner ℂ (T x) (x : H)).im - (star z * (‖(x : H)‖ : ℂ)^2).im = _
    rw [real_expectation hs x,← Complex.ofReal_pow]
    simp only [Complex.mul_im,Complex.star_def,Complex.conj_im,
      Complex.ofReal_im,Complex.ofReal_re,mul_zero,zero_add,neg_mul,zero_sub,neg_neg]
  have hi := (Complex.abs_im_le_norm (inner ℂ (shift T z x) (x : H))).trans
    (norm_inner_le_norm (shift T z x) (x : H))
  rw [him,abs_mul,abs_of_nonneg (sq_nonneg ‖(x : H)‖)] at hi
  by_cases hx : ‖(x : H)‖ = 0
  · rw [hx,mul_zero]; positivity
  · have hxpos := lt_of_le_of_ne (norm_nonneg (x : H)) (Ne.symm hx)
    nlinarith

variable [CompleteSpace H]

theorem selfAdjoint_formal {T : H →ₗ.[ℂ] H} (hs : IsSelfAdjoint T) :
    T.IsFormalAdjoint T := by
  have h := LinearPMap.adjoint_isFormalAdjoint hs.dense_domain
  rwa [show T.adjoint = T from hs] at h

 

theorem shift_bijective {T : H →ₗ.[ℂ] H} (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) : Function.Bijective (shift T z).toFun := by
  have hf := selfAdjoint_formal hs
  have hb : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖shift T z x‖ := by
    intro x
    exact (le_mul_of_one_le_left (norm_nonneg _) hz).trans (shift_im_lower_bound hf z x)
  have hclosed := range_closed_of_lower_bound (shift_closed hs.isClosed z) hb
  let : IsClosed (LinearMap.range (shift T z).toFun : Set H) := hclosed
  have hr : LinearMap.range (shift T z).toFun = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    have hg := orthogonal_range_shift hs.dense_domain z hy
    rw [show T.adjoint = T from hs] at hg
    obtain ⟨x,hx,he⟩ := T.mem_graph_iff.mp hg
    have hi := real_expectation hf x
    rw [he,hx,inner_smul_left,inner_self_eq_norm_sq_to_K] at hi
    simp only [starRingEnd_apply,star_star] at hi
    change (z*(‖y‖ : ℂ)^2).im = 0 at hi
    rw [← Complex.ofReal_pow,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,zero_add] at hi
    have him : z.im ≠ 0 := by intro h; rw [h,abs_zero] at hz; norm_num at hz
    have hn : ‖y‖^2 = 0 := (mul_eq_zero.mp hi).resolve_left him
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  constructor
  · change Function.Injective (fun x : T.domain => shift T z x)
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    have h := hb (x-y)
    change ‖((x-y : T.domain) : H)‖ ≤ ‖(T.toFun-z • T.domain.subtype) (x-y)‖ at h
    change (T.toFun-z • T.domain.subtype) x = (T.toFun-z • T.domain.subtype) y at hxy
    rw [map_sub,hxy,sub_self,norm_zero] at h
    exact le_antisymm h (norm_nonneg _)
  · exact LinearMap.range_eq_top.mp hr

 
def resolvent (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) : H →L[ℂ] H :=
  (T.domain.subtype.comp (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).symm.toLinearMap).mkContinuous
    |z.im|⁻¹ (by
      intro y
      let x := (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).symm y
      have hx : shift T z x = y := (LinearEquiv.ofBijective (shift T z).toFun
        (shift_bijective hs z hz)).apply_symm_apply y
      have h := shift_im_lower_bound (selfAdjoint_formal hs) z x
      rw [hx] at h
      change ‖(x : H)‖ ≤ |z.im|⁻¹*‖y‖
      exact (le_inv_mul_iff₀ (lt_of_lt_of_le zero_lt_one hz)).mpr h)

theorem resolvent_graph (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) (y : H) :
    (resolvent T hs z hz y,y+z•resolvent T hs z hz y) ∈ T.graph := by
  apply (shift_graph T z _ _).mp
  exact (shift T z).mem_graph_iff.mpr ⟨_,rfl,
    (LinearEquiv.ofBijective (shift T z).toFun (shift_bijective hs z hz)).apply_symm_apply y⟩

theorem resolvent_shift (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|)
    (x : T.domain) : resolvent T hs z hz (T x-z•(x : H)) = (x : H) := by
  obtain ⟨y,hy,he⟩ := T.mem_graph_iff.mp
    (resolvent_graph T hs z hz (T x-z•(x : H)))
  dsimp only [Prod.fst,Prod.snd] at hy he
  have hshift : shift T z y = shift T z x := by
    rw [shift_apply,shift_apply,he,hy,add_sub_cancel_right]
  have heq : y = x := (shift_bijective hs z hz).injective hshift
  exact hy.symm.trans (congrArg Subtype.val heq)

theorem resolvent_norm_le (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    ‖resolvent T hs z hz‖ ≤ |z.im|⁻¹ := by
  exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (abs_nonneg _)) _

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem resolvent_adjoint (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T) (z : ℂ) (hz : 1 ≤ |z.im|) :
    (resolvent T hs z hz).adjoint =
      resolvent T hs (star z) (by simpa only [Complex.star_def,Complex.conj_im,abs_neg] using hz) := by
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  obtain ⟨a,ha,hTa⟩ := T.mem_graph_iff.mp (resolvent_graph T hs z hz x)
  obtain ⟨b,hb,hTb⟩ := T.mem_graph_iff.mp (resolvent_graph T hs (star z)
    (by simpa only [Complex.star_def,Complex.conj_im,abs_neg] using hz) y)
  dsimp only [Prod.fst,Prod.snd] at ha hb hTa hTb
  have h := selfAdjoint_formal hs a b
  rw [hTa,hTb,ha,hb,inner_add_left,inner_add_right,inner_smul_left,inner_smul_right] at h
  exact (add_right_cancel (show inner ℂ x (resolvent T hs (star z) _ y) +
      star z * inner ℂ (resolvent T hs z hz x) (resolvent T hs (star z) _ y) =
    inner ℂ (resolvent T hs z hz x) y +
      star z * inner ℂ (resolvent T hs z hz x) (resolvent T hs (star z) _ y) from h)).symm

 

theorem boundedPerturbation_shift_surjective (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (K : H →L[ℂ] H) (z : ℂ) (hz : 1 ≤ |z.im|) (hK : ‖K‖ < |z.im|) :
    ∀ y : H, ∃ x : T.domain, T x-z•(x : H)+K x = y := by
  let R := resolvent T hs z hz
  have hzpos : 0 < |z.im| := lt_of_lt_of_le zero_lt_one hz
  have hn : ‖-(K*R)‖ < 1 := by
    rw [norm_neg]
    calc
      _ ≤ ‖K‖*‖R‖ := norm_mul_le _ _
      _ ≤ ‖K‖*|z.im|⁻¹ := mul_le_mul_of_nonneg_left (resolvent_norm_le T hs z hz) (norm_nonneg _)
      _ < 1 := (mul_inv_lt_iff₀ hzpos).mpr (by simpa using hK)
  have hu : IsUnit (1+K*R) := by
    simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hn
  have hsur := (ContinuousLinearMap.isUnit_iff_bijective.mp hu).surjective
  intro y
  obtain ⟨w,hw⟩ := hsur y
  obtain ⟨x,hx,hTx⟩ := T.mem_graph_iff.mp (resolvent_graph T hs z hz w)
  dsimp only [Prod.fst,Prod.snd] at hx hTx
  refine ⟨x,?_⟩
  rw [hTx,hx,add_sub_cancel_right]
  exact hw

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
def inverseEnergy (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) : Space G →L[ℂ] Space G :=
  boundedMultiplier (fun i => (h i : ℂ)⁻¹) zero_le_one (by
    intro i
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (zero_le_one.trans (hh i))]
    exact inv_le_one_of_one_le₀ (hh i))

omit [DecidableEq ι] in
theorem inverseEnergy_apply (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) (i : ι) :
    inverseEnergy h hh x i = (h i : ℂ)⁻¹ • x i := rfl

theorem inverseEnergy_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : finiteCore (G := G)) :
    inverseEnergy h hh x = (coreMultiplier (fun i => (h i : ℂ)⁻¹) x : Space G) := by
  ext i
  rfl
end StronglyRationalVOA.HilbertScale

end

end OAI
