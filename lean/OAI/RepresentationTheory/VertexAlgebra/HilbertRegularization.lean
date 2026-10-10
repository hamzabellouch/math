import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.BoundedMultiplierSingle
import OAI.RepresentationTheory.VertexAlgebra.CutoffPowerControl

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
def regularized (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) (n : ℕ) : Space G →L[ℂ] Space G :=
  (energyExtension h M).comp (((n : ℂ)+1) • complement h hh n)

theorem regularized_core (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (n : ℕ) (x : finiteCore (G := G)) :
    regularized h hh M n x = M (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) := by
  change energyExtension h M (((n : ℂ)+1) • complement h hh n x) = _
  rw [← weighted_resolvent_core h hh n x,energyExtension_weighted h hh M hM]

 
def coreOperator (M : finiteCore (G := G) →ₗ[ℂ] Space G) : Space G →ₗ.[ℂ] Space G where
  domain := finiteCore
  toFun := M

omit [∀ i, CompleteSpace (G i)] in
theorem coreOperator_formalAdjoint (M : finiteCore (G := G) →ₗ[ℂ] Space G)
    (hM : ∀ x y : finiteCore (G := G), inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y)) :
    (coreOperator M).IsFormalAdjoint (coreOperator M) := hM

theorem coreOperator_closable (M : finiteCore (G := G) →ₗ[ℂ] Space G)
    (hM : ∀ x y : finiteCore (G := G), inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y)) :
    (coreOperator M).IsClosable :=
  ((coreOperator M).adjoint_isClosed finiteCore_dense).isClosable.leIsClosable
    ((coreOperator_formalAdjoint M hM).le_adjoint finiteCore_dense)

 
theorem regularized_graph_closure (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable) (n : ℕ) (x : Space G) :
    (resolvent h hh n x,regularized h hh M n x) ∈ (coreOperator M).closure.graph := by
  have hclosed : IsClosed {z : Space G |
      (resolvent h hh n z,regularized h hh M n z) ∈ (coreOperator M).closure.graph} :=
    hc.closure_isClosed.preimage ((resolvent h hh n).continuous.prodMk (regularized h hh M n).continuous)
  have hin : (finiteCore (G := G) : Set (Space G)) ⊆ {z : Space G |
      (resolvent h hh n z,regularized h hh M n z) ∈ (coreOperator M).closure.graph} := by
    intro z hz
    let v : finiteCore (G := G) := ⟨z,hz⟩
    apply LinearPMap.le_graph_of_le (coreOperator M).le_closure
    apply (coreOperator M).mem_graph_iff.mpr
    refine ⟨coreMultiplier (fun i => (resolventWeight h n i : ℂ)) v,rfl,?_⟩
    exact (regularized_core h hh M hM n v).symm
  exact closure_minimal hin hclosed (finiteCore_dense x)

end StronglyRationalVOA.HilbertScale

open scoped Topology
open Filter

namespace StronglyRationalVOA.HilbertScale
open Filter
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

theorem weighted_resolvent_difference (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (n : ℕ)
    (x : finiteCore (G := G)) :
    coreDiagonal (fun i => (h i : ℂ))
      (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x) =
      ((n : ℂ)+1) • (x : Space G) -
        ((n : ℂ)+1) • (coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x : Space G) := by
  rw [weighted_resolvent_core,← smul_sub]
  congr 1
  change complement h hh n x = (x : Space G)-resolvent h hh n x
  exact eq_sub_iff_add_eq.mpr ((add_comm _ _).trans (resolvent_add_complement (G := G) h hh n (x : Space G)))

 

theorem regularized_defect_pairing (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G))
    (n : ℕ) (x y : finiteCore (G := G)) :
    inner ℂ (regularized h hh M n x) (y : Space G) -
      inner ℂ (x : Space G) (regularized h hh M n y) =
    inner ℂ (resolvent h hh n (energyExtension h K (complement h hh n x))) (y : Space G) := by
  let rx := coreMultiplier (fun i => (resolventWeight h n i : ℂ)) x
  let ry := coreMultiplier (fun i => (resolventWeight h n i : ℂ)) y
  let t : ℂ := (n : ℂ)+1
  have ht : t ≠ 0 := by dsimp [t]; exact_mod_cast (show n+1 ≠ 0 by omega)
  have htstar : star t = t := by simp [t]
  have htx : coreDiagonal (fun i => (h i : ℂ)) rx = t • (x : Space G)-t • (rx : Space G) :=
    weighted_resolvent_difference h hh n x
  have hty : coreDiagonal (fun i => (h i : ℂ)) ry = t • (y : Space G)-t • (ry : Space G) :=
    weighted_resolvent_difference h hh n y
  have hnormK : K rx = t • energyExtension h K (complement h hh n x) := by
    rw [← energyExtension_weighted h hh K hK rx,weighted_resolvent_core h hh n x,map_smul]
  have hR : (resolvent (G := G) h hh n).adjoint = resolvent h hh n := resolvent_selfAdjoint h hh n
  have hinner : inner ℂ (energyExtension h K (complement h hh n x)) (ry : Space G) =
      inner ℂ (resolvent h hh n (energyExtension h K (complement h hh n x))) (y : Space G) := by
    change inner ℂ _ (resolvent h hh n (y : Space G)) = _
    simpa only [hR] using (ContinuousLinearMap.adjoint_inner_left (resolvent h hh n)
      (y : Space G) (energyExtension h K (complement h hh n x))).symm
  rw [regularized_core h hh M hM n x,regularized_core h hh M hM n y]
  change inner ℂ (M rx) (y : Space G)-inner ℂ (x : Space G) (M ry) = _
  apply mul_left_cancel₀ ht
  calc
    t * (inner ℂ (M rx) (y : Space G)-inner ℂ (x : Space G) (M ry)) =
        inner ℂ (M rx) (coreDiagonal (fun i => (h i : ℂ)) ry)-
          inner ℂ (coreDiagonal (fun i => (h i : ℂ)) rx) (M ry) := by
      rw [htx,hty]
      simp only [inner_sub_right,inner_sub_left,inner_smul_right,inner_smul_left,
        starRingEnd_apply,htstar]
      rw [hs rx ry]
      ring
    _ = inner ℂ (K rx) (ry : Space G) := hk rx ry
    _ = _ := by rw [hnormK,inner_smul_left,starRingEnd_apply,htstar,hinner]

theorem regularized_defect (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G))
    (n : ℕ) :
    regularized h hh M n - (regularized h hh M n).adjoint =
      (resolvent h hh n).comp ((energyExtension h K).comp (complement h hh n)) := by
  let B := regularized h hh M n
  let Q := (resolvent h hh n).comp ((energyExtension h K).comp (complement h hh n))
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by simpa [DenseRange] using (finiteCore_dense (G := G))
  have hp : ∀ x y : Space G, inner ℂ (B x) y-inner ℂ x (B y) = inner ℂ (Q x) y := by
    intro x y
    refine hd.induction_on₂ ?_ ?_ x y
    · exact isClosed_eq
        (((B.continuous.comp continuous_fst).inner continuous_snd).sub
          (continuous_fst.inner (B.continuous.comp continuous_snd)))
        ((Q.continuous.comp continuous_fst).inner continuous_snd)
    · intro x y
      exact regularized_defect_pairing h hh M K hM hK hs hk n x y
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (B x-B.adjoint x) y = inner ℂ (Q x) y
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  exact hp x y

 

theorem coreOperator_essentialSelfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hs : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G)) :
    IsSelfAdjoint (coreOperator M).closure := by
  have hc := coreOperator_closable M hs
  have hd : Dense ((coreOperator M).closure.domain : Set (Space G)) :=
    finiteCore_dense.mono (LinearPMap.domain_mono.monotone (coreOperator M).le_closure)
  apply SymmetricOperator.selfAdjoint_of_regularizers hd hc.closure_isClosed
    (SymmetricOperator.formalAdjoint_closure hc hc (coreOperator_formalAdjoint M hs))
    (resolvent h hh) (regularized h hh M) (resolvent_selfAdjoint h hh)
    (regularized_graph_closure h hh M hM hc) (resolvent_strong_one h hh)
  intro x
  simp_rw [regularized_defect h hh M K hM hK hs hk]
  have hk0 : Tendsto (fun n => energyExtension h K (complement h hh n x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,map_zero] using (energyExtension h K).continuous.continuousAt.tendsto.comp
      (complement_strong_zero h hh x)
  change Tendsto (fun n => resolvent h hh n (energyExtension h K (complement h hh n x))) atTop (𝓝 0)
  apply squeeze_zero_norm
    (a := fun n => ‖energyExtension h K (complement h hh n x)‖)
  · intro n
    simpa only [one_mul] using
      (resolvent (G := G) h hh n).le_of_opNorm_le (resolvent_norm (G := G) h hh n)
        (energyExtension h K (complement h hh n x))
  · simpa only [norm_zero] using hk0.norm

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.OperatorTransport
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem monotone (E : H ≃ₗᵢ[ℂ] K) : Monotone (transport E) := by
  intro S T hST
  apply LinearPMap.le_of_le_graph
  rw [graph_eq,graph_eq]
  exact Submodule.comap_mono (LinearPMap.le_graph_of_le hST)

theorem closable (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosable) :
    (transport E T).IsClosable :=
  (closed E hT.closure_isClosed).isClosable.leIsClosable (monotone E T.le_closure)

theorem closure (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosable) :
    (transport E T).closure = transport E T.closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (closable E hT).graph_closure_eq_closure_graph,graph_eq,graph_eq,
    ← hT.graph_closure_eq_closure_graph]
  apply SetLike.coe_injective
  change _root_.closure ((graphEquiv E) ⁻¹' (T.graph : Set (K × K))) =
    (graphEquiv E) ⁻¹' _root_.closure (T.graph : Set (K × K))
  exact ((graphEquiv E).preimage_closure _).symm

end StronglyRationalVOA.OperatorTransport

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem coreEnergy_mem (a : V) :
    U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore := by
  have h : (a : Completion V) ∈ HilbertCore.space V := ⟨a,rfl⟩
  rwa [← U.finiteCore_comap_energyCoordinates] at h

 

def coreEnergyCoordinates : V ≃ₗ[ℂ] HilbertScale.finiteCore (G := fun d => A.grade d) :=
  LinearEquiv.ofBijective
    ((U.energyCoordinates.toLinearEquiv.toLinearMap.comp
      (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).toLinearMap).codRestrict _ U.coreEnergy_mem)
    (by
      constructor
      · intro x y h
        exact (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V).injective
          (U.energyCoordinates.injective (congrArg Subtype.val h))
      · intro x
        have hx : U.energyCoordinates.symm x ∈ HilbertCore.space V := by
          rw [← U.finiteCore_comap_energyCoordinates]
          change U.energyCoordinates (U.energyCoordinates.symm x) ∈ HilbertScale.finiteCore
          rw [U.energyCoordinates.apply_symm_apply]
          exact x.property
        obtain ⟨v,hv⟩ := hx
        refine ⟨v,Subtype.ext ?_⟩
        change (v : Completion V) = U.energyCoordinates.symm x at hv
        change U.energyCoordinates (v : Completion V) = x
        rw [hv,U.energyCoordinates.apply_symm_apply])

@[simp] theorem coreEnergyCoordinates_coe (a : V) :
    (U.coreEnergyCoordinates a : HilbertScale.Space (fun d => A.grade d)) =
      U.energyCoordinates (a : Completion V) := rfl

theorem coreEnergyCoordinates_energyShift (a : V) :
    HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) (U.coreEnergyCoordinates a) =
      U.energyCoordinates (A.energyShift a : Completion V) := by
  apply lp.ext
  funext d
  apply Subtype.ext
  simp only [HilbertScale.coreDiagonal_apply,coreEnergyCoordinates_coe,
    Submodule.coe_smul,U.energyCoordinates_coe]
  simp only [energyShift,LinearMap.add_apply,Module.End.one_apply,map_add,
    A.gradeComponent_energy,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast,
    add_smul,one_smul]

 
def spectralCoreMap (T : V →ₗ[ℂ] Completion V) :
    HilbertScale.finiteCore (G := fun d => A.grade d) →ₗ[ℂ] HilbertScale.Space (fun d => A.grade d) :=
  U.energyCoordinates.toLinearEquiv.toLinearMap.comp (T.comp U.coreEnergyCoordinates.symm.toLinearMap)

@[simp] theorem spectralCoreMap_apply (T : V →ₗ[ℂ] Completion V) (a : V) :
    U.spectralCoreMap T (U.coreEnergyCoordinates a) = U.energyCoordinates (T a) := by
  simp [spectralCoreMap]

theorem spectralCoreOperator_transport (T : V →ₗ[ℂ] Completion V) :
    OperatorTransport.transport U.energyCoordinates (HilbertScale.coreOperator (U.spectralCoreMap T)) =
      HilbertCore.operator T := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [OperatorTransport.mem_graph_iff]
  constructor
  · intro h
    obtain ⟨x,hx,hy⟩ := (HilbertScale.coreOperator (U.spectralCoreMap T)).mem_graph_iff.mp h
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    have hv : (v : Completion V) = z.1 := U.energyCoordinates.injective hx
    have hw : T v = z.2 := by
      apply U.energyCoordinates.injective
      change U.spectralCoreMap T (U.coreEnergyCoordinates v) = _ at hy
      simpa only [U.spectralCoreMap_apply] using hy
    apply (HilbertCore.operator T).mem_graph_iff.mpr
    exact ⟨HilbertCore.equiv V v,hv,by simpa only [HilbertCore.operator_apply] using hw⟩
  · intro h
    obtain ⟨x,hx,hy⟩ := (HilbertCore.operator T).mem_graph_iff.mp h
    obtain ⟨v,rfl⟩ := (HilbertCore.equiv V).surjective x
    apply (HilbertScale.coreOperator (U.spectralCoreMap T)).mem_graph_iff.mpr
    refine ⟨U.coreEnergyCoordinates v,congrArg U.energyCoordinates hx,?_⟩
    change U.spectralCoreMap T (U.coreEnergyCoordinates v) = U.energyCoordinates z.2
    rw [U.spectralCoreMap_apply]
    exact congrArg U.energyCoordinates (by simpa only [HilbertCore.operator_apply] using hy)

include U in
 

theorem firstOrder_essentialSelfAdjoint (T K : V →ₗ[ℂ] Completion V) {C D : ℝ}
    (hT : ∀ a, ‖T a‖ ≤ C*‖A.energyShift a‖)
    (hK : ∀ a, ‖K a‖ ≤ D*‖A.energyShift a‖)
    (hs : ∀ x y : V, inner ℂ (T x) (y : Completion V) = inner ℂ (x : Completion V) (T y))
    (hk : ∀ x y : V,
      inner ℂ (T x) (A.energyShift y : Completion V)-
        inner ℂ (A.energyShift x : Completion V) (T y) = inner ℂ (K x) (y : Completion V)) :
    IsSelfAdjoint (HilbertCore.operator T).closure := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  have hT' : ∀ x, ‖U.spectralCoreMap T x‖ ≤
      C*‖HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x‖ := by
    intro x
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyShift,
      U.energyCoordinates.norm_map,Completion.norm_coe] using hT v
  have hK' : ∀ x, ‖U.spectralCoreMap K x‖ ≤
      D*‖HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x‖ := by
    intro x
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_energyShift,
      U.energyCoordinates.norm_map,Completion.norm_coe] using hK v
  have hs' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap T x) y = inner ℂ (x : HilbertScale.Space _) (U.spectralCoreMap T y) := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,U.energyCoordinates.inner_map_map] using hs v w
  have hk' : ∀ x y : HilbertScale.finiteCore (G := fun d => A.grade d),
      inner ℂ (U.spectralCoreMap T x)
          (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) y)-
        inner ℂ (HilbertScale.coreDiagonal (fun d : ℕ => ((1+(d : ℝ) : ℝ) : ℂ)) x)
          (U.spectralCoreMap T y) = inner ℂ (U.spectralCoreMap K x) y := by
    intro x y
    obtain ⟨v,rfl⟩ := U.coreEnergyCoordinates.surjective x
    obtain ⟨w,rfl⟩ := U.coreEnergyCoordinates.surjective y
    simpa only [U.spectralCoreMap_apply,U.coreEnergyCoordinates_coe,
      U.coreEnergyCoordinates_energyShift,U.energyCoordinates.inner_map_map] using hk v w
  have hsa := HilbertScale.coreOperator_essentialSelfAdjoint (fun d : ℕ => 1+(d : ℝ))
    (fun d => by have := Nat.cast_nonneg (α := ℝ) d; linarith) (U.spectralCoreMap T) (U.spectralCoreMap K) hT' hK' hs' hk'
  have hcl := HilbertScale.coreOperator_closable (U.spectralCoreMap T) hs'
  have h := OperatorTransport.selfAdjoint U.energyCoordinates hsa
  rwa [← OperatorTransport.closure U.energyCoordinates hcl,U.spectralCoreOperator_transport] at h

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem smearedCore_essentialSelfAdjoint {a : V} {d p : ℕ}
    (ha : a ∈ A.grade d) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian d a)
    (he : A.PolynomialEnergyBound a) {C : ℝ}
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖A.energyShift v‖)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (HilbertCore.operator (A.smearedMap a d he f hf)).closure := by
  have hf' : RapidCoefficients (fun n => -(n : ℂ)*f n) := by
    simpa only [neg_mul,one_mul] using hf.int_mul.smul (-1)
  apply U.firstOrder_essentialSelfAdjoint (A.smearedMap a d he f hf)
    (A.smearedMap a d he (fun n => -(n : ℂ)*f n) hf')
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) he hf
      (by simpa only [pow_one] using hb) v
  · intro v
    simpa only [pow_one] using A.smearedMap_bound (k := 1) he hf'
      (by simpa only [pow_one] using hb) v
  · exact U.smearedMap_symmetric ha hq hh he hf hr
  · exact U.smearedMap_energy_commutator ha hq hh he hf hr

 
theorem current_closedSmearedOperator_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 1 a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (U.closedSmearedOperator hc a 1 f hf) := by
  obtain ⟨C,_hC,hb⟩ := U.current_linear_energyBound hc ha hq hh
  apply U.smearedCore_essentialSelfAdjoint ha hq hh (U.polynomialEnergyBounds hc a)
    (C := C) (p := 1) (by simpa only [pow_one] using hb) hf hr

 

theorem weightTwo_closedSmearedOperator_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 2) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 2 a)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (U.closedSmearedOperator hc a 2 f hf) := by
  obtain ⟨C,_hC,hb⟩ := U.optimal_quasiPrimary_energyBound hc ha hq hh (by omega)
  apply U.smearedCore_essentialSelfAdjoint ha hq hh (U.polynomialEnergyBounds hc a)
    (C := C) (p := 4) (by simpa only [show 2-1=1 by decide,pow_one] using hb) hf hr

 

theorem stress_closedSmearedOperator_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {f : ℤ → ℂ} (hf : RapidCoefficients f) (hr : ∀ n, star (f n) = f (-n)) :
    IsSelfAdjoint (U.closedSmearedOperator hc A.conformalVector 2 f hf) := by
  have hh : U.IsHermitian 2 A.conformalVector := by
    simp [IsHermitian,U.pct_conformal]
  apply U.smearedCore_essentialSelfAdjoint A.conformal_mem A.conformal_quasiPrimary hh
    (U.polynomialEnergyBounds hc A.conformalVector)
    (C := 1+A.centralCharge.re) (p := 2) ?_ hf hr
  intro n v
  simpa only [A.physicalMode_conformal] using U.virasoro_linear_energy n v

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.SmoothCircleFunction

def IsReal (f : SmoothCircleFunction) : Prop := ∀ t, star (f t) = f t

theorem coefficient_real {f : SmoothCircleFunction} (hf : f.IsReal) (n : ℤ) :
    star (f.coefficient n) = f.coefficient (-n) := by
  rw [coefficient,coefficient,fourierCoeffOn_eq_integral,fourierCoeffOn_eq_integral]
  simp only [star_smul,star_trivial]
  have hc : star (∫ x in (0 : ℝ)..2*Real.pi,
      fourier (-n) (x : AddCircle (2*Real.pi-0)) • f x) =
      ∫ x in (0 : ℝ)..2*Real.pi,
        star (fourier (-n) (x : AddCircle (2*Real.pi-0)) • f x) := by
    exact (Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm _).symm
  rw [hc]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [smul_eq_mul,star_mul,neg_neg]
  rw [hf t, mul_comm]
  rw [show star (fourier (-n) (t : AddCircle (2*Real.pi-0))) =
      fourier n (t : AddCircle (2*Real.pi-0)) from by
        rw [fourier_neg]; exact star_star _]

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

 
theorem stress_closedSmoothField_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {f : SmoothCircleFunction} (hf : f.IsReal) :
    IsSelfAdjoint (U.closedSmoothField hc A.conformalVector 2 f) :=
  U.stress_closedSmearedOperator_selfAdjoint hc f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)

theorem current_closedSmoothField_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 1) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 1 a)
    {f : SmoothCircleFunction} (hf : f.IsReal) :
    IsSelfAdjoint (U.closedSmoothField hc a 1 f) :=
  U.current_closedSmearedOperator_selfAdjoint hc ha hq hh f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)

theorem weightTwo_closedSmoothField_selfAdjoint (hc : A.toVertexAlgebra.C2Cofinite)
    {a : V} (ha : a ∈ A.grade 2) (hq : A.IsQuasiPrimary a) (hh : U.IsHermitian 2 a)
    {f : SmoothCircleFunction} (hf : f.IsReal) :
    IsSelfAdjoint (U.closedSmoothField hc a 2 f) :=
  U.weightTwo_closedSmearedOperator_selfAdjoint hc ha hq hh f.rapid_coefficients (SmoothCircleFunction.coefficient_real hf)

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)

include U in
 

theorem physicalMode_sobolev_bound {a : V} {d k p : ℕ} (ha : a ∈ A.grade d)
    {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n v, ‖A.physicalMode a d n v‖ ≤ C*(1+|(n : ℝ)|)^p*‖(A.energyShift^k) v‖)
    (r : ℕ) (n : ℤ) (v : V) :
    ‖(A.energyShift^r) (A.physicalMode a d n v)‖ ≤
      C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖ := by
  induction r generalizing v with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using hb n v
  | succ r ih =>
    have he : A.energyShift (A.physicalMode a d n v) =
        (-(n : ℂ)) • A.physicalMode a d n v + A.physicalMode a d n (A.energyShift v) :=
      sub_eq_iff_eq_add.mp (A.energyShift_physical_commutator ha n v)
    rw [pow_succ,Module.End.mul_apply,he,map_add,map_smul]
    have hn : ‖-(n : ℂ)‖ = |(n : ℝ)| := by
      rw [norm_neg,← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
    have hp : (A.energyShift^(k+r)) (A.energyShift v) =
        (A.energyShift^(k+(r+1))) v := by
      rw [show k+(r+1)=k+r+1 by omega,pow_succ,Module.End.mul_apply]
    have hm := U.energyShift_pow_norm_mono (show k+r ≤ k+(r+1) by omega) v
    calc
      _ ≤ ‖(-(n : ℂ)) • (A.energyShift^r) (A.physicalMode a d n v)‖ +
          ‖(A.energyShift^r) (A.physicalMode a d n (A.energyShift v))‖ := norm_add_le _ _
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) v‖) +
          C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+r)) (A.energyShift v)‖ := by
        rw [norm_smul,hn]
        exact add_le_add (mul_le_mul_of_nonneg_left (ih v) (abs_nonneg _)) (ih _)
      _ ≤ |(n : ℝ)| *(C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+(r+1))) v‖) +
          C*(1+|(n : ℝ)|)^(p+r)*‖(A.energyShift^(k+(r+1))) v‖ := by
        rw [hp]
        gcongr
      _ = _ := by rw [show p+Nat.succ r=p+r+1 by omega,pow_succ]; ring

end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

namespace StronglyRationalVOA.CFTTypeVOA.UnitaryStructure
open UniformSpace Filter
open scoped Topology
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
end StronglyRationalVOA.CFTTypeVOA.UnitaryStructure

end

end OAI
