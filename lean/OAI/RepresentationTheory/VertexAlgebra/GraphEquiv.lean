import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.GraphCommutants

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

noncomputable section

namespace StronglyRationalVOA
universe u v
open Filter
open scoped ContDiff
open scoped ENNReal
namespace OperatorTransport
variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
def graphEquiv (E : H ≃ₗᵢ[ℂ] K) : (H × H) ≃L[ℂ] (K × K) :=
  E.toContinuousLinearEquiv.prodCongr E.toContinuousLinearEquiv

theorem graph_eq (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) :
    (transport E T).graph = T.graph.comap (graphEquiv E).toLinearMap := by
  ext z
  exact mem_graph_iff E T z.1 z.2

theorem closed (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosed) :
    (transport E T).IsClosed := by
  rw [LinearPMap.IsClosed,graph_eq]
  exact hT.preimage (graphEquiv E).continuous

theorem dense (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K}
    (hT : Dense (T.domain : Set K)) : Dense ((transport E T).domain : Set H) :=
  hT.preimage E.toHomeomorph.isOpenMap

variable [CompleteSpace H] [CompleteSpace K]

theorem adjoint (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K}
    (hT : Dense (T.domain : Set K)) :
    (transport E T).adjoint = transport E T.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (dense E hT)]
  ext z
  rw [mem_graph_iff,LinearPMap.adjoint_graph_eq_graph_adjoint hT]
  simp only [Submodule.mem_adjoint_iff]
  constructor
  · intro hz a b hab
    have hh := hz (E.symm a) (E.symm b) ((mem_graph_iff E T _ _).mpr (by simpa using hab))
    rw [← E.inner_map_map (E.symm b) z.1, ← E.inner_map_map (E.symm a) z.2,
      E.apply_symm_apply,E.apply_symm_apply] at hh
    exact hh
  · intro hz a b hab
    have hh := hz (E a) (E b) ((mem_graph_iff E T _ _).mp hab)
    simpa only [E.inner_map_map] using hh

theorem selfAdjoint (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (transport E T) := by
  rw [LinearPMap.isSelfAdjoint_def,adjoint E hT.dense_domain,
    (LinearPMap.isSelfAdjoint_def.mp hT)]

omit [CompleteSpace H] [CompleteSpace K] in
theorem domRestrict (E : H ≃ₗᵢ[ℂ] K) (T : K →ₗ.[ℂ] K) (S : Submodule ℂ K) :
    (transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap) =
      transport E (T.domRestrict S) := by
  apply LinearPMap.eq_of_eq_graph
  ext z
  rw [mem_graph_iff]
  simp only [LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨x,hx,hy⟩
    exact ⟨⟨E x.val,x.property⟩,congrArg E hx,by rw [← hy]; exact (E.apply_symm_apply _).symm⟩
  · rintro ⟨x,hx,hy⟩
    have hz : z.1 ∈ ((transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap)).domain := by
      change E z.1 ∈ S ⊓ T.domain
      rw [← hx]; exact x.property
    refine ⟨⟨z.1,hz⟩,rfl,?_⟩
    change E.symm (T ⟨E z.1,hz.2⟩) = z.2
    have heq : (⟨E z.1,hz.2⟩ : T.domain) = ⟨x.val,x.property.2⟩ := Subtype.ext hx.symm
    rw [heq]
    change E.symm ((T.domRestrict S) x) = _
    rw [hy,E.symm_apply_apply]

omit [CompleteSpace H] [CompleteSpace K] in
theorem hasCore (E : H ≃ₗᵢ[ℂ] K) {T : K →ₗ.[ℂ] K} (hT : T.IsClosed)
    {S : Submodule ℂ K} (hS : T.HasCore S) :
    (transport E T).HasCore (S.comap E.toLinearEquiv.toLinearMap) := by
  have hle : (transport E T).domRestrict (S.comap E.toLinearEquiv.toLinearMap) ≤
      transport E T := LinearPMap.domRestrict_le
  have hle' : T.domRestrict S ≤ T := LinearPMap.domRestrict_le
  have hc := (closed E hT).isClosable.leIsClosable hle
  have hc' := hT.isClosable.leIsClosable hle' 
  refine ⟨fun x hx => hS.le_domain hx,?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hc.graph_closure_eq_closure_graph,domRestrict,graph_eq,graph_eq]
  have hh : (T.domRestrict S).graph.topologicalClosure = T.graph := by
    rw [hc'.graph_closure_eq_closure_graph,hS.closure_eq]
  apply SetLike.coe_injective
  change closure ((graphEquiv E) ⁻¹' ((T.domRestrict S).graph : Set (K × K))) =
    (graphEquiv E) ⁻¹' (T.graph : Set (K × K))
  rw [← (graphEquiv E).preimage_closure]
  exact congrArg (fun s : Set (K × K) => (graphEquiv E) ⁻¹' s) (congrArg SetLike.coe hh)

end OperatorTransport

namespace CFTTypeVOA.UnitaryStructure
open UniformSpace
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {A : CFTTypeVOA V} (U : A.UnitaryStructure)

theorem finiteCore_comap_energyCoordinates :
    (HilbertScale.finiteCore (G := fun d => A.grade d)).comap
      U.energyCoordinates.toLinearEquiv.toLinearMap = HilbertCore.space V := by
  classical
  apply le_antisymm
  · intro x hx
    have h : ∀ z ∈ HilbertScale.finiteCore (G := fun d => A.grade d),
        U.energyCoordinates.symm z ∈ HilbertCore.space V := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨d,a,rfl⟩ := hz
        rw [← U.energyCoordinates_grade a,U.energyCoordinates.symm_apply_apply]
        exact ⟨a.val,rfl⟩
      | zero => simpa only [map_zero] using (HilbertCore.space V).zero_mem
      | add z w _ _ hz hw => simpa only [map_add] using (HilbertCore.space V).add_mem hz hw
      | smul c z _ hz => simpa only [map_smul] using (HilbertCore.space V).smul_mem c hz
    simpa only [LinearIsometryEquiv.symm_apply_apply] using h (U.energyCoordinates x) hx
  · rintro x ⟨a,rfl⟩
    change U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore
    apply A.homogeneous_induction (P := fun a =>
      U.energyCoordinates (a : Completion V) ∈ HilbertScale.finiteCore)
    · change U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) 0) ∈ _
      rw [map_zero,map_zero]
      exact Submodule.zero_mem _
    · intro d b hb
      rw [U.energyCoordinates_grade ⟨b,hb⟩]
      exact HilbertScale.single_mem_finiteCore _ _
    · intro b c hb hc
      change U.energyCoordinates ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (b+c)) ∈ _
      rw [map_add,map_add]
      exact Submodule.add_mem _ hb hc

 

def energyOperator (w : ℕ → ℝ) : Completion V →ₗ.[ℂ] Completion V :=
  OperatorTransport.transport U.energyCoordinates
    (HilbertScale.diagonal (fun d => (w d : ℂ)))

theorem energyOperator_closed (w : ℕ → ℝ) : (U.energyOperator w).IsClosed :=
  OperatorTransport.closed _ (HilbertScale.diagonal_closed _)

theorem energyOperator_dense (w : ℕ → ℝ) :
    Dense ((U.energyOperator w).domain : Set (Completion V)) :=
  OperatorTransport.dense _ (HilbertScale.domain_dense _)

theorem energyOperator_selfAdjoint (w : ℕ → ℝ) : IsSelfAdjoint (U.energyOperator w) := by
  let : ∀ d, FiniteDimensional ℂ (A.grade d) := A.grade_finite
  exact OperatorTransport.selfAdjoint _ (HilbertScale.real_diagonal_selfAdjoint w)

 

theorem energyOperator_hasCore (w : ℕ → ℝ) :
    (U.energyOperator w).HasCore (HilbertCore.space V) := by
  have h := OperatorTransport.hasCore U.energyCoordinates
    (HilbertScale.diagonal_closed (G := fun d => A.grade d) (fun d => (w d : ℂ)))
    (HilbertScale.diagonal_hasCore (fun d => (w d : ℂ)))
  rw [U.finiteCore_comap_energyCoordinates] at h
  exact h

theorem coe_mem_energyOperator (w : ℕ → ℝ) (a : V) :
    (a : Completion V) ∈ (U.energyOperator w).domain :=
  (U.energyOperator_hasCore w).le_domain ⟨a,rfl⟩

 
def conformalHamiltonian : Completion V →ₗ.[ℂ] Completion V :=
  U.energyOperator (fun d => d)

 
def energyPower (k : ℕ) : Completion V →ₗ.[ℂ] Completion V :=
  U.energyOperator (fun d => (1+(d : ℝ))^k)

theorem energyOperator_grade (w : ℕ → ℝ) {d : ℕ} (a : A.grade d) :
    U.energyOperator w ⟨(a.val : Completion V),U.coe_mem_energyOperator w a.val⟩ =
      (w d : ℂ) • (a.val : Completion V) := by
  have hg : ((a.val : Completion V), (w d : ℂ) • (a.val : Completion V)) ∈
      (U.energyOperator w).graph := by
    apply (OperatorTransport.mem_graph_iff _ _ _ _).mpr
    rw [map_smul,U.energyCoordinates_grade]
    apply (HilbertScale.diagonal (fun d => (w d : ℂ))).mem_graph_iff.mpr
    refine ⟨⟨_,HilbertScale.single_mem_domain _ _ _⟩,rfl,?_⟩
    rw [HilbertScale.diagonal_single]
    ext i
    simp only [lp.coeFn_smul,Pi.smul_apply]
    by_cases hi : i = d
    · subst i; simp
    · simp [lp.single_apply,hi]
  obtain ⟨x,hx,hy⟩ := (U.energyOperator w).mem_graph_iff.mp hg
  have heq : x = ⟨(a.val : Completion V),U.coe_mem_energyOperator w a.val⟩ :=
    Subtype.ext hx
  rwa [heq] at hy

 
theorem energyPower_coe (k : ℕ) (a : V) :
    U.energyPower k ⟨(a : Completion V),U.coe_mem_energyOperator _ a⟩ =
      ((A.energyShift^k) a : Completion V) := by
  apply A.homogeneous_induction (P := fun a =>
    U.energyPower k ⟨(a : Completion V),U.coe_mem_energyOperator _ a⟩ =
      ((A.energyShift^k) a : Completion V))
  · change (U.energyPower k).toFun 0 = ((Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V)
      ((A.energyShift^k) 0))
    rw [map_zero,map_zero,map_zero]
  · intro d b hb
    calc
      _ = (((1+(d : ℝ))^k : ℝ) : ℂ) • (b : Completion V) :=
        U.energyOperator_grade (fun d => (1+(d : ℝ))^k) ⟨b,hb⟩
      _ = ((A.energyShift^k) b : Completion V) := by
        rw [A.energyShift_pow_on_grade hb]
        change _ = (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) (_ • b)
        rw [map_smul,Complex.ofReal_pow,Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_natCast]
        rfl
  · intro b c hb hc
    have hbc : ((b+c : V) : Completion V) = (b : Completion V) + (c : Completion V) :=
      map_add (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) b c
    have hx : (⟨((b+c : V) : Completion V),U.coe_mem_energyOperator _ (b+c)⟩ :
        (U.energyPower k).domain) =
      ⟨(b : Completion V),U.coe_mem_energyOperator _ b⟩ +
      ⟨(c : Completion V),U.coe_mem_energyOperator _ c⟩ := Subtype.ext hbc
    rw [hx,(U.energyPower k).map_add,hb,hc]
    change _ = (Completion.toComplₗᵢ : V →ₗᵢ[ℂ] Completion V) ((A.energyShift^k) (b+c))
    rw [map_add,map_add]
    rfl

 

def smoothEnergySpace : Submodule ℂ (Completion V) := ⨅ k : ℕ, (U.energyPower k).domain

theorem core_le_smoothEnergySpace : HilbertCore.space V ≤ U.smoothEnergySpace := by
  apply le_iInf
  intro k
  exact (U.energyOperator_hasCore _).le_domain

theorem smoothEnergySpace_dense : Dense (U.smoothEnergySpace : Set (Completion V)) :=
  HilbertCore.dense.mono U.core_le_smoothEnergySpace

end CFTTypeVOA.UnitaryStructure

end StronglyRationalVOA

open scoped Topology
open Filter
namespace StronglyRationalVOA
namespace SymmetricOperator
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

 
def shift (T : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H where
  domain := T.domain
  toFun := T.toFun - z • T.domain.subtype

@[simp] theorem shift_apply (T : H →ₗ.[ℂ] H) (z : ℂ) (x : T.domain) :
    shift T z x = T x - z • (x : H) := rfl

theorem shift_graph (T : H →ₗ.[ℂ] H) (z : ℂ) (x y : H) :
    (x,y) ∈ (shift T z).graph ↔ (x,y+z•x) ∈ T.graph := by
  rw [(shift T z).mem_graph_iff,T.mem_graph_iff]
  dsimp only [Prod.fst,Prod.snd]
  constructor
  · rintro ⟨a,ha,hb⟩
    refine ⟨a,ha,?_⟩
    change T a - z • (a : H) = y at hb
    rw [← ha,← hb]; abel
  · rintro ⟨a,ha,hb⟩
    exact ⟨a,ha,by change T a - z • (a : H) = y; rw [hb,ha]; abel⟩

theorem shift_closed {T : H →ₗ.[ℂ] H} (hT : T.IsClosed) (z : ℂ) :
    (shift T z).IsClosed := by
  have heq : ((shift T z).graph : Set (H × H)) =
      (fun p : H × H => (p.1,p.2+z•p.1)) ⁻¹' T.graph := by
    ext x; exact shift_graph T z x.1 x.2
  rw [LinearPMap.IsClosed,heq]
  exact hT.preimage (continuous_fst.prodMk (continuous_snd.add (continuous_fst.const_smul z)))

theorem real_expectation {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    (inner ℂ (T x) (x : H)).im = 0 := by
  have h := congrArg Complex.im (hs x x)
  have hc := inner_conj_symm (𝕜 := ℂ) (T x) (x : H)
  have hi := congrArg Complex.im hc
  simp only [Complex.conj_im] at hi
  linarith

theorem shift_I_norm_sq {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    ‖shift T Complex.I x‖^2 = ‖T x‖^2 + ‖(x : H)‖^2 := by
  rw [shift_apply,norm_sub_sq (𝕜 := ℂ),inner_smul_right,norm_smul,Complex.norm_I,one_mul]
  have hh := real_expectation hs x
  simp only [RCLike.re_to_complex,Complex.mul_re,Complex.I_re,Complex.I_im,
    zero_mul,hh,mul_zero,sub_zero]

theorem shift_I_lower_bound {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T) (x : T.domain) :
    ‖(x : H)‖ ≤ ‖shift T Complex.I x‖ := by
  have hh := shift_I_norm_sq hs x
  nlinarith [sq_nonneg ‖T x‖,norm_nonneg (shift T Complex.I x),norm_nonneg (x : H)]

variable [CompleteSpace H]

 

theorem range_closed_of_lower_bound {T : H →ₗ.[ℂ] H} (hT : T.IsClosed)
    (hb : ∀ x : T.domain, ‖(x : H)‖ ≤ ‖T x‖) :
    IsClosed (LinearMap.range T.toFun : Set H) := by
  apply IsSeqClosed.isClosed
  intro a y ha hay
  choose x hx using ha
  change ∀ n, T (x n) = a n at hx
  have hc : CauchySeq (fun n => (x n : H)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hay.cauchySeq ε hε
    refine ⟨N,fun m hm n hn => ?_⟩
    calc
      dist (x m : H) (x n : H) = ‖((x m-x n : T.domain) : H)‖ := by simp [dist_eq_norm]
      _ ≤ ‖T (x m-x n)‖ := hb _
      _ = dist (a m) (a n) := by rw [T.map_sub,hx m,hx n,dist_eq_norm]
      _ < ε := hN m hm n hn
  obtain ⟨v,hv⟩ := cauchySeq_tendsto_of_complete hc
  have hg : (v,y) ∈ T.graph := hT.mem_of_tendsto (hv.prodMk_nhds hay)
    (Eventually.of_forall (fun n => T.mem_graph_iff.mpr ⟨x n,rfl,hx n⟩))
  obtain ⟨w,_,hw⟩ := T.mem_graph_iff.mp hg
  exact ⟨w,hw⟩

 

theorem orthogonal_range_shift {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (z : ℂ) {y : H}
    (hy : y ∈ (LinearMap.range (shift T z).toFun)ᗮ) :
    (y,star z • y) ∈ T.adjoint.graph := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint hd]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  obtain ⟨x,hx,hTx⟩ := T.mem_graph_iff.mp hab
  dsimp only [Prod.fst,Prod.snd] at hx hTx
  have hh := ((LinearMap.range (shift T z).toFun).mem_orthogonal y).mp hy
    (shift T z x) ⟨x,rfl⟩
  rw [shift_apply,inner_sub_left,inner_smul_left] at hh
  rw [← hx,← hTx,inner_smul_right]
  simpa only [starRingEnd_apply] using hh

 

theorem selfAdjoint_of_deficiency_zero {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (hp : ∀ y : H, (y,Complex.I • y) ∈ T.adjoint.graph → y = 0)
    (hm : ∀ y : H, (y,(-Complex.I) • y) ∈ T.adjoint.graph → y = 0) :
    IsSelfAdjoint T := by
  have hclosed : IsClosed (LinearMap.range (shift T Complex.I).toFun : Set H) :=
    range_closed_of_lower_bound (shift_closed hT _) (shift_I_lower_bound hs)
  let : IsClosed (LinearMap.range (shift T Complex.I).toFun : Set H) := hclosed
  have hr : LinearMap.range (shift T Complex.I).toFun = ⊤ := by
    apply Submodule.orthogonal_eq_bot_iff.mp
    apply (Submodule.eq_bot_iff _).mpr
    intro y hy
    apply hm y
    simpa only [Complex.star_def,Complex.conj_I] using orthogonal_range_shift hd Complex.I hy
  have hle : T ≤ T.adjoint := hs.le_adjoint hd
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm _ hle
  apply LinearPMap.le_of_le_graph
  intro p hpgraph
  obtain ⟨y,hy,hTy⟩ := T.adjoint.mem_graph_iff.mp hpgraph
  have hv : T.adjoint y - Complex.I • (y : H) ∈ LinearMap.range (shift T Complex.I).toFun := by
    rw [hr]; trivial
  obtain ⟨x,hx⟩ := hv
  have hxadj : (x : H) ∈ T.adjoint.domain := hle.1 x.property
  let x' : T.adjoint.domain := ⟨x,hxadj⟩
  have hTx : T.adjoint x' = T x := by
    exact (hle.2 (x := x) (y := x') rfl).symm
  have hzero : (y : H) - x = 0 := by
    apply hp
    refine T.adjoint.mem_graph_iff.mpr ⟨y-x',rfl,?_⟩
    rw [T.adjoint.map_sub,hTx]
    change T x - Complex.I • (x : H) = T.adjoint y - Complex.I • (y : H) at hx
    simp only [smul_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mpr hx.symm
  have hxy : (x : H) = (y : H) := (sub_eq_zero.mp hzero).symm
  refine T.mem_graph_iff.mpr ⟨x,hxy.trans hy,?_⟩
  rw [← hTy,← hTx]
  congr 1
  exact Subtype.ext hxy

omit [CompleteSpace H] in
 

theorem formalAdjoint_closure {T S : H →ₗ.[ℂ] H}
    (hT : T.IsClosable) (hS : S.IsClosable) (hs : T.IsFormalAdjoint S) :
    T.closure.IsFormalAdjoint S.closure := by
  intro x y
  have hx : ((x : H),T.closure x) ∈ T.graph.topologicalClosure := by
    rw [hT.graph_closure_eq_closure_graph]
    exact T.closure.mem_graph_iff.mpr ⟨x,rfl,rfl⟩
  have hy : ((y : H),S.closure y) ∈ S.graph.topologicalClosure := by
    rw [hS.graph_closure_eq_closure_graph]
    exact S.closure.mem_graph_iff.mpr ⟨y,rfl,rfl⟩
  have hleft : ∀ q ∈ S.graph, ∀ p ∈ T.graph.topologicalClosure,
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
    intro q hq
    apply closure_minimal
    · intro p hp
      obtain ⟨a,ha,hTa⟩ := T.mem_graph_iff.mp hp
      obtain ⟨b,hb,hSb⟩ := S.mem_graph_iff.mp hq
      change inner ℂ p.2 q.1 = inner ℂ p.1 q.2
      rw [← ha,← hTa,← hb,← hSb]
      exact hs a b
    · exact isClosed_eq (continuous_snd.inner continuous_const)
        (continuous_fst.inner continuous_const)
  have hright : ∀ q ∈ S.graph.topologicalClosure,
      inner ℂ (T.closure x) q.1 = inner ℂ (x : H) q.2 := by
    apply closure_minimal
    · intro q hq; exact hleft q hq _ hx
    · exact isClosed_eq (continuous_const.inner continuous_fst)
        (continuous_const.inner continuous_snd)
  exact hright _ hy

 

theorem regularizer_adjoint {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (R B : H →L[ℂ] H)
    (hR : IsSelfAdjoint R) (hg : ∀ x : H, (R x,B x) ∈ T.graph)
    {y z : H} (hy : (y,z) ∈ T.adjoint.graph) :
    B.adjoint y = R z := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hh := (Submodule.mem_adjoint_iff _ _).mp
    (by rwa [← LinearPMap.adjoint_graph_eq_graph_adjoint hd] : (y,z) ∈ T.graph.adjoint)
    (R x) (B x) (hg x)
  have hRadj : R.adjoint = R := hR
  rw [← hRadj,ContinuousLinearMap.adjoint_inner_right]
  exact sub_eq_zero.mp hh

 

theorem selfAdjoint_of_regularizers {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) (hT : T.IsClosed) (hs : T.IsFormalAdjoint T)
    (R B : ℕ → H →L[ℂ] H)
    (hR : ∀ n, IsSelfAdjoint (R n))
    (hg : ∀ n x, (R n x,B n x) ∈ T.graph)
    (hlim : ∀ x, Tendsto (fun n => R n x) atTop (𝓝 x))
    (hcomm : ∀ x, Tendsto (fun n => (B n - (B n).adjoint) x) atTop (𝓝 0)) :
    IsSelfAdjoint T := by
  have hreal : ∀ y z : H, (y,z) ∈ T.adjoint.graph → (inner ℂ z y).im = 0 := by
    intro y z hy
    have hBadj : ∀ n, (B n).adjoint y = R n z :=
      fun n => regularizer_adjoint hd (R n) (B n) (hR n) (hg n) hy
    have hBl : Tendsto (fun n => B n y) atTop (𝓝 z) := by
      have hh := (hcomm y).add (hlim z)
      simp only [sub_apply,← hBadj,sub_add_cancel,zero_add] at hh
      exact hh
    have hre : ∀ n, (inner ℂ (B n y) (R n y)).im = 0 := by
      intro n
      obtain ⟨x,hx,hBx⟩ := T.mem_graph_iff.mp (hg n y)
      dsimp only [Prod.fst,Prod.snd] at hx hBx
      rw [← hx,← hBx]
      exact real_expectation hs x
    have hilt := Complex.continuous_im.continuousAt.tendsto.comp (hBl.inner (hlim y))
    have heq : (fun n => (inner ℂ (B n y) (R n y)).im) = fun _ => (0 : ℝ) := funext hre
    change Tendsto (fun n => (inner ℂ (B n y) (R n y)).im) atTop (𝓝 _) at hilt
    rw [heq] at hilt
    exact (tendsto_nhds_unique hilt tendsto_const_nhds)
  apply selfAdjoint_of_deficiency_zero hd hT hs
  · intro y hy
    have hh := hreal y (Complex.I • y) hy
    rw [inner_smul_left] at hh
    simp only [Complex.conj_I,neg_mul,Complex.mul_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,Complex.neg_im,
      inner_self_eq_norm_sq_to_K] at hh
    have hy0 : ‖y‖^2 = 0 := by
      simp only [neg_eq_zero] at hh
      change ((‖y‖ : ℂ)^2).re = 0 at hh
      simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hy0)
  · intro y hy
    have hh := hreal y ((-Complex.I) • y) hy
    rw [inner_smul_left] at hh
    simp only [map_neg,Complex.conj_I,neg_neg,Complex.mul_im,
      Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add,
      inner_self_eq_norm_sq_to_K] at hh
    have hy0 : ‖y‖^2 = 0 := by
      change ((‖y‖ : ℂ)^2).re = 0 at hh
      simpa only [← Complex.ofReal_pow,Complex.ofReal_re] using hh
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hy0)

end SymmetricOperator
end StronglyRationalVOA

namespace StronglyRationalVOA
namespace HilbertScale
open scoped ENNReal
universe u
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 
def boundedMultiplier (w : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) :
    Space G →L[ℂ] Space G :=
  lp.mapCLM 2 (fun i => w i • ContinuousLinearMap.id ℂ (G i)) hC
    (fun i => (norm_smul_le _ _).trans ((mul_le_mul_of_nonneg_left
      ContinuousLinearMap.norm_id_le (norm_nonneg (w i))).trans (by simpa using hw i)))

omit [DecidableEq ι] in
@[simp] theorem boundedMultiplier_apply (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) (x : Space G) (i : ι) :
    boundedMultiplier w hC hw x i = w i • x i := rfl

omit [DecidableEq ι] in
theorem boundedMultiplier_norm (w : ι → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hw : ∀ i, ‖w i‖ ≤ C) : ‖boundedMultiplier (G := G) w hC hw‖ ≤ C :=
  lp.norm_mapCLM_le _ _ _ _
end HilbertScale
end StronglyRationalVOA

end

end OAI
