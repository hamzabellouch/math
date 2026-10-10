import Mathlib
import OAI.RepresentationTheory.VertexAlgebra.SummableNormSobolev

namespace OAI

/-! Vertex algebra, energy bounds and closed smeared-field operators. -/

universe u

noncomputable section
open scoped Topology
open Filter
namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]
omit [DecidableEq ι] in
theorem inverseEnergy_selfAdjoint (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) :
    IsSelfAdjoint (inverseEnergy (G := G) h hh) := by
  change (inverseEnergy (G := G) h hh).adjoint = inverseEnergy h hh
  unfold inverseEnergy
  rw [boundedMultiplier_adjoint]
  ext x i
  simp only [boundedMultiplier_apply,map_inv₀,Complex.star_def,Complex.conj_ofReal]

omit [DecidableEq ι] in
theorem inverseEnergy_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i) (x : Space G) :
    (inverseEnergy h hh x,x) ∈ (diagonal (fun i => (h i : ℂ))).graph := by
  apply (mem_graph_iff _ _ _).mpr
  intro i
  rw [inverseEnergy_apply,smul_smul,mul_inv_cancel₀,one_smul]
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))

omit [DecidableEq ι] in
theorem inverseEnergy_diagonal (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : (diagonal (G := G) (fun i => (h i : ℂ))).domain) :
    inverseEnergy h hh (diagonal (fun i => (h i : ℂ)) x) = (x : Space G) := by
  ext i
  rw [inverseEnergy_apply,diagonal_apply,smul_smul,inv_mul_cancel₀,one_smul]
  exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (hh i)))

theorem energyExtension_inverse_graph (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable) (x : Space G) :
    (inverseEnergy h hh x,energyExtension h M x) ∈ (coreOperator M).closure.graph := by
  obtain ⟨v,hv,he⟩ := (diagonal (fun i => (h i : ℂ))).mem_graph_iff.mp (inverseEnergy_graph h hh x)
  have hg := energyExtension_diagonal_graph h hh M hM hc v
  dsimp only [Prod.fst,Prod.snd] at hv he
  rwa [hv,he] at hg

 

theorem energyExtension_defect (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M K : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hk : ∀ x y : finiteCore (G := G),
      inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
        inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G)) :
    energyExtension h M - (energyExtension h M).adjoint =
      (inverseEnergy h hh).comp (energyExtension h K) := by
  let E := energyExtension h M
  let F := (inverseEnergy h hh).comp (energyExtension h K)
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by
    simpa [DenseRange] using (finiteCore_dense (G := G))
  have hp : ∀ x y : Space G, inner ℂ (E x) y-inner ℂ x (E y) = inner ℂ (F x) y := by
    intro x y
    refine hd.induction_on₂ ?_ ?_ x y
    · exact isClosed_eq
        (((E.continuous.comp continuous_fst).inner continuous_snd).sub
          (continuous_fst.inner (E.continuous.comp continuous_snd)))
        ((F.continuous.comp continuous_fst).inner continuous_snd)
    · intro x y
      let sx := coreMultiplier (fun i => (h i : ℂ)⁻¹) x
      let sy := coreMultiplier (fun i => (h i : ℂ)⁻¹) y
      have hcx : coreDiagonal (fun i => (h i : ℂ)) sx = (x : Space G) :=
        congrArg Subtype.val (coreMultiplier_cancel h hh x)
      have hcy : coreDiagonal (fun i => (h i : ℂ)) sy = (y : Space G) :=
        congrArg Subtype.val (coreMultiplier_cancel h hh y)
      have hS : (inverseEnergy (G := G) h hh).adjoint = inverseEnergy h hh :=
        inverseEnergy_selfAdjoint h hh
      change inner ℂ (energyExtension h M x) (y : Space G) -
        inner ℂ (x : Space G) (energyExtension h M y) =
        inner ℂ (inverseEnergy h hh (energyExtension h K x)) (y : Space G)
      rw [← hS,ContinuousLinearMap.adjoint_inner_left,
        energyExtension_core h hh M hM x,energyExtension_core h hh M hM y,
        energyExtension_core h hh K hK x,inverseEnergy_core]
      simpa only [hcx,hcy] using hk sx sy
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (E x-E.adjoint x) y = inner ℂ (F x) y
  rw [inner_sub_left,ContinuousLinearMap.adjoint_inner_left]
  exact hp x y

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

theorem resolvent_preserves_regularizer_range (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (S E F : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hg : ∀ x, (S x,E x) ∈ T.graph) (hdef : E-E.adjoint = S.comp F)
    (z : ℂ) (hz : 1 ≤ |z.im|) (hF : ‖F‖ < |z.im|) (y : H) :
    ∃ u : H, resolvent T hs z hz (S y) = S u := by
  obtain ⟨u,hu⟩ := boundedPerturbation_shift_surjective T hs F z hz hF y
  have hgu : ((u : H),T u) ∈ T.adjoint.graph := by
    rw [show T.adjoint = T from hs]
    exact T.mem_graph_iff.mpr ⟨u,rfl,rfl⟩
  have ha := regularizer_adjoint hs.dense_domain S E hS hg hgu
  have he : E u = S (T u)+S (F u) := by
    have he := congrArg (fun Q : H →L[ℂ] H => Q u) hdef
    change E u-E.adjoint u = S (F u) at he
    rw [ha] at he
    exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  obtain ⟨v,hv,hvT⟩ := T.mem_graph_iff.mp (hg u)
  dsimp only [Prod.fst,Prod.snd] at hv hvT
  have hvshift : T v-z•(v : H) = S y := by
    rw [hvT,hv,he,← hu,map_add,map_sub,map_smul]
    abel
  refine ⟨u,?_⟩
  have hr := resolvent_shift T hs z hz v
  rw [hvshift] at hr
  exact hr.trans hv

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 
def BoundedGraphCore (T : H →ₗ.[ℂ] H) (S E : H →L[ℂ] H) : Prop :=
  (LinearMap.range (S.prod E).toLinearMap).topologicalClosure = T.graph

theorem graph_of_parametrized_adjoint {T : H →ₗ.[ℂ] H} (hs : IsSelfAdjoint T)
    (S E : H →L[ℂ] H) (hc : BoundedGraphCore T S E) {x y : H}
    (hxy : ∀ v, inner ℂ (E v) x = inner ℂ (S v) y) : (x,y) ∈ T.graph := by
  rw [← show T.adjoint = T from hs,LinearPMap.adjoint_graph_eq_graph_adjoint hs.dense_domain]
  apply (Submodule.mem_adjoint_iff _ _).mpr
  intro a b hab
  have hclosed : IsClosed {p : H × H | inner ℂ p.2 x = inner ℂ p.1 y} :=
    isClosed_eq (continuous_snd.inner continuous_const) (continuous_fst.inner continuous_const)
  have hin : (LinearMap.range (S.prod E).toLinearMap : Set (H × H)) ⊆
      {p | inner ℂ p.2 x = inner ℂ p.1 y} := by
    rintro p ⟨v,rfl⟩
    exact hxy v
  have he := closure_minimal hin hclosed
  rw [← hc] at hab
  exact sub_eq_zero.mpr (he hab)

omit [CompleteSpace H] in
theorem formalAdjoint_graph_pairing {T : H →ₗ.[ℂ] H} (hs : T.IsFormalAdjoint T)
    {x y a b : H} (hxy : (x,y) ∈ T.graph) (hab : (a,b) ∈ T.graph) :
    inner ℂ y a = inner ℂ x b := by
  obtain ⟨u,hu,hTu⟩ := T.mem_graph_iff.mp hxy
  obtain ⟨v,hv,hTv⟩ := T.mem_graph_iff.mp hab
  dsimp only [Prod.fst,Prod.snd] at hu hv hTu hTv
  rw [← hu,← hv,← hTu,← hTv]
  exact hs u v

 

theorem resolvent_graph_invariant (A B : H →ₗ.[ℂ] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (S E F : H →L[ℂ] H)
    (hgA : ∀ x, (S x,E x) ∈ A.graph) (hgB : ∀ x, (S x,F x) ∈ B.graph)
    (hcA : BoundedGraphCore A S E) (hcB : BoundedGraphCore B S F)
    (hw : ∀ x y, inner ℂ (E x) (F y) = inner ℂ (F x) (E y))
    (z : ℂ) (hz : 1 ≤ |z.im|)
    (hr : ∀ x, ∃ u, resolvent A hA z hz (S x) = S u) :
    ∀ x y, (x,y) ∈ B.graph →
      (resolvent A hA z hz x,resolvent A hA z hz y) ∈ B.graph := by
  let R := resolvent A hA z hz
  have hcore : ∀ x, (R (S x),R (F x)) ∈ B.graph := by
    intro x
    obtain ⟨u,hu⟩ := hr x
    have heu : E u = S x+z•S u := by
      simpa only [hu] using A.mem_graph_snd_inj (hgA u) (resolvent_graph A hA z hz (S x)) hu.symm
    have hh : (F u,F x+z•F u) ∈ A.graph := by
      apply graph_of_parametrized_adjoint hA S E hcA
      intro v
      rw [hw v u,heu,inner_add_right,inner_smul_right,
        formalAdjoint_graph_pairing (selfAdjoint_formal hB) (hgB v) (hgB x),
        formalAdjoint_graph_pairing (selfAdjoint_formal hB) (hgB v) (hgB u)]
      rw [inner_add_right,inner_smul_right]
    obtain ⟨a,ha,hTa⟩ := A.mem_graph_iff.mp hh
    dsimp only [Prod.fst,Prod.snd] at ha hTa
    have hRa := resolvent_shift A hA z hz a
    rw [hTa,ha,add_sub_cancel_right] at hRa
    change R (F x) = F u at hRa
    change (R (S x),R (F x)) ∈ B.graph
    rw [show R (S x) = S u from hu,hRa]
    exact hgB u
  have hclosed : IsClosed {p : H × H | (R p.1,R p.2) ∈ B.graph} :=
    hB.isClosed.preimage ((R.continuous.comp continuous_fst).prodMk (R.continuous.comp continuous_snd))
  have hin : (LinearMap.range (S.prod F).toLinearMap : Set (H × H)) ⊆
      {p | (R p.1,R p.2) ∈ B.graph} := by
    rintro p ⟨x,rfl⟩
    exact hcore x
  intro x y hxy
  rw [← hcB] at hxy
  exact closure_minimal hin hclosed hxy

 

theorem graph_invariant_of_commutes_resolvent (T : H →ₗ.[ℂ] H) (hs : IsSelfAdjoint T)
    (z : ℂ) (hz : 1 ≤ |z.im|) (Q : H →L[ℂ] H)
    (hq : Q * resolvent T hs z hz = resolvent T hs z hz * Q) :
    ∀ x y, (x,y) ∈ T.graph → (Q x,Q y) ∈ T.graph := by
  intro x y hxy
  obtain ⟨u,hu,hTu⟩ := T.mem_graph_iff.mp hxy
  dsimp only [Prod.fst,Prod.snd] at hu hTu
  have hr := resolvent_shift T hs z hz u
  rw [hu,hTu] at hr
  have hqr : resolvent T hs z hz (Q (y-z•x)) = Q x := by
    rw [← show Q (resolvent T hs z hz (y-z•x)) = resolvent T hs z hz (Q (y-z•x)) from
      congrArg (fun L : H →L[ℂ] H => L (y-z•x)) hq,hr]
  have hg := resolvent_graph T hs z hz (Q (y-z•x))
  rwa [hqr,map_sub,map_smul,sub_add_cancel] at hg

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

theorem inverseEnergy_coreWeighted (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (x : finiteCore (G := G)) :
    inverseEnergy h hh (coreDiagonal (fun i => (h i : ℂ)) x) = (x : Space G) := by
  change inverseEnergy h hh ((coreMultiplier (fun i => (h i : ℂ)) x : finiteCore) : Space G) = _
  rw [inverseEnergy_core,coreMultiplier_inv_cancel h hh]

 

theorem energyExtension_boundedGraphCore (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M : finiteCore (G := G) →ₗ[ℂ] Space G) {C : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hc : (coreOperator M).IsClosable) :
    SymmetricOperator.BoundedGraphCore (coreOperator M).closure (inverseEnergy h hh) (energyExtension h M) := by
  unfold SymmetricOperator.BoundedGraphCore
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal _ ?_ hc.closure_isClosed
    rintro p ⟨x,rfl⟩
    exact energyExtension_inverse_graph h hh M hM hc x
  · rw [← hc.graph_closure_eq_closure_graph]
    apply Submodule.topologicalClosure_mono
    intro p hp
    obtain ⟨x,hx,hMx⟩ := (coreOperator M).mem_graph_iff.mp hp
    refine ⟨coreDiagonal (fun i => (h i : ℂ)) x,?_⟩
    apply Prod.ext
    · change inverseEnergy h hh (coreDiagonal (fun i => (h i : ℂ)) x) = p.1
      exact (inverseEnergy_coreWeighted h hh x).trans hx
    · change energyExtension h M (coreDiagonal (fun i => (h i : ℂ)) x) = p.2
      exact (energyExtension_weighted h hh M hM x).trans hMx

theorem energyExtension_weakCommutation (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M N : finiteCore (G := G) →ₗ[ℂ] Space G) {C D : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hN : ∀ x, ‖N x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (x y : Space G) :
    inner ℂ (energyExtension h M x) (energyExtension h N y) =
      inner ℂ (energyExtension h N x) (energyExtension h M y) := by
  have hd : DenseRange ((finiteCore (G := G)).subtype) := by
    simpa [DenseRange] using (finiteCore_dense (G := G))
  refine hd.induction_on₂ ?_ ?_ x y
  · exact isClosed_eq
      (((energyExtension h M).continuous.comp continuous_fst).inner
        ((energyExtension h N).continuous.comp continuous_snd))
      (((energyExtension h N).continuous.comp continuous_fst).inner
        ((energyExtension h M).continuous.comp continuous_snd))
  · intro a b
    change inner ℂ (energyExtension h M (a : Space G)) (energyExtension h N (b : Space G)) =
      inner ℂ (energyExtension h N (a : Space G)) (energyExtension h M (b : Space G))
    rw [energyExtension_core h hh M hM,energyExtension_core h hh N hN,
      energyExtension_core h hh N hN,energyExtension_core h hh M hM]
    exact hw _ _

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SymmetricOperator
open scoped Topology
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 

theorem graph_entries_commute (A B : H →ₗ.[ℂ] H) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (z : ℂ) (hz : 1 ≤ |z.im|)
    (hr : ∀ x y, (x,y) ∈ B.graph →
      (resolvent A hA z hz x,resolvent A hA z hz y) ∈ B.graph)
    (hra : ∀ x y, (x,y) ∈ B.graph →
      ((resolvent A hA z hz).adjoint x,(resolvent A hA z hz).adjoint y) ∈ B.graph)
    (i j k l : Bool) :
    ClosedGraphData.entry A hA.isClosed i j * ClosedGraphData.entry B hB.isClosed k l =
      ClosedGraphData.entry B hB.isClosed k l * ClosedGraphData.entry A hA.isClosed i j := by
  have hR : ∀ k l, resolvent A hA z hz * ClosedGraphData.entry B hB.isClosed k l =
      ClosedGraphData.entry B hB.isClosed k l * resolvent A hA z hz :=
    ClosedGraphData.entry_commutes_of_graph_invariant B hB.isClosed _ hr hra
  have hQ : ∀ k l, ∀ x y, (x,y) ∈ A.graph →
      (ClosedGraphData.entry B hB.isClosed k l x,ClosedGraphData.entry B hB.isClosed k l y) ∈ A.graph := by
    intro k l
    exact graph_invariant_of_commutes_resolvent A hA z hz _ (hR k l).symm
  have hQa : ∀ x y, (x,y) ∈ A.graph →
      ((ClosedGraphData.entry B hB.isClosed k l).adjoint x,
        (ClosedGraphData.entry B hB.isClosed k l).adjoint y) ∈ A.graph := by
    change ∀ x y, (x,y) ∈ A.graph →
      (star (ClosedGraphData.entry B hB.isClosed k l) x,
        star (ClosedGraphData.entry B hB.isClosed k l) y) ∈ A.graph
    rw [ClosedGraphData.star_entry]
    exact hQ l k
  exact (ClosedGraphData.entry_commutes_of_graph_invariant A hA.isClosed _ (hQ k l) hQa i j).symm

end StronglyRationalVOA.SymmetricOperator

namespace StronglyRationalVOA.HilbertScale
open scoped Topology
variable {ι : Type*} {G : ι → Type u} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [DecidableEq ι] [∀ i, CompleteSpace (G i)]

 

theorem coreOperator_strongCommutation (h : ι → ℝ) (hh : ∀ i, 1 ≤ h i)
    (M N K L : finiteCore (G := G) →ₗ[ℂ] Space G) {C D E F : ℝ}
    (hM : ∀ x, ‖M x‖ ≤ C * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hN : ∀ x, ‖N x‖ ≤ D * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hK : ∀ x, ‖K x‖ ≤ E * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hL : ∀ x, ‖L x‖ ≤ F * ‖coreDiagonal (fun i => (h i : ℂ)) x‖)
    (hsM : ∀ x y : finiteCore (G := G), inner ℂ (M x) (y : Space G) = inner ℂ (x : Space G) (M y))
    (hsN : ∀ x y : finiteCore (G := G), inner ℂ (N x) (y : Space G) = inner ℂ (x : Space G) (N y))
    (hkM : ∀ x y, inner ℂ (M x) (coreDiagonal (fun i => (h i : ℂ)) y) -
      inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (M y) = inner ℂ (K x) (y : Space G))
    (hkN : ∀ x y, inner ℂ (N x) (coreDiagonal (fun i => (h i : ℂ)) y) -
      inner ℂ (coreDiagonal (fun i => (h i : ℂ)) x) (N y) = inner ℂ (L x) (y : Space G))
    (hw : ∀ x y, inner ℂ (M x) (N y) = inner ℂ (N x) (M y)) (i j k l : Bool) :
    ClosedGraphData.entry (coreOperator M).closure (coreOperator_closable M hsM).closure_isClosed i j *
      ClosedGraphData.entry (coreOperator N).closure (coreOperator_closable N hsN).closure_isClosed k l =
    ClosedGraphData.entry (coreOperator N).closure (coreOperator_closable N hsN).closure_isClosed k l *
      ClosedGraphData.entry (coreOperator M).closure (coreOperator_closable M hsM).closure_isClosed i j := by
  let A := (coreOperator M).closure
  let B := (coreOperator N).closure
  have hA : IsSelfAdjoint A := coreOperator_essentialSelfAdjoint h hh M K hM hK hsM hkM
  have hB : IsSelfAdjoint B := coreOperator_essentialSelfAdjoint h hh N L hN hL hsN hkN
  let S := inverseEnergy (G := G) h hh
  let EM := energyExtension h M
  let EN := energyExtension h N
  let EK := energyExtension h K
  have hgA : ∀ x, (S x,EM x) ∈ A.graph :=
    energyExtension_inverse_graph h hh M hM (coreOperator_closable M hsM)
  have hgB : ∀ x, (S x,EN x) ∈ B.graph :=
    energyExtension_inverse_graph h hh N hN (coreOperator_closable N hsN)
  have hdef : EM-EM.adjoint = S.comp EK := energyExtension_defect h hh M K hM hK hkM
  have hinv : ∀ z : ℂ, ∀ hz : 1 ≤ |z.im|, ‖EK‖ < |z.im| →
      ∀ x y, (x,y) ∈ B.graph →
        (SymmetricOperator.resolvent A hA z hz x,SymmetricOperator.resolvent A hA z hz y) ∈ B.graph := by
    intro z hz hEK
    apply SymmetricOperator.resolvent_graph_invariant A B hA hB S EM EN hgA hgB
      (energyExtension_boundedGraphCore h hh M hM (coreOperator_closable M hsM))
      (energyExtension_boundedGraphCore h hh N hN (coreOperator_closable N hsN))
      (energyExtension_weakCommutation h hh M N hM hN hw) z hz
    exact SymmetricOperator.resolvent_preserves_regularizer_range A hA S EM EK
      (inverseEnergy_selfAdjoint h hh) hgA hdef z hz hEK
  let z : ℂ := ((‖EK‖+2 : ℝ) : ℂ)*Complex.I
  have hzabs : |z.im| = ‖EK‖+2 := by
    dsimp [z]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_im,
      mul_one,zero_mul,add_zero]
    exact abs_of_nonneg (by positivity)
  have hz : 1 ≤ |z.im| := by rw [hzabs]; linarith [norm_nonneg EK]
  have hzK : ‖EK‖ < |z.im| := by rw [hzabs]; linarith
  apply SymmetricOperator.graph_entries_commute A B hA hB z hz (hinv z hz hzK) ?_ i j k l
  rw [SymmetricOperator.resolvent_adjoint A hA z hz]
  apply hinv
  simpa only [Complex.star_def,Complex.conj_im,abs_neg] using hzK

end StronglyRationalVOA.HilbertScale

namespace StronglyRationalVOA.SmoothCircleFunction
open MeasureTheory
local instance inverseEnergySelfContinuousPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

 
def toContinuousMap (f : SmoothCircleFunction) : C(AddCircle (2*Real.pi),ℂ) :=
  ⟨f.periodic.lift, continuous_coinduced_dom.mpr f.smooth.continuous⟩

@[simp] theorem toContinuousMap_coe (f : SmoothCircleFunction) (t : ℝ) :
    f.toContinuousMap (t : AddCircle (2*Real.pi)) = f t := rfl

@[simp] theorem fourierCoeff_toContinuousMap (f : SmoothCircleFunction) (n : ℤ) :
    fourierCoeff f.toContinuousMap n = f.coefficient n := by
  have hl : (f.toContinuousMap : AddCircle (2*Real.pi) → ℂ) =
      AddCircle.liftIoc (2*Real.pi) 0 f := by
    funext t
    have ht : ((AddCircle.equivIoc (2*Real.pi) 0 t : ℝ) : AddCircle (2*Real.pi)) = t :=
      AddCircle.coe_equivIoc
    rw [← ht,toContinuousMap_coe,AddCircle.liftIoc_coe_apply (AddCircle.equivIoc _ _ t).property]
  rw [hl,fourierCoeff_liftIoc_eq]
  simp only [coefficient,zero_add]

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.FourierAnalysis
open MeasureTheory AddCircle
variable {T : ℝ} [Fact (0 < T)]

 
def coefficientCLM (n : ℤ) : C(AddCircle T,ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => fourierCoeff f n
      map_add' := by
        intro f g
        exact congrFun (fourierCoeff.add
          (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))) n
      map_smul' := by
        intro c f
        exact fourierCoeff.const_smul f c n } 1 (by
      intro f
      change ‖∫ t : AddCircle T, fourier (-n) t • f t ∂haarAddCircle‖ ≤ 1*‖f‖
      have H := norm_integral_le_of_norm_le_const (μ := (haarAddCircle : Measure (AddCircle T)))
        (f := fun t => fourier (-n) t • f t) (C := ‖f‖) (Filter.Eventually.of_forall (by
          intro t
          rw [norm_smul,show ‖fourier (-n) t‖ = 1 from Circle.norm_coe _,one_mul]
          exact f.norm_coe_le_norm t))
      simpa using H)

@[simp] theorem coefficientCLM_apply (n : ℤ) (f : C(AddCircle T,ℂ)) :
    coefficientCLM n f = fourierCoeff f n := rfl

 
theorem coefficient_character_mul (g : C(AddCircle T,ℂ)) (m n : ℤ) :
    fourierCoeff ((fourier m : C(AddCircle T,ℂ))*g) n = fourierCoeff g (n-m) := by
  unfold fourierCoeff
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  change fourier (-n) t * (fourier m t * g t) = fourier (-(n-m)) t * g t
  rw [← mul_assoc,← fourier_add]
  rw [show -n+m = -(n-m) by omega]

 

theorem hasSum_coefficient_product (f g : C(AddCircle T,ℂ))
    (hf : Summable (fourierCoeff f)) (n : ℤ) :
    HasSum (fun m : ℤ => fourierCoeff f m * fourierCoeff g (n-m))
      (fourierCoeff (f*g) n) := by
  have H := (coefficientCLM (T := T) n).hasSum
    ((hasSum_fourier_series_of_summable hf).mul_right g)
  convert H using 1
  · ext m
    change _ = fourierCoeff ((fourierCoeff f m • (fourier m : C(AddCircle T,ℂ)))*g) n
    rw [smul_mul_assoc]
    change _ = fourierCoeff (fourierCoeff f m • (((fourier m : C(AddCircle T,ℂ))*g) : AddCircle T → ℂ)) n
    rw [fourierCoeff.const_smul,smul_eq_mul]
    change _ = fourierCoeff f m * fourierCoeff ((fourier m : C(AddCircle T,ℂ))*g) n
    rw [coefficient_character_mul]
  · rfl

end StronglyRationalVOA.FourierAnalysis

namespace StronglyRationalVOA.SmoothCircleFunction
local instance inverseEnergySelfProductPeriodPos : Fact (0 < 2*Real.pi) := ⟨period_pos⟩

 
def mul (f g : SmoothCircleFunction) : SmoothCircleFunction :=
  ⟨fun t => f t*g t, fun t => by dsimp only; rw [f.periodic,g.periodic], f.smooth.mul g.smooth⟩

@[simp] theorem mul_apply (f g : SmoothCircleFunction) (t : ℝ) : f.mul g t = f t*g t := rfl

@[simp] theorem toContinuousMap_mul (f g : SmoothCircleFunction) :
    (f.mul g).toContinuousMap = f.toContinuousMap*g.toContinuousMap := by
  ext t
  induction t using QuotientAddGroup.induction_on
  rfl

 
theorem coefficient_mul (f g : SmoothCircleFunction) (n : ℤ) :
    HasSum (fun m : ℤ => f.coefficient m*g.coefficient (n-m)) ((f.mul g).coefficient n) := by
  have hs : Summable (fourierCoeff f.toContinuousMap) := by
    rw [show fourierCoeff f.toContinuousMap = f.coefficient from funext f.fourierCoeff_toContinuousMap]
    exact (by simpa using f.rapid_coefficients 0 : Summable (fun m => ‖f.coefficient m‖)).of_norm
  simpa only [fourierCoeff_toContinuousMap,← toContinuousMap_mul] using
    FourierAnalysis.hasSum_coefficient_product f.toContinuousMap g.toContinuousMap hs n

end StronglyRationalVOA.SmoothCircleFunction

namespace StronglyRationalVOA.SmoothCircleFunction
open scoped ContDiff

 
def differentiated (f : SmoothCircleFunction) (k : ℕ) : SmoothCircleFunction where
  toFun := iteratedDeriv k f
  periodic := f.periodic_iteratedDeriv k
  smooth := by
    rw [iteratedDeriv_eq_iterate]
    exact f.smooth.iterate_deriv k

@[simp] theorem differentiated_apply (f : SmoothCircleFunction) (k : ℕ) (t : ℝ) :
    f.differentiated k t = iteratedDeriv k f t := rfl

 

theorem coefficient_deriv_zero (f : SmoothCircleFunction) :
    (f.differentiated 1).coefficient 0 = 0 := by
  rw [coefficient,fourierCoeffOn_eq_integral]
  have H : (∫ t in (0 : ℝ)..2*Real.pi, iteratedDeriv 1 f t) = 0 := by
    rw [iteratedDeriv_one]
    have hd : Differentiable ℝ (f : ℝ → ℂ) := by
      simpa only [iteratedDeriv_zero] using f.differentiable_iteratedDeriv 0
    rw [intervalIntegral.integral_deriv_eq_sub
      (fun x _ => hd x)
      (by simpa only [iteratedDeriv_one] using
        (f.continuous_iteratedDeriv 1).intervalIntegrable 0 (2*Real.pi))]
    have h := f.periodic 0
    simpa only [zero_add,sub_eq_zero] using h
  simp only [neg_zero,fourier_zero,one_smul,differentiated_apply,H,smul_zero]
end StronglyRationalVOA.SmoothCircleFunction

end

end OAI
