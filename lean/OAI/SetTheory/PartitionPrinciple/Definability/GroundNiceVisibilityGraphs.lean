import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameGraphs
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMixtureDensityRecovery

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) : ZFSet.{u} :=
  familyCodeGraph b.encode (fun i => (M.niceVisibilityName a s T (K i)).val)

theorem mem_niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceVisibilityGraph a s b T K ↔
      ∃ i, z = ZFSet.pair (b.encode i) (M.niceVisibilityName a s T (K i)).val := by
  rw [niceVisibilityGraph, mem_familyCodeGraph]
  exact exists_congr (fun _ => eq_comm)

theorem pair_mem_niceVisibilityGraph (T : ZFSet.{u}) (K : I → Subgroup G) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode i) z ∈ M.niceVisibilityGraph a s b T K ↔
      z = (M.niceVisibilityName a s T (K i)).val :=
  pair_mem_familyCodeGraph _ _ b.injective i z

theorem niceVisibilityGraph_function (T : ZFSet.{u}) (K : I → Subgroup G) :
    FunctionGraphOn b.carrier (M.niceVisibilityGraph a s b T K) := by
  have equal : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  simpa only [niceVisibilityGraph, equal] using familyCodeGraph_function b.encode
    (fun i => (M.niceVisibilityName a s T (K i)).val) b.injective

theorem niceVisibilityGraph_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (indices : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    M.niceVisibilityGraph a s b T K ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB := M.groundRelations_mem pairing unions powers separation hT carrier
  have hone := M.transitive carrier (s.encode_mem ⊤)
  let slots : Fin 6 → Fin 7 := ![1, 0, 2, 3, 4, 5]
  let chosen (env : Fin 7 → ZFSet.{u}) :=
    ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z (fun j => env (slots j.succ))))
      (env (slots 0))
  let selected := (M.definable_separation separation nameSupportFormula).reindex slots
  let inner (j : Fin 2) (env : Fin 7 → ZFSet.{u}) : ZFSet.{u} :=
    Fin.cases (chosen env) (Fin.cases (env 6) (fun k => Fin.elim0 k)) j
  let defined : GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      ZFSet.prod (chosen env) {env 6}) := by
    apply (M.definable_familySetCode pairing unions powers separation).comp (g := inner)
    intro j
    exact Fin.cases selected (Fin.cases (GroundDefinableFunction.projection M 6)
      (fun k => Fin.elim0 k)) j
  let params := extend B (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t)
      (extend (s.encode ⊤) Fin.elim0)))))
  have ground := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (Fin.cases hone (fun j => Fin.elim0 j))))))) indices
  have value (i : I) : ZFSet.prod (chosen (extend (b.encode i) params)) {(extend (b.encode i) params) 6} =
      (M.niceVisibilityName a s T (K i)).val := by
    rw [M.niceVisibilityName_code]
    apply congrArg (fun X => ZFSet.prod X {s.encode ⊤})
    have args : (fun j : Fin 5 => (extend (b.encode i) params) (slots j.succ)) =
        extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k))))) j
    change ZFSet.sep _ _ = _
    rw [args]
    exact (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
      carrier group supports maps valid i (M.transitive indices (b.encode_mem i))).symm
  have equal : defined.graph params b.carrier = M.niceVisibilityGraph a s b T K := by
    apply ZFSet.ext
    intro z
    rw [defined.mem_graph, M.mem_niceVisibilityGraph]
    constructor
    · rintro ⟨x, hx, eq⟩
      obtain ⟨i, rfl⟩ := (b.mem_carrier x).1 hx
      exact ⟨i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i))⟩
    · rintro ⟨i, eq⟩
      exact ⟨b.encode i, b.encode_mem i, eq.trans (congrArg (ZFSet.pair (b.encode i)) (value i).symm)⟩
  exact equal ▸ ground

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
