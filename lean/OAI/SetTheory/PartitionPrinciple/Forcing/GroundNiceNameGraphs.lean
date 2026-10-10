import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

noncomputable def niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) : ZFSet.{u} :=
  familyCodeGraph b.encode (fun i => M.niceNameCandidates a s T (K i))

theorem mem_niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) (z : ZFSet.{u}) :
    z ∈ M.niceNameCandidateGraph a s b T K ↔
      ∃ i, z = ZFSet.pair (b.encode i) (M.niceNameCandidates a s T (K i)) := by
  rw [niceNameCandidateGraph, mem_familyCodeGraph]
  exact exists_congr (fun _ => eq_comm)

theorem pair_mem_niceNameCandidateGraph (T : ZFSet.{u}) (K : I → Subgroup G) (i : I) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode i) z ∈ M.niceNameCandidateGraph a s b T K ↔
      z = M.niceNameCandidates a s T (K i) :=
  pair_mem_familyCodeGraph _ _ b.injective i z

theorem niceNameCandidateGraph_function (T : ZFSet.{u}) (K : I → Subgroup G) :
    FunctionGraphOn b.carrier (M.niceNameCandidateGraph a s b T K) := by
  have equal : ZFSet.range b.encode = b.carrier := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_range]
    exact (b.mem_carrier z).symm
  simpa only [niceNameCandidateGraph, equal] using familyCodeGraph_function b.encode
    (fun i => M.niceNameCandidates a s T (K i)) b.injective

theorem niceNameCandidates_eq_selection (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
    (i : I) (hi : b.encode i ∈ M.sets) :
    M.niceNameCandidates a s T (K i) =
      ZFSet.sep (fun z => Realize M.sets nameSupportFormula
        (extend z (extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))))))
        (M.groundRelations T s.carrier) := by
  apply ZFSet.ext
  intro z
  rw [niceNameCandidates, ZFSet.mem_sep, ZFSet.mem_sep]
  apply and_congr_right
  intro hz
  have data := (M.mem_groundRelations T s.carrier z).1 hz
  let τ := Name.ofSubset valid data.2
  have fixed := M.realize_nameSupportFormula a s t b K pairing unions powers separation collection
    carrier group supports maps i hi τ data.1
  change NiceNameCode a s T (K i) τ.val ↔ Realize M.sets nameSupportFormula _
  refine Iff.trans ?_ fixed.symm
  constructor
  · rintro ⟨σ, eq, _, h⟩
    have same : σ = τ := Subtype.ext eq
    exact same ▸ h
  · intro h
    exact ⟨τ, rfl, data.2, h⟩

theorem niceNameCandidateGraph_mem (K : I → Subgroup G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (indices : b.carrier ∈ M.sets) (supports : supportBasisCode b t K ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) :
    M.niceNameCandidateGraph a s b T K ∈ M.sets := by
  let B := M.groundRelations T s.carrier
  have hB := M.groundRelations_mem pairing unions powers separation hT carrier
  let slots : Fin 6 → Fin 6 := ![1, 0, 2, 3, 4, 5]
  let defined := (M.definable_separation separation nameSupportFormula).reindex slots
  let params := extend B (extend s.carrier (extend t.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0))))
  have ground := defined.graph_mem pairing separation collection params
    (Fin.cases hB (Fin.cases carrier (Fin.cases group (Fin.cases supports
      (Fin.cases maps (fun j => Fin.elim0 j)))))) indices
  have value (i : I) :
      ZFSet.sep (fun z => Realize M.sets nameSupportFormula
        (extend z (fun j => (extend (b.encode i) params) (slots j.succ))))
          ((extend (b.encode i) params) (slots 0)) = M.niceNameCandidates a s T (K i) := by
    have args : (fun j : Fin 5 => (extend (b.encode i) params) (slots j.succ)) =
        extend (b.encode i) (extend s.carrier (extend t.carrier
          (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) Fin.elim0)))) := by
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (fun k => Fin.elim0 k))))) j
    rw [args]
    exact (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
      carrier group supports maps valid i (M.transitive indices (b.encode_mem i))).symm
  have equal : defined.graph params b.carrier = M.niceNameCandidateGraph a s b T K := by
    apply ZFSet.ext
    intro z
    rw [defined.mem_graph, M.mem_niceNameCandidateGraph]
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
