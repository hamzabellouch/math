import OAI.SetTheory.PartitionPrinciple.Definability.GroundDefinableRelationProducts

namespace OAI



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawNiceNameCandidates (i T P G basis maps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets nameSupportFormula
    (extend z (extend i (extend P (extend G (extend basis (extend maps Fin.elim0)))))))
      (M.groundRelations T P)

noncomputable def rawNiceNameCandidateGraph (nodes T P G basis maps : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun i : nodes => i.val)
    (fun i => M.rawNiceNameCandidates i.val T P G basis maps)

noncomputable def rawNiceVisibilityGraph (nodes T P G basis maps top : ZFSet.{u}) : ZFSet.{u} :=
  familyCodeGraph (fun i : nodes => i.val)
    (fun i => ZFSet.prod (M.rawNiceNameCandidates i.val T P G basis maps) {top})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawNiceNameCandidates :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawNiceNameCandidates (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let bound := GroundSetTerm.app (M.definable_groundRelations pairing unions powers separation) ![v 1, v 2]
  let term := GroundSetTerm.app (M.definable_separation separation nameSupportFormula)
    ![bound, v 0, v 2, v 3, v 4, v 5]
  refine term.definition.congr ?_
  intro env
  apply congrArg (fun params : Fin 5 → ZFSet.{u} =>
    ZFSet.sep (fun z => Realize M.sets nameSupportFormula (extend z params))
      (M.groundRelations (env 1) (env 2)))
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
    (Fin.cases rfl (fun k => Fin.elim0 k))))) j

variable (collection : CollectionSchema M.sets)

noncomputable def definable_rawNiceNameCandidateGraph :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawNiceNameCandidateGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) :=
  (M.definable_rawNiceNameCandidates pairing unions powers separation).definable_graph
    pairing separation collection

noncomputable def definable_rawNiceVisibilityGraph :
    GroundDefinableFunction M (fun env : Fin 7 → ZFSet.{u} =>
      M.rawNiceVisibilityGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5) (env 6)) := by
  let v := GroundSetTerm.var M (n := 7)
  let chosen := GroundSetTerm.app (M.definable_rawNiceNameCandidates pairing unions powers separation)
    ![v 0, v 1, v 2, v 3, v 4, v 5]
  let name := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![chosen, v 6]
  exact name.definition.definable_graph pairing separation collection

variable {I H Q : Type u} [Group H] [PartialOrder Q]
variable (a : PosetAction H Q) (s : Presentation Q) (t : Presentation H) (b : Presentation I)
variable (K : I → Subgroup H)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
include pairing unions powers separation collection carrier group supports maps valid

theorem rawNiceNameCandidates_eq (i : I) (hi : b.encode i ∈ M.sets) :
    M.rawNiceNameCandidates (b.encode i) T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) = M.niceNameCandidates a s T (K i) :=
  (M.niceNameCandidates_eq_selection a s t b K pairing unions powers separation collection
    carrier group supports maps valid i hi).symm

theorem rawNiceNameCandidateGraph_eq (nodes : b.carrier ∈ M.sets) :
    M.rawNiceNameCandidateGraph b.carrier T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) = M.niceNameCandidateGraph a s b T K := by
  apply ZFSet.ext
  intro z
  rw [rawNiceNameCandidateGraph, mem_familyCodeGraph, M.mem_niceNameCandidateGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨j, eq⟩ := (b.mem_carrier i.val).1 i.property
    refine ⟨j, ?_⟩
    rw [← eq, M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid j (M.transitive nodes (b.encode_mem j))] at equal
    exact equal.symm
  · rintro ⟨i, equal⟩
    refine ⟨⟨b.encode i, b.encode_mem i⟩, ?_⟩
    change ZFSet.pair (b.encode i) (M.rawNiceNameCandidates _ _ _ _ _ _) = z
    rw [M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid i (M.transitive nodes (b.encode_mem i))]
    exact equal.symm

theorem rawNiceVisibilityGraph_eq [OrderTop Q] (nodes : b.carrier ∈ M.sets) :
    M.rawNiceVisibilityGraph b.carrier T s.carrier t.carrier (supportBasisCode b t K)
      (a.conditionMapFamily s t) (s.encode ⊤) = M.niceVisibilityGraph a s b T K := by
  apply ZFSet.ext
  intro z
  rw [rawNiceVisibilityGraph, mem_familyCodeGraph, M.mem_niceVisibilityGraph]
  constructor
  · rintro ⟨i, equal⟩
    obtain ⟨j, eq⟩ := (b.mem_carrier i.val).1 i.property
    refine ⟨j, ?_⟩
    rw [← eq, M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid j (M.transitive nodes (b.encode_mem j))] at equal
    rw [M.niceVisibilityName_code]
    exact equal.symm
  · rintro ⟨i, equal⟩
    refine ⟨⟨b.encode i, b.encode_mem i⟩, ?_⟩
    change ZFSet.pair (b.encode i) (ZFSet.prod (M.rawNiceNameCandidates _ _ _ _ _ _) _) = z
    rw [M.rawNiceNameCandidates_eq pairing unions powers separation collection a s t b K
      carrier group supports maps valid i (M.transitive nodes (b.encode_mem i))]
    rw [M.niceVisibilityName_code] at equal
    exact equal.symm

end PartitionPilot.Forcing.TransitiveGround

end OAI
