import OAI.SetTheory.PartitionPrinciple.Geometry.GroundExternalGenerators
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentProjections
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableFunctionClosure

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {R : Type u} (c : Presentation R) (Q B : ZFSet.{u})
variable (shape : Q ⊆ ZFSet.prod c.carrier B)
local notation "s" => SetMembers.presentation Q

noncomputable def flatCarrierRow : SetMembers Q → R :=
  (s).decodeFunction c (rowAssignmentRows Q c.carrier B) (rowAssignmentRows_function shape)

noncomputable def flatCarrierData : SetMembers Q → SetMembers B :=
  (s).decodeFunction (SetMembers.presentation B) (rowAssignmentData Q c.carrier B) (rowAssignmentData_function shape)

theorem flatCarrier_coordinates (p : SetMembers Q) :
    SetMembers.raw p = ZFSet.pair (c.encode (flatCarrierRow c Q B shape p))
      (SetMembers.raw (flatCarrierData c Q B shape p)) := by
  have rowEdge := (s).decodeFunction_mem c (rowAssignmentRows Q c.carrier B) (rowAssignmentRows_function shape) p
  have dataEdge := (s).decodeFunction_mem (SetMembers.presentation B)
    (rowAssignmentData Q c.carrier B) (rowAssignmentData_function shape) p
  change ZFSet.pair (SetMembers.raw p) (c.encode (flatCarrierRow c Q B shape p)) ∈ _ at rowEdge
  change ZFSet.pair (SetMembers.raw p) (SetMembers.raw (flatCarrierData c Q B shape p)) ∈ _ at dataEdge
  obtain ⟨row, _hr, A, _hA, code⟩ := ZFSet.mem_prod.1 (shape (SetMembers.raw_mem p))
  rw [code, rowAssignmentRows_entry] at rowEdge
  rw [code, rowAssignmentData_entry] at dataEdge
  rw [rowEdge.2.2.2, dataEdge.2.2.2]
  exact code

theorem flatCarrier_coordinateGraphs :
    (s).graph c (flatCarrierRow c Q B shape) = rowAssignmentRows Q c.carrier B ∧
    (s).graph (SetMembers.presentation B) (flatCarrierData c Q B shape) = rowAssignmentData Q c.carrier B :=
  ⟨(s).graph_decodeFunction c _ _, (s).graph_decodeFunction (SetMembers.presentation B) _ _⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem flatCarrierSequence_projections_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hQ : Q ∈ M.sets) (hRows : c.carrier ∈ M.sets) (hB : B ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (seq : Nat → SetMembers Q)
    (whole : groundSequenceGraph seq ∈ M.sets) :
    natPresentation.graph c (fun n => flatCarrierRow c Q B shape (seq n.down)) ∈ M.sets ∧
      groundSequenceGraph (fun n => flatCarrierData c Q B shape (seq n)) ∈ M.sets := by
  obtain ⟨rowEq, dataEq⟩ := flatCarrier_coordinateGraphs c Q B shape
  have rowGround := M.rowAssignmentRows_mem pairing unions powers separation hQ hRows hB
  have dataGround := M.rowAssignmentData_mem pairing unions powers separation hQ hRows hB
  rw [← rowEq] at rowGround
  rw [← dataEq] at dataGround
  have first := M.relationCompose_mem pairing unions powers separation omega hQ hRows whole rowGround
  have second := M.relationCompose_mem pairing unions powers separation omega hQ hB whole dataGround
  have firstEq := natPresentation.relationCompose_graph (s) c (fun n => seq n.down) (flatCarrierRow c Q B shape)
  have secondEq := natPresentation.relationCompose_graph (s) (SetMembers.presentation B)
    (fun n => seq n.down) (flatCarrierData c Q B shape)
  change relationCompose ZFSet.omega Q c.carrier (groundSequenceGraph seq) ((s).graph c _) = _ at firstEq
  change relationCompose ZFSet.omega Q B (groundSequenceGraph seq) ((s).graph (SetMembers.presentation B) _) = _ at secondEq
  rw [firstEq] at first
  rw [secondEq] at second
  exact ⟨first, second⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
