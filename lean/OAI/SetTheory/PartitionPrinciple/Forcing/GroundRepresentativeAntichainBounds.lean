import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStructuralFullIndexSize

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable {rows I T Q order D X : ZFSet.{u}}

theorem representative_antichain_subset_candidate
    (shape : Q ⊆ M.stageOneCandidateBound rows I T)
    (antichain : OrderAntichainCode Q order D)
    (compatible : ∀ row A C, ZFSet.pair row A ∈ Q → ZFSet.pair row C ∈ Q →
      AssignmentIndexAgreement A C →
      ∃ z ∈ Q, ZFSet.pair z (ZFSet.pair row A) ∈ order ∧
        ZFSet.pair z (ZFSet.pair row C) ∈ order)
    (representatives : ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A) :
    D ⊆ M.stageOneCandidateBound rows X T := by
  intro q member
  obtain ⟨row, hRow, A, hA, subsetA, smallA, rfl⟩ :=
    (M.mem_stageOneCandidateBound rows I T q).1 (shape (antichain.1 member))
  obtain ⟨C, inD, contained, exactLists⟩ := representatives row A member
  have dataC := (M.pair_mem_stageOneCandidateBound rows I T row C).1 (shape (antichain.1 inD))
  have agreement := assignment_representative_agreement subsetA dataC.2.2.1 contained exactLists
  have equal := antichain.eq_of_common_lower inD member
    (compatible row C A (antichain.1 inD) (antichain.1 member) agreement)
  have same : C = A := (ZFSet.pair_inj.1 equal).2
  have subsetC := (assignment_subset_iff_indices_subset dataC.2.2.1).2 contained
  exact (M.pair_mem_stageOneCandidateBound rows X T row A).2
    ⟨hRow, hA, same ▸ subsetC, smallA⟩

theorem representative_antichain_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {K : ZFSet.{u}} (hRows : rows ∈ M.sets) (hX : X ∈ M.sets)
    (hT : T ∈ M.sets) (hK : K ∈ M.sets) (hD : D ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (ordinal : ordinalSetProperty K)
    (strong : GroundStrongLimit M K)
    (smallRows : GroundBelow M rows K) (smallX : GroundBelow M X K)
    (smallT : GroundBelow M T K)
    (shape : Q ⊆ M.stageOneCandidateBound rows I T)
    (antichain : OrderAntichainCode Q order D)
    (compatible : ∀ row A C, ZFSet.pair row A ∈ Q → ZFSet.pair row C ∈ Q →
      AssignmentIndexAgreement A C →
      ∃ z ∈ Q, ZFSet.pair z (ZFSet.pair row A) ∈ order ∧
        ZFSet.pair z (ZFSet.pair row C) ∈ order)
    (representatives : ∀ row A, ZFSet.pair row A ∈ D →
      ∃ C, ZFSet.pair row C ∈ D ∧ assignmentIndices I T C ⊆ X ∧
        assignmentOnIndices (assignmentIndices I T (assignmentOnIndices X T A)) T C =
          assignmentOnIndices X T A) : GroundBelow M D K :=
  (GroundBelow.stageOneCandidateBound pairing unions powers separation hRows hX hT hK omega
    ordinal strong smallRows smallX smallT).restrict separation hD hK
    (M.representative_antichain_subset_candidate shape antichain compatible representatives)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
