import OAI.SetTheory.PartitionPrinciple.Transfinite.StageTwoAssignmentSplices

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem assignmentCut_mem (separation : SeparationSchema M.sets)
    {levels alpha A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentCut levels alpha A ∈ M.sets := by
  let formula : BoundedFormula 3 := BoundedFormula.exMem 1
    (BoundedFormula.pairMembershipFormula 1 0 3)
  let params := extend alpha (extend levels Fin.elim0)
  have ground := M.bounded_separation_mem separation formula params
    (Fin.cases hAlpha (Fin.cases hLevels (fun i => Fin.elim0 i))) hA
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth formula (extend z params)) A =
      assignmentCut levels alpha A := by
    apply ZFSet.ext
    intro z
    simp only [ZFSet.mem_sep, assignmentCut, formula,
      BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ ground

theorem assignmentUpper_mem (separation : SeparationSchema M.sets)
    {levels alpha A : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentUpper levels alpha A ∈ M.sets := by
  exact M.bounded_separation_mem separation (.neg (.mem 0 1))
    (extend (assignmentCut levels alpha A) Fin.elim0)
    (Fin.cases (M.assignmentCut_mem separation hLevels hAlpha hA) (fun i => Fin.elim0 i)) hA

theorem assignmentSplice_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hAq : Aq ∈ M.sets) (hAp : Ap ∈ M.sets) :
    assignmentSplice levels alpha Aq Ap ∈ M.sets :=
  M.binary_union_mem pairing unions
    (M.assignmentCut_mem separation hLevels hAlpha hAq)
    (M.assignmentUpper_mem separation hLevels hAlpha hAp)

theorem assignmentCut_small (separation : SeparationSchema M.sets)
    {levels alpha A N : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentCut levels alpha A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentCut_mem separation hLevels hAlpha hA) hN
    (assignmentCut_subset levels alpha A) small

theorem assignmentUpper_small (separation : SeparationSchema M.sets)
    {levels alpha A N : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hA : A ∈ M.sets) (hN : N ∈ M.sets) (small : M.groundEmbeddable A N) :
    M.groundEmbeddable (assignmentUpper levels alpha A) N :=
  M.groundEmbeddable_restrict separation
    (M.assignmentUpper_mem separation hLevels hAlpha hA) hN
    (assignmentUpper_subset levels alpha A) small

theorem assignmentSplice_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (hAq : Aq ∈ M.sets) (hAp : Ap ∈ M.sets)
    (smallq : M.groundEmbeddable Aq ZFSet.omega)
    (smallp : M.groundEmbeddable Ap ZFSet.omega) :
    M.groundEmbeddable (assignmentSplice levels alpha Aq Ap) ZFSet.omega :=
  M.groundEmbeddable_restrict separation
    (M.assignmentSplice_mem pairing unions separation hLevels hAlpha hAq hAp)
    (M.omega_mem separation infinite) (assignmentSplice_subset levels alpha Aq Ap)
    (M.groundCountable_binary_union pairing unions powers separation infinite choice
      hAq hAp smallq smallp)

theorem assignmentSplice_mem_groundSmallSubsets
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {J levels alpha Aq Ap : ZFSet.{u}}
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets)
    (memberq : Aq ∈ M.groundSmallSubsets J ZFSet.omega)
    (memberp : Ap ∈ M.groundSmallSubsets J ZFSet.omega) :
    assignmentSplice levels alpha Aq Ap ∈ M.groundSmallSubsets J ZFSet.omega := by
  obtain ⟨hAq, subsetq, smallq⟩ := (M.mem_groundSmallSubsets J ZFSet.omega Aq).1 memberq
  obtain ⟨hAp, subsetp, smallp⟩ := (M.mem_groundSmallSubsets J ZFSet.omega Ap).1 memberp
  refine (M.mem_groundSmallSubsets J ZFSet.omega _).2
    ⟨M.assignmentSplice_mem pairing unions separation hLevels hAlpha hAq hAp, ?_,
      M.assignmentSplice_countable pairing unions powers separation infinite choice
        hLevels hAlpha hAq hAp smallq smallp⟩
  intro z hz
  exact (ZFSet.mem_union.1 (assignmentSplice_subset levels alpha Aq Ap hz)).elim
    (fun member => subsetq member) (fun member => subsetp member)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem assignmentIndexLevels_mem {I T eta levels : ZFSet.{u}}
    (hI : I ∈ M.sets) (hT : T ∈ M.sets) (hEta : eta ∈ M.sets)
    (hLevels : levels ∈ M.sets) : assignmentIndexLevels I T eta levels ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation
    (M.stageOneAssignments_mem pairing unions powers separation hI hT) hI hEta
    (M.productFirst_mem pairing unions powers separation hI
      (M.prod_mem pairing unions powers separation hT hT)) hLevels

theorem stageTwoAssignmentLevels_mem {I0 I1 T : ZFSet.{u}}
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hT : T ∈ M.sets) :
    stageTwoAssignmentLevels I0 I1 T ∈ M.sets := by
  have hz := M.empty_mem ⟨I0, hI0⟩
  have ho : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hz hz
  have hEta := M.unorderedPair_mem pairing hz ho
  have hI := M.binary_union_mem pairing unions hI0 hI1
  exact M.assignmentIndexLevels_mem pairing unions powers separation hI hT hEta
    (M.refinementIndexFieldGraph_mem pairing unions powers separation hI hEta 0)

theorem stageTwoAssignmentCuts_mem {I0 I1 T A : ZFSet.{u}}
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hT : T ∈ M.sets) (hA : A ∈ M.sets) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 0) A ∈ M.sets ∧
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A ∈ M.sets ∧
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 2) A ∈ M.sets := by
  have hz := M.empty_mem ⟨I0, hI0⟩
  have ho : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hz hz
  have ht : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions ho ho
  have graph := M.stageTwoAssignmentLevels_mem pairing unions powers separation hI0 hI1 hT
  exact ⟨M.assignmentCut_mem separation graph hz hA,
    M.assignmentCut_mem separation graph ho hA, M.assignmentCut_mem separation graph ht hA⟩

theorem stageTwoAssignmentCut_one_mem_groundSmallSubsets
    (infinite : Realize M.sets infinity Fin.elim0)
    {I0 I1 T A : ZFSet.{u}}
    (first : RefinementIndexLevelCode I0 ∅)
    (second : RefinementIndexLevelCode I1 (natSetCode 1))
    (hI0 : I0 ∈ M.sets) (hI1 : I1 ∈ M.sets) (hT : T ∈ M.sets)
    (member : A ∈ M.groundSmallSubsets (stageOneAssignments (I0 ∪ I1) T) ZFSet.omega) :
    assignmentCut (stageTwoAssignmentLevels I0 I1 T) (natSetCode 1) A ∈
      M.groundSmallSubsets (stageOneAssignments I0 T) ZFSet.omega := by
  obtain ⟨hA, _, small⟩ := (M.mem_groundSmallSubsets _ _ A).1 member
  have ground := (M.stageTwoAssignmentCuts_mem pairing unions powers separation hI0 hI1 hT hA).2.1
  exact (M.mem_groundSmallSubsets _ _ _).2 ⟨ground,
    stageTwoAssignmentCut_one_subset first second A,
    M.groundEmbeddable_restrict separation ground (M.omega_mem separation infinite)
      (assignmentCut_subset _ _ A) small⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
