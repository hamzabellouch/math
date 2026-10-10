import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialExternalChronology

namespace OAI

section

namespace PartitionPilot.Forcing.GroundChronologicalExternal
open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable {births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion}
variable {heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion}
variable {prior : GroundChronologicalHistory M T0 C D rD}
variable (external : GroundChronologicalExternal M initial I Sources Reps G m inv one T τ
  P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed T0 completion births heights prior)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (includes : M.sets ⊆ N.sets)
variable (pairingN : Realize N.sets SetFormula.pairing Fin.elim0)
variable (unionsN : Realize N.sets SetFormula.union Fin.elim0)
variable (powersN : Realize N.sets powerSet Fin.elim0) (separationN : SeparationSchema N.sets)
variable (infiniteN : Realize N.sets SetFormula.infinity Fin.elim0)
variable (choiceN : Realize N.sets SetFormula.choice Fin.elim0)
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets)
variable (smallD : M.groundEmbeddable D ZFSet.omega)
variable (irreflexive : ∀ q ∈ D, ZFSet.pair q q ∉ rD)
include external pairing unions includes pairingN unionsN powersN separationN infiniteN choiceN hC hD smallD irreflexive

theorem exists_extension_basis {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (completion.externalPointCarrier P0 r0 μ0 A0)
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ completion.externalPointOrder P0 r0 μ0 A0 := by
  have filterAtLimit : MeetFilterCode (external.history.space births.limit)
      (external.history.order births.limit) (external.history.meetGraph births.limit) F := by
    simpa only [external.limit_values.1, external.limit_values.2.1, external.limit_values.2.2.1] using filter
  have basis := external.history.exists_extension_basis includes pairingN unionsN powersN separationN infiniteN choiceN
    (M.insert_mem pairing unions births.limit_ground births.limit_ground) hC hD
    (ordinalSetProperty_succ births.times.ordinal) smallD irreflexive
    (ZFSet.mem_insert births.limit births.limit) hF filterAtLimit
  simpa only [external.limit_values.2.1] using basis

theorem exists_bounded_extension_basis {F : ZFSet.{u}} (hF : F ∈ N.sets)
    (filter : MeetFilterCode (completion.externalBoundedCarrier P0 r0 μ0 A0)
      (completion.externalBoundedOrder P0 r0 μ0 A0) (completion.externalBoundedMeet P0 r0 μ0 A0) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ completion.externalBoundedOrder P0 r0 μ0 A0 := by
  have filterAtLimit : MeetFilterCode (external.bounded_history.space births.limit)
      (external.bounded_history.order births.limit) (external.bounded_history.meetGraph births.limit) F := by
    simpa only [external.bounded_values.1, external.bounded_values.2.1, external.bounded_values.2.2.1] using filter
  have basis := external.bounded_history.exists_extension_basis includes pairingN unionsN powersN separationN infiniteN choiceN
    (M.insert_mem pairing unions births.limit_ground births.limit_ground) hC hD
    (ordinalSetProperty_succ births.times.ordinal) smallD irreflexive
    (ZFSet.mem_insert births.limit births.limit) hF filterAtLimit
  simpa only [external.bounded_values.2.1] using basis

end PartitionPilot.Forcing.GroundChronologicalExternal

end

end OAI
