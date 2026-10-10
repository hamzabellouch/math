import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLinkedProfilePreservation

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def LinkedProfilePreservingTransitionRawCode (M : TransitiveGround.{u})
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : ZFSet.{u})
    (source target : Fin 24 → ZFSet.{u}) : Prop :=
  LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target ∧
  Families = M.groundPower (source 0) ∧
  OldProfilePreservationCode (source 0) (source 1) (source 2)
    (target 0) (target 1) (target 2) points Families

namespace SetFormula
def linkedProfilePreservingTransitionRawFormula {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : Fin n)
    (source target : Fin 24 → Fin n) : SetFormula n :=
  .conj (linkedMainTransitionRawFormula K Labels C D rD N sourceCode targetCode z points actors
    sourceBirth targetBirth source target)
    (.conj (relativePowerFormula (source 0) Families)
      (BoundedFormula.oldProfilePreservationFormula (source 0) (source 1) (source 2)
        (target 0) (target 1) (target 2) points Families).toFormula)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem realize_linkedProfilePreservingTransitionRawFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : Fin n)
    (source target : Fin 24 → Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionRawFormula K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target) env ↔
    LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD)
      (env N) (env sourceCode) (env targetCode) (env z) (env points) (env actors)
      (env sourceBirth) (env targetBirth) (env Families)
      (fun j => env (source j)) (fun j => env (target j)) :=
  (M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth source target
    env members omega ordinal).and
    ((M.realize_relativePowerFormula (source 0) Families env members).and
      (BoundedFormula.realize_oldProfilePreservationFormula M (source 0) (source 1) (source 2)
        (target 0) (target 1) (target 2) points Families env members))

end TransitiveGround

namespace LinkedProfilePreservingTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth Families : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedProfilePreservingTransitionRawCode M K Labels C D rD N sourceCode targetCode z
      points actors sourceBirth targetBirth Families source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedProfilePreservingTransitionCode M K Labels C D rD sourceCode targetCode z := by
  rw [omega] at raw
  obtain ⟨s, t, sourceEqual, targetEqual, transition, equal, covered⟩ :=
    raw.1.exists_transition pairing unions powers separation sourceGround targetGround
      hPoints hActors hC hD hrD rfl
  have sourceCode := s.rawFields_code
  have targetCode := t.rawFields_code
  rw [sourceEqual] at sourceCode
  rw [targetEqual] at targetCode
  have sourceFields := sourceCode.fields_unique raw.1.1
  have targetFields := targetCode.fields_unique raw.1.2.1
  have mapEqual : ZFSet.pair transition.map.points transition.map.actors = ZFSet.pair points actors :=
    equal.trans raw.1.2.2.2.2.1.1
  have pointsEqual := (ZFSet.pair_inj.1 mapEqual).1
  have preservation := raw.2.2
  rw [raw.2.1, ← sourceFields, ← targetFields] at preservation
  refine ⟨s, t, sourceEqual, targetEqual, transition, equal, covered, ?_⟩
  change OldProfilePreservationCode s.main.stage.carrier s.main.stage.order s.main.stage.meetGraph
    t.main.stage.carrier t.main.stage.order t.main.stage.meetGraph
    transition.map.points (M.groundPower s.main.stage.carrier)
  rw [pointsEqual]
  exact preservation

end LinkedProfilePreservingTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)
theorem profileTransition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (covered : transition.CoversOldBirths) (preserved : transition.PreservesOldProfiles) :
    LinkedProfilePreservingTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields :=
  ⟨source.transition_rawFields target transition covered, rfl, preserved⟩

end GroundLinkedMainStage

end PartitionPilot.Forcing

end

end OAI
