import OAI.SetTheory.PartitionPrinciple.Definability.LinkedMainTransitionRawCodes

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

def LinkedMainTransitionCode (M : TransitiveGround.{u})
    (K Labels C D rD sourceCode targetCode z : ZFSet.{u}) : Prop :=
  ∃ source target : GroundLinkedMainStage M K Labels C D rD,
    source.code = sourceCode ∧ target.code = targetCode ∧
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths

namespace LinkedMainTransitionRawCode
variable {M : TransitiveGround.{u}}
variable {K Labels C D rD N sourceCode targetCode z points actors sourceBirth targetBirth : ZFSet.{u}}
variable {source target : Fin 24 → ZFSet.{u}}

theorem exists_transition
    (raw : LinkedMainTransitionRawCode M K Labels C D rD N sourceCode targetCode z points actors
      sourceBirth targetBirth source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (sourceGround : ∀ j, source j ∈ M.sets) (targetGround : ∀ j, target j ∈ M.sets)
    (hPoints : points ∈ M.sets) (hActors : actors ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (omega : N = ZFSet.omega) :
    LinkedMainTransitionCode M K Labels C D rD sourceCode targetCode z := by
  obtain ⟨s, hs, sf⟩ := raw.1.exists_linked_fields pairing unions powers separation sourceGround hC hD hrD omega
  obtain ⟨t, ht, tf⟩ := raw.2.1.exists_linked_fields pairing unions powers separation targetGround hC hD hrD omega
  obtain ⟨sb, tb, ⟨encoded, ordinary, chronological⟩, coverage⟩ := raw.2.2
  rw [← sf] at sb coverage
  rw [← tf] at tb
  rw [← sf, ← tf] at ordinary chronological
  change ZFSet.pair s.main.cutoff sourceBirth ∈ s.serial.fields.graph 3 at sb
  change ZFSet.pair t.main.cutoff targetBirth ∈ t.serial.fields.graph 3 at tb
  have sourceEq : sourceBirth = s.main.birth :=
    (s.serial.fields.value_eq_of_entry 3 sb).symm.trans s.terminal_values.2.2.2.1
  have targetEq : targetBirth = t.main.birth :=
    (t.serial.fields.value_eq_of_entry 3 tb).symm.trans t.terminal_values.2.2.2.1
  rw [s.rawFields_graphs, t.rawFields_graphs, sourceEq, targetEq] at chronological
  rw [targetEq] at coverage
  let map : GroundMainTransition s.main.stage t.main.stage :=
    GroundMainTransition.ofLaws hPoints hActors ordinary
  let transition := GroundChronologicalMainTransition.ofFieldLaws s.serial.fields t.serial.fields
    s.agreement t.agreement map chronological
  exact ⟨s, t, hs, ht, transition, encoded.symm, coverage⟩

end LinkedMainTransitionRawCode

namespace GroundLinkedMainStage
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable (source target : GroundLinkedMainStage M K Labels C D rD)

theorem transition_rawFields
    (transition : GroundChronologicalMainTransition source.main target.main)
    (coverage : transition.CoversOldBirths) :
    LinkedMainTransitionRawCode M K Labels C D rD ZFSet.omega source.code target.code
      transition.map.code transition.map.points transition.map.actors source.main.birth target.main.birth
      source.rawFields target.rawFields := by
  refine ⟨source.rawFields_code, target.rawFields_code, ?_, ?_, ⟨rfl, transition.map.laws, ?_⟩, coverage⟩
  · change ZFSet.pair source.main.cutoff source.main.birth ∈ source.serial.fields.graph 3
    rw [← source.terminal_values.2.2.2.1]
    exact source.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · change ZFSet.pair target.main.cutoff target.main.birth ∈ target.serial.fields.graph 3
    rw [← target.terminal_values.2.2.2.1]
    exact target.serial.fields.value_entry 3 (ZFSet.mem_insert _ _)
  · rw [source.rawFields_graphs, target.rawFields_graphs]
    exact transition.field_laws source.serial.fields target.serial.fields source.agreement target.agreement

end GroundLinkedMainStage

namespace SetFormula

def linkedMainTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 52
  let fresh := prefixIndex n 52
  exBlock 52 (linkedMainTransitionRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
    (old sourceCode) (old targetCode) (old z) (fresh 48) (fresh 49) (fresh 50) (fresh 51)
    (fun j => fresh (j.castAdd 28)) (fun j => fresh (Fin.natAdd 24 (j.castAdd 4))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 52 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51)
          (fun j => fields (j.castAdd 28)) (fun j => fields (Fin.natAdd 24 (j.castAdd 4))) := by
  rw [linkedMainTransitionFormula, realize_exBlock]
  have actual (fields : Fin 52 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedMainTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 52 K) (suffixIndex n 52 Labels) (suffixIndex n 52 C) (suffixIndex n 52 D)
      (suffixIndex n 52 rD) (suffixIndex n 52 N) (suffixIndex n 52 sourceCode)
      (suffixIndex n 52 targetCode) (suffixIndex n 52 z)
      (prefixIndex n 52 48) (prefixIndex n 52 49) (prefixIndex n 52 50) (prefixIndex n 52 51)
      (fun j => prefixIndex n 52 (j.castAdd 28)) (fun j => prefixIndex n 52 (Fin.natAdd 24 (j.castAdd 4)))
      (extendMany 52 fields env) (extendMany_members 52 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedMainTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedMainTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedMainTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 28)) (fun j => ground (Fin.natAdd 24 (j.castAdd 4)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage⟩
    let extra : Fin 4 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (fun _ => target.main.birth)))
    let fields : Fin 52 → ZFSet.{u} := Fin.addCases (m := 24) (n := 28) source.rawFields (Fin.addCases (m := 24) (n := 4) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (fun _ => target.main.birth_ground)))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 28) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 4) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 28)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 4))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedMainTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      source.main.birth target.main.birth source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.transition_rawFields target transition coverage

end TransitiveGround
end

universe u

namespace GroundChronologicalMainTransition
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source target chosenSource chosenTarget : GroundLinkedMainStage M K Labels C D rD}
def retargetLinked (transition : GroundChronologicalMainTransition source.main target.main)
    (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code) : GroundChronologicalMainTransition chosenSource.main chosenTarget.main := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  let points := transition.map.points
  let actors := transition.map.actors
  have ordinary : MainTransitionLaws source.main.stage.carrier target.main.stage.carrier
      source.main.stage.order target.main.stage.order source.main.stage.meetGraph target.main.stage.meetGraph
      source.main.stage.actors target.main.stage.actors source.main.stage.multiplication target.main.stage.multiplication
      source.main.stage.identity target.main.stage.identity source.main.stage.action target.main.stage.action
      source.main.stage.bottom target.main.stage.bottom source.main.stage.height target.main.stage.height points actors :=
    transition.map.laws
  rw [first.stage, second.stage] at ordinary
  let map : GroundMainTransition chosenSource.main.stage chosenTarget.main.stage :=
    GroundMainTransition.ofLaws transition.map.points_ground transition.map.actors_ground ordinary
  refine { map := map, cutoff_le := ?_, birth := ?_, history_prefix := ?_ }
  · simpa only [first.cutoff, second.cutoff] using transition.cutoff_le
  · intro x y t entry
    rw [← first.birth, ← second.birth]
    exact transition.birth x y t entry
  · intro s before
    have oldBefore : s = source.main.cutoff ∨ s ∈ source.main.cutoff := by
      simpa only [first.cutoff] using before
    have original := transition.history_prefix s oldBefore
    have lower := first.history_five s oldBefore
    have upper := second.history_five s (transition.prefix_bound oldBefore)
    exact ⟨upper.1.symm.trans (original.1.trans lower.1),
      upper.2.1.symm.trans (original.2.1.trans lower.2.1),
      upper.2.2.1.symm.trans (original.2.2.1.trans lower.2.2.1),
      upper.2.2.2.1.symm.trans (original.2.2.2.1.trans lower.2.2.2.1),
      upper.2.2.2.2.symm.trans (original.2.2.2.2.trans lower.2.2.2.2)⟩

variable (transition : GroundChronologicalMainTransition source.main target.main)
variable (sourceCode : source.code = chosenSource.code) (targetCode : target.code = chosenTarget.code)

theorem retargetLinked_points :
    (transition.retargetLinked sourceCode targetCode).map.points = transition.map.points := rfl

theorem retargetLinked_actors :
    (transition.retargetLinked sourceCode targetCode).map.actors = transition.map.actors := rfl

theorem retargetLinked_code :
    (transition.retargetLinked sourceCode targetCode).map.code = transition.map.code := rfl

theorem retargetLinked_coversOldBirths_iff :
    (transition.retargetLinked sourceCode targetCode).CoversOldBirths ↔ transition.CoversOldBirths := by
  have first := source.same_code chosenSource sourceCode
  have second := target.same_code chosenTarget targetCode
  change OldBirthFiberCoverageCode chosenSource.main.stage.carrier transition.map.points
    chosenTarget.main.birth chosenSource.main.cutoff ↔ _
  rw [← first.stage, ← second.birth, ← first.cutoff]
  rfl

theorem retargetLinked_coversOldBirths (coverage : transition.CoversOldBirths) :
    (transition.retargetLinked sourceCode targetCode).CoversOldBirths :=
  (transition.retargetLinked_coversOldBirths_iff sourceCode targetCode).2 coverage

end GroundChronologicalMainTransition

namespace LinkedMainTransitionCode
variable {M : TransitiveGround.{u}} {K Labels C D rD z : ZFSet.{u}}

theorem exists_at (source target : GroundLinkedMainStage M K Labels C D rD)
    (code : LinkedMainTransitionCode M K Labels C D rD source.code target.code z) :
    ∃ transition : GroundChronologicalMainTransition source.main target.main,
      transition.map.code = z ∧ transition.CoversOldBirths := by
  obtain ⟨first, second, sourceCode, targetCode, transition, equal, coverage⟩ := code
  exact ⟨transition.retargetLinked sourceCode targetCode,
    (transition.retargetLinked_code sourceCode targetCode).trans equal,
    transition.retargetLinked_coversOldBirths sourceCode targetCode coverage⟩

end LinkedMainTransitionCode

end PartitionPilot.Forcing

end OAI
