import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainBoundTaskOutput
import OAI.SetTheory.PartitionPrinciple.Transfinite.LinkedSuccessorOutputFieldEquality

namespace OAI



namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {source : GroundLinkedMainStage M K Labels C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source.main Labels)

theorem exists_taskBearingLinkedTarget
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (hLabels : Labels ∈ M.sets)
    (serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD)
    (agreement : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      serial.fields.value j s = certificate.target.history.fieldValue j s)
    (invariant : certificate.target.Invariant K Labels)
    (rank : ZFSet.rank serial.code < ZFSet.rank K) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      target.main = certificate.target ∧
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source.code target.code
        certificate.transition.map.code := by
  let target : GroundLinkedMainStage M K Labels C D rD :=
    ⟨certificate.target, serial, agreement, invariant, rank⟩
  let extra : Fin 8 → ZFSet.{u} :=
    fun j => certificate.successorOutputValues (Fin.natAdd 21 (j.castAdd 1))
  let maps : Fin 4 → ZFSet.{u} := Fin.cases certificate.transition.map.points
    (Fin.cases certificate.transition.map.actors
      (Fin.cases source.main.birth (fun _ => certificate.target.birth)))
  let fields : Fin 60 → ZFSet.{u} :=
    Fin.addCases (m := 24) (n := 36) source.rawFields
      (Fin.addCases (m := 24) (n := 12) target.rawFields
        (Fin.addCases (m := 4) (n := 8) maps extra))
  have extraGround : ∀ j, extra j ∈ M.sets := fun j =>
    certificate.successorOutputValues_ground pairing unions powers separation infinite hLabels _
  have mapsGround : ∀ j, maps j ∈ M.sets :=
    Fin.cases certificate.transition.map.points_ground
      (Fin.cases certificate.transition.map.actors_ground
        (Fin.cases source.main.birth_ground (fun _ => certificate.target.birth_ground)))
  have ground : ∀ j, fields j ∈ M.sets := by
    intro j
    refine Fin.addCases (m := 24) (n := 36) ?_ ?_ j
    · intro a
      simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing a
    · intro a
      refine Fin.addCases (m := 24) (n := 12) ?_ ?_ a
      · intro b
        simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing b
      · intro b
        refine Fin.addCases (m := 4) (n := 8) ?_ ?_ b
        · intro c
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using mapsGround c
        · intro c
          simpa only [fields, Fin.addCases_right] using extraGround c
  have sourceFields : (fun j : Fin 24 => fields (j.castAdd 36)) = source.rawFields := by
    funext j
    simp only [fields, Fin.addCases_left]
  have targetFields : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 12))) = target.rawFields := by
    funext j
    simp only [fields, Fin.addCases_right, Fin.addCases_left]
  have taskFields : (fun j : Fin 8 => fields (Fin.natAdd 52 j)) = extra := by
    funext j
    have index : Fin.natAdd 52 j = Fin.natAdd 24 (Fin.natAdd 24 (Fin.natAdd 4 j)) := by
      apply Fin.ext
      change 52 + j.val = 24 + (24 + (4 + j.val))
      simp only [← Nat.add_assoc]
    rw [index]
    simp only [fields, Fin.addCases_right]
  have outputs : linkedSuccessorOutputFields source.rawFields target.rawFields
      certificate.transition.map.points certificate.transition.map.actors extra =
      certificate.successorOutputValues := by
    obtain ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := source.rawFields_stage_projections
    obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10⟩ := target.rawFields_stage_projections
    obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12, o13, o14, o15, o16, o17, o18, o19, o20, o21, o22, o23, o24, o25, o26, o27, o28, o29⟩ :=
      certificate.successorOutputValues_projections
    apply linkedSuccessorOutputFields_eq
    exact ⟨
      s0.trans o0.symm, t0.trans o1.symm, s1.trans o2.symm, t1.trans o3.symm,
      s2.trans o4.symm, t2.trans o5.symm, s3.trans o6.symm, t3.trans o7.symm,
      s4.trans o8.symm, t4.trans o9.symm, s6.trans o10.symm, t6.trans o11.symm,
      s7.trans o12.symm, t7.trans o13.symm, s8.trans o14.symm, t8.trans o15.symm,
      s10.trans o16.symm, t10.trans o17.symm, o18.symm, o19.symm,
      s9.trans o20.symm, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl,
      rfl, t9.trans o29.symm⟩
  refine ⟨target, rfl, fields, ground, ?_⟩
  rw [sourceFields, targetFields, taskFields]
  change TaskBearingMainSuccessorRawCode M K Labels C D rD ZFSet.omega source.code target.code
    certificate.transition.map.code certificate.transition.map.points certificate.transition.map.actors
    source.main.birth certificate.target.birth source.rawFields target.rawFields extra
  refine ⟨source.transition_rawFields target certificate.transition certificate.coversOldBirths,
    certificate.cutoff_strict, ?_⟩
  rw [outputs]
  exact certificate.boundSuccessorOutput pairing unions powers separation infinite hLabels

end PartitionPilot.Forcing.GroundInitialMainSuccessorData

end OAI
