import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLayerSourceCongruence
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixFieldFamilies

namespace OAI

section

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem prior_raw_witness_rank_lt (i : I) {s t Qs rs μs : ZFSet.{u}}
    (cutoff : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff)
    (before : t = s ∨ t ∈ s)
    (spaces : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 0 ↔
      ZFSet.pair a y ∈ Qs)
    (orders : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 1 ↔
      ZFSet.pair a y ∈ rs)
    (meets : ∀ a ∈ t, ∀ y, ZFSet.pair a y ∈ (run.linked i).serial.fields.graph 2 ↔
      ZFSet.pair a y ∈ μs)
    {o : Ordinal.{u}} (rank : ZFSet.rank run.code < o) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode Qs rs μs
      ((run.diagram.stage i).history.space s) ((run.diagram.stage i).history.order s)
      ((run.diagram.stage i).history.meetGraph s) ((run.diagram.stage i).history.birth s)
      t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have hs : s ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
    simpa only [run.linked_main, ZFSet.mem_insert_iff] using cutoff
  have ht : t ∈ insert (run.linked i).main.cutoff (run.linked i).main.cutoff := by
    rcases before with rfl | earlier
    · exact hs
    · exact (run.linked i).serial.ordinal.1 s hs t earlier
  have raw := (run.linked i).serial.layer_code s hs t ht before _
    ((run.linked i).serial.layerWitness_entry hs ht before)
  have values (j : Fin 5) : (run.linked i).serial.fields.value j s =
      (run.diagram.stage i).history.fieldValue j s := by
    exact ((run.linked i).agreement j s hs).trans
      (congrArg (fun stage : GroundChronologicalMainStage M C D rD =>
        stage.history.fieldValue j s) (run.linked_main i))
  rw [values 0, values 1, values 2, values 3] at raw
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code)))
        (0 : Fin 1).succ.succ)
  have serialRank : ZFSet.rank (run.linked i).serial.code < o :=
    serialBound.trans_lt ((run.linkedCode_rank_lt_code i).trans rank)
  exact ⟨(run.linked i).serial.layerWitness s t, (run.linked i).serial.layerWitness_ground s t,
    raw.congr_source_entries spaces orders meets,
    ((run.linked i).serial.layerWitness_rank_lt_code hs ht before).trans serialRank⟩

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
