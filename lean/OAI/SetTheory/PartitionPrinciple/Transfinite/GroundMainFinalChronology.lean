import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalSeparatedActors
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitCoverageConstruction

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

noncomputable def finalGeometry (i₀ : I) : GroundMainFinalGeometry M C D rD where
  carrier := run.limitPoints
  order := run.limitOrder
  meetGraph := run.limitMeetGraph
  actors := run.limitActors
  multiplication := run.limitMultiplication
  inverse := run.limitInverse
  identity := run.limitIdentity i₀
  action := run.limitAction
  bottom := run.limitBottom i₀
  height := run.limitHeight
  birth := run.limitBirth
  times := run.cutoffLimit
  carrier_ground := run.limitPoints_ground
  order_ground := run.limitOrder_ground
  meet_ground := run.limitMeetGraph_ground
  actors_ground := run.limitActors_ground
  multiplication_ground := run.limitMultiplication_ground
  inverse_ground := run.limitInverse_ground
  action_ground := run.limitAction_ground
  height_ground := run.limitHeight_ground
  birth_ground := run.limitBirth_ground
  times_ground := run.cutoffLimit_ground
  columns_ground := (run.diagram.stage i₀).stage.columns_ground
  coordinates_ground := (run.diagram.stage i₀).stage.coordinates_ground
  coordinate_order_ground := (run.diagram.stage i₀).stage.coordinate_order_ground
  meet := run.limitMeet_code
  group_code := run.limitGroup_code i₀
  action_code := run.limitAction_code i₀
  bottom_mem := run.limitBottom_mem i₀
  least := run.limitBottom_least i₀
  height_code := run.limitHeight_code
  birth_function := run.limitBirth_function
  times_ordinal := run.cutoffLimit_ordinal
  old_meet := run.limit_old_meet

end PartitionPilot.Forcing.GroundMainPrefix



namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]

structure FinalChronology
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (level : GroundMainCandidateLevel M K) where
  serial : GroundSerializedChronology M (insert run.cutoffLimit run.cutoffLimit) C D rD
  code_rank : ZFSet.rank serial.code < ZFSet.rank K
  candidate : serial.code ∈ level.validChronologies C D rD
  graphs : serial.fields.graph = run.limitChronologyFields.graph
  values : ∀ j s, serial.fields.value j s = run.limitChronologyFields.value j s
  attained_layer_bound : serial.layerBound = functionGraphRange
    (chronologyPairs (insert run.cutoffLimit run.cutoffLimit)) serial.layers

variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_finalChronology
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (indices : GroundBelow M run.indices K) (rank : ZFSet.rank run.code < ZFSet.rank K)
    (level : GroundMainCandidateLevel M K) : Nonempty (run.FinalChronology level) := by
  obtain ⟨serial, _, codeRank, candidate, graphs, values, attained⟩ :=
    run.exists_limitSerialization collection infinite choice hK standard indices rank level
  exact ⟨⟨serial, codeRank, candidate, graphs, values, attained⟩⟩

namespace FinalChronology
variable {run} {level : GroundMainCandidateLevel M K}
variable (chronology : run.FinalChronology level)

theorem code_ground : chronology.serial.code ∈ M.sets := chronology.serial.code_ground pairing

theorem history_values (s : ZFSet.{u}) :
    chronology.serial.toHistory.space s = run.limitChronologyFields.value 0 s ∧
    chronology.serial.toHistory.order s = run.limitChronologyFields.value 1 s ∧
    chronology.serial.toHistory.meetGraph s = run.limitChronologyFields.value 2 s ∧
    chronology.serial.toHistory.birth s = run.limitChronologyFields.value 3 s ∧
    chronology.serial.toHistory.height s = run.limitChronologyFields.value 4 s :=
  ⟨chronology.values 0 s, chronology.values 1 s, chronology.values 2 s,
    chronology.values 3 s, chronology.values 4 s⟩

theorem terminal_values (i₀ : I) :
    chronology.serial.toHistory.space run.cutoffLimit = (run.finalGeometry i₀).carrier ∧
    chronology.serial.toHistory.order run.cutoffLimit = (run.finalGeometry i₀).order ∧
    chronology.serial.toHistory.meetGraph run.cutoffLimit = (run.finalGeometry i₀).meetGraph ∧
    chronology.serial.toHistory.birth run.cutoffLimit = (run.finalGeometry i₀).birth ∧
    chronology.serial.toHistory.height run.cutoffLimit = (run.finalGeometry i₀).height := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values run.cutoffLimit
  exact ⟨space.trans (run.limitChronologyFields_terminal 0),
    order.trans (run.limitChronologyFields_terminal 1), meet.trans (run.limitChronologyFields_terminal 2),
    birth.trans (run.limitChronologyFields_terminal 3), height.trans (run.limitChronologyFields_terminal 4)⟩

theorem earlier_values (i : I) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) :
    chronology.serial.toHistory.space s = (run.diagram.stage i).history.space s ∧
    chronology.serial.toHistory.order s = (run.diagram.stage i).history.order s ∧
    chronology.serial.toHistory.meetGraph s = (run.diagram.stage i).history.meetGraph s ∧
    chronology.serial.toHistory.birth s = (run.diagram.stage i).history.birth s ∧
    chronology.serial.toHistory.height s = (run.diagram.stage i).history.height s := by
  obtain ⟨space, order, meet, birth, height⟩ := chronology.history_values s
  exact ⟨space.trans (run.limitChronologyFields_values i 0 before),
    order.trans (run.limitChronologyFields_values i 1 before),
    meet.trans (run.limitChronologyFields_values i 2 before),
    birth.trans (run.limitChronologyFields_values i 3 before),
    height.trans (run.limitChronologyFields_values i 4 before)⟩

theorem earlier_entries (i : I) (j : Fin 5) {s : ZFSet.{u}}
    (before : s = (run.diagram.stage i).cutoff ∨ s ∈ (run.diagram.stage i).cutoff) (y : ZFSet.{u}) :
    ZFSet.pair s y ∈ chronology.serial.fields.graph j ↔
      ZFSet.pair s y ∈ (run.linked i).serial.fields.graph j := by
  rw [chronology.graphs]
  exact run.limitChronologyFields_source_entries i j before y

end FinalChronology

end PartitionPilot.Forcing.GroundMainPrefix

end

end OAI
