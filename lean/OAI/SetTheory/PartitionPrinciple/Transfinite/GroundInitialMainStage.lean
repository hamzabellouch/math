import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteSeedBounds
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialMainAlgebra
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTwoPointHeights
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundTwoStageMainDiagram

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}

noncomputable def initialBirth (stage : GroundMainStage M C D rD) : ZFSet.{u} :=
  constantFamilyGraph stage.carrier ∅

theorem initialBirth_function (stage : GroundMainStage M C D rD) :
    ZFSet.IsFunc stage.carrier (insert (∅ : ZFSet.{u}) ∅) stage.initialBirth :=
  constantFamilyGraph_function stage.carrier ∅

theorem initialBirth_entry (stage : GroundMainStage M C D rD) (x t : ZFSet.{u}) :
    ZFSet.pair x t ∈ stage.initialBirth ↔ x ∈ stage.carrier ∧ t = ∅ :=
  pair_mem_constantFamilyGraph stage.carrier ∅ x t

theorem initialBirth_ground (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    stage.initialBirth ∈ M.sets :=
  M.constantFamilyGraph_mem pairing unions powers separation stage.carrier_ground
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)

theorem initialBirth_old_meet (stage : GroundMainStage M C D rD) :
    OldMeetCode stage.order stage.meetGraph stage.initialBirth := by
  intro x y z a b c _ bornX earlier
  have equal := ((stage.initialBirth_entry x b).1 bornX).2
  exact False.elim (ZFSet.notMem_empty a (equal ▸ earlier))

noncomputable def initialHistory (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    GroundChronologicalHistory M (insert (∅ : ZFSet.{u}) ∅) C D rD where
  space := fun _ => stage.carrier
  order := fun _ => stage.order
  meetGraph := fun _ => stage.meetGraph
  birth := fun _ => stage.initialBirth
  height := fun _ => stage.height
  space_mem := fun _ _ => stage.carrier_ground
  order_mem := fun _ _ => stage.order_ground
  meet_mem := fun _ _ => stage.meet_ground
  birth_mem := fun _ _ => stage.initialBirth_ground pairing unions powers separation
  height_mem := fun _ _ => stage.height_ground
  meet_order := fun _ _ => stage.meet
  birth_function := fun _ _ => stage.initialBirth_function
  birth_bound := by
    intro s hs x _ t entry
    have zero : s = ∅ := by simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty,
      or_false] using hs
    exact Or.inl (((stage.initialBirth_entry x t).1 entry).2.trans zero.symm)
  old_meet := fun _ _ => stage.initialBirth_old_meet
  strict_height := fun _ _ => stage.height_code
  layer := fun _ _ _ _ _ =>
    .countablePoints stage.carrier stage.carrier_ground small (fun _ hx _ => hx)

noncomputable def initialChronological (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    GroundChronologicalMainStage M C D rD where
  stage := stage
  cutoff := ∅
  cutoff_ground := M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩
  cutoff_ordinal := ordinalSetProperty_empty
  history := stage.initialHistory pairing unions powers separation small
  carrier_eq := rfl
  order_eq := rfl
  meet_eq := rfl
  height_eq := rfl

noncomputable def initialChronologyField (stage : GroundMainStage M C D rD) : Fin 5 → ZFSet.{u} :=
  Fin.cases stage.carrier (Fin.cases stage.order (Fin.cases stage.meetGraph
    (Fin.cases stage.initialBirth (Fin.cases stage.height Fin.elim0))))

noncomputable def initialChronologyGraph (stage : GroundMainStage M C D rD)
    (j : Fin 5) : ZFSet.{u} :=
  constantFamilyGraph (insert (∅ : ZFSet.{u}) ∅) (stage.initialChronologyField j)

theorem initialChronologyGraph_entry (stage : GroundMainStage M C D rD)
    (j : Fin 5) (t x : ZFSet.{u}) :
    ZFSet.pair t x ∈ stage.initialChronologyGraph j ↔
      t = ∅ ∧ x = stage.initialChronologyField j := by
  simp only [initialChronologyGraph, pair_mem_constantFamilyGraph,
    ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false]

theorem initialChronologyGraphs_ground (stage : GroundMainStage M C D rD)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (j : Fin 5) : stage.initialChronologyGraph j ∈ M.sets ∧
      ZFSet.IsFunc (insert (∅ : ZFSet.{u}) ∅) {stage.initialChronologyField j}
        (stage.initialChronologyGraph j) := by
  have zero := M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩
  have field : stage.initialChronologyField j ∈ M.sets :=
    Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
      (Fin.cases (stage.initialBirth_ground pairing unions powers separation)
        (Fin.cases stage.height_ground (fun i => Fin.elim0 i))))) j
  exact ⟨M.constantFamilyGraph_mem pairing unions powers separation
    (M.insert_mem pairing unions zero zero) field, constantFamilyGraph_function _ _⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)

noncomputable def initialChronologyBound : ZFSet.{u} :=
  ZFSet.range stage.initialChronologyField

theorem mem_initialChronologyBound (x : ZFSet.{u}) :
    x ∈ stage.initialChronologyBound ↔ ∃ j : Fin 5, stage.initialChronologyField j = x :=
  ZFSet.mem_range

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialChronologyBound_ground : stage.initialChronologyBound ∈ M.sets := by
  apply M.finite_range_mem pairing unions ⟨stage.carrier, stage.carrier_ground⟩
  exact Fin.cases stage.carrier_ground (Fin.cases stage.order_ground (Fin.cases stage.meet_ground
    (Fin.cases (stage.initialBirth_ground pairing unions powers separation)
      (Fin.cases stage.height_ground (fun i => Fin.elim0 i)))))

noncomputable def initialGroundChronologyFields :
    GroundChronologyFields M (insert (∅ : ZFSet.{u}) ∅) where
  time_ground := M.insert_mem pairing unions
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)
    (M.empty_mem ⟨stage.carrier, stage.carrier_ground⟩)
  bound := stage.initialChronologyBound
  bound_ground := stage.initialChronologyBound_ground pairing unions powers separation
  graph := stage.initialChronologyGraph
  graph_ground := fun j => (stage.initialChronologyGraphs_ground pairing unions powers separation j).1
  function := by
    intro j
    have actual := (stage.initialChronologyGraphs_ground pairing unions powers separation j).2
    refine ⟨?_, actual.2⟩
    intro z hz
    obtain ⟨s, hs, x, hx, rfl⟩ := ZFSet.mem_prod.1 (actual.1 hz)
    have equal : x = stage.initialChronologyField j := ZFSet.mem_singleton.1 hx
    exact ZFSet.pair_mem_prod.2 ⟨hs,
      (stage.mem_initialChronologyBound x).2 ⟨j, equal.symm⟩⟩

theorem initialGroundChronologyFields_graph :
    (stage.initialGroundChronologyFields pairing unions powers separation).graph =
      stage.initialChronologyGraph := rfl

theorem initialGroundChronologyFields_value (j : Fin 5) {s : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) :
    (stage.initialGroundChronologyFields pairing unions powers separation).value j s =
      stage.initialChronologyField j := by
  apply (stage.initialGroundChronologyFields pairing unions powers separation).value_eq_of_entry j
  apply (stage.initialChronologyGraph_entry j s (stage.initialChronologyField j)).2
  exact ⟨by simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using hs, rfl⟩

theorem initialGroundChronologyFields_values :
    let fields := stage.initialGroundChronologyFields pairing unions powers separation
    fields.value 0 ∅ = stage.carrier ∧ fields.value 1 ∅ = stage.order ∧
      fields.value 2 ∅ = stage.meetGraph ∧ fields.value 3 ∅ = stage.initialBirth ∧
      fields.value 4 ∅ = stage.height := by
  exact ⟨stage.initialGroundChronologyFields_value pairing unions powers separation 0 (ZFSet.mem_insert _ _),
    stage.initialGroundChronologyFields_value pairing unions powers separation 1 (ZFSet.mem_insert _ _),
    stage.initialGroundChronologyFields_value pairing unions powers separation 2 (ZFSet.mem_insert _ _),
    stage.initialGroundChronologyFields_value pairing unions powers separation 3 (ZFSet.mem_insert _ _),
    stage.initialGroundChronologyFields_value pairing unions powers separation 4 (ZFSet.mem_insert _ _)⟩

theorem initialGroundChronologyFields_code_ground :
    (stage.initialGroundChronologyFields pairing unions powers separation).code ∈ M.sets :=
  (stage.initialGroundChronologyFields pairing unions powers separation).code_ground pairing

end GroundMainStage

section
open SetFormula
universe u

theorem InitialMainAlgebra.carrier_eq_pair :
    (InitialMainAlgebra.carrier : ZFSet.{u}) =
      {InitialMainAlgebra.bottom, InitialMainAlgebra.top} := by
  apply ZFSet.ext
  intro x
  rw [InitialMainAlgebra.mem_carrier, ZFSet.mem_pair]

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {C D rD c d0 d1 : ZFSet.{u}}
variable (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
variable (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) (gap : ZFSet.pair d0 d1 ∈ rD)

noncomputable def initialMainStage : GroundMainStage M C D rD := by
  have ground := M.initialMainAlgebra_ground pairing unions separation infinite
  have hP := ground.1
  have hG := ground.2.1
  have hr := ground.2.2.1
  have hMeet := ground.2.2.2.1
  have hm := ground.2.2.2.2.1
  have hInv := ground.2.2.2.2.2.1
  have hA := ground.2.2.2.2.2.2
  have hBottom := M.transitive hP InitialMainAlgebra.bottom_mem
  have hTop := M.transitive hP InitialMainAlgebra.top_mem
  have height := M.twoPointHeight_mem pairing hBottom hTop (M.transitive hC hc)
    (M.transitive hD h0) (M.transitive hD h1)
  have strict : StrictLexHeightCode InitialMainAlgebra.carrier C D InitialMainAlgebra.order
      (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top c d0 d1) rD := by
    rw [InitialMainAlgebra.carrier_eq_pair]
    exact twoPointHeight_strict InitialMainAlgebra.bottom_ne_top hc h0 h1 gap
  have small : M.groundEmbeddable
      (relationImage InitialMainAlgebra.carrier (ZFSet.prod C D)
        (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top c d0 d1)) ZFSet.omega := by
    rw [InitialMainAlgebra.carrier_eq_pair]
    exact M.twoPointHeight_range_countable pairing unions powers separation infinite hC hD hc h0 h1
  exact GroundMainStage.ofCodes pairing unions powers separation hP hG hr hMeet hA hm hInv
    hC hD hrD height InitialMainAlgebra.meet_code InitialMainAlgebra.group_code
    InitialMainAlgebra.action_code InitialMainAlgebra.bottom_mem InitialMainAlgebra.least
    InitialMainAlgebra.top_mem InitialMainAlgebra.greatest strict small

noncomputable def initialMainChronological : GroundChronologicalMainStage M C D rD :=
  (M.initialMainStage pairing unions powers separation infinite hC hD hrD hc h0 h1 gap).initialChronological
    pairing unions powers separation (M.natSetCode_countable pairing unions powers separation infinite 2)

theorem initialMainStage_fields :
    let stage := M.initialMainStage pairing unions powers separation infinite hC hD hrD hc h0 h1 gap
    stage.carrier = natSetCode 2 ∧ stage.actors = natSetCode 1 ∧
      stage.order = InitialMainAlgebra.order ∧ stage.meetGraph = InitialMainAlgebra.meetGraph ∧
      stage.height = twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top c d0 d1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem initialMainChronological_fields :
    let stage := M.initialMainChronological pairing unions powers separation infinite hC hD hrD hc h0 h1 gap
    stage.stage.carrier = natSetCode 2 ∧ stage.stage.actors = natSetCode 1 ∧
      stage.cutoff = ∅ ∧ stage.birth = constantFamilyGraph (natSetCode 2) ∅ :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem initialMainStage_two_points :
    let stage := M.initialMainStage pairing unions powers separation infinite hC hD hrD hc h0 h1 gap
    stage.bottom ≠ stage.top ∧ ∀ x ∈ stage.carrier, x = stage.bottom ∨ x = stage.top :=
  ⟨InitialMainAlgebra.bottom_ne_top, fun x hx => (InitialMainAlgebra.mem_carrier x).1 hx⟩

end TransitiveGround

end

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem initialChronologyCore :
    ChronologyCoreCode (insert (∅ : ZFSet.{u}) ∅) stage.initialChronologyBound C D rD
      stage.initialChronologyGraph := by
  refine ⟨(stage.initialGroundChronologyFields pairing unions powers separation).function, ?_⟩
  intro s hs L r μ birth height eL er eμ eb eh
  have zero : s = ∅ := by
    simpa only [ZFSet.mem_insert_iff, ZFSet.notMem_empty, or_false] using hs
  have lEq : L = stage.carrier := ((stage.initialChronologyGraph_entry 0 s L).1 eL).2
  have rEq : r = stage.order := ((stage.initialChronologyGraph_entry 1 s r).1 er).2
  have mEq : μ = stage.meetGraph := ((stage.initialChronologyGraph_entry 2 s μ).1 eμ).2
  have bEq : birth = stage.initialBirth := ((stage.initialChronologyGraph_entry 3 s birth).1 eb).2
  have hEq : height = stage.height := ((stage.initialChronologyGraph_entry 4 s height).1 eh).2
  subst s L r μ birth height
  exact ⟨stage.meet, stage.initialBirth_function,
    fun x _ t entry => Or.inl (((stage.initialBirth_entry x t).1 entry).2),
    stage.initialBirth_old_meet, stage.height_code⟩

noncomputable def initialDecodedChronology
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    GroundChronologicalHistory M (insert (∅ : ZFSet.{u}) ∅) C D rD :=
  (stage.initialGroundChronologyFields pairing unions powers separation).toHistory
    (stage.initialChronologyCore pairing unions powers separation) (by
      intro cutoff hc _ _ _
      refine .countablePoints stage.carrier stage.carrier_ground small ?_
      intro x hx _
      have equal : (stage.initialGroundChronologyFields pairing unions powers separation).value
          0 cutoff = stage.carrier :=
        stage.initialGroundChronologyFields_value pairing unions powers separation 0 hc
      exact equal ▸ hx)

theorem initialDecodedChronology_values
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) {s : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) :
    let history := stage.initialDecodedChronology pairing unions powers separation small
    history.space s = stage.carrier ∧ history.order s = stage.order ∧
      history.meetGraph s = stage.meetGraph ∧ history.birth s = stage.initialBirth ∧
      history.height s = stage.height :=
  ⟨stage.initialGroundChronologyFields_value pairing unions powers separation 0 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 1 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 2 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 3 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 4 hs⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
variable (injected : InjectionCode stage.carrier ZFSet.omega injection)

noncomputable def initialSerializedChronology :
    GroundSerializedChronology M (insert (∅ : ZFSet.{u}) ∅) C D rD where
  fields := stage.initialGroundChronologyFields pairing unions powers separation
  ordinal := ordinalSetProperty_succ ordinalSetProperty_empty
  core := stage.initialChronologyCore pairing unions powers separation
  layerBound := {countableLayerWitness stage.carrier injection}
  layer_bound_ground := by
    have ground := M.countableLayerWitness_mem pairing stage.carrier_ground hInjection
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ground ground
  layers := constantFamilyGraph (chronologyPairs (insert (∅ : ZFSet.{u}) ∅))
    (countableLayerWitness stage.carrier injection)
  layers_ground := M.constantFamilyGraph_mem pairing unions powers separation
    (M.chronologyPairs_mem pairing unions powers separation
      (stage.initialGroundChronologyFields pairing unions powers separation).time_ground)
    (M.countableLayerWitness_mem pairing stage.carrier_ground hInjection)
  layer_function := constantFamilyGraph_function _ _
  layer_code := by
    intro s hs t _ _ z entry
    have equal : z = countableLayerWitness stage.carrier injection :=
      ((pair_mem_constantFamilyGraph _ _ _ _).1 entry).2
    refine Or.inl ⟨stage.carrier, injection, equal, injected, ?_⟩
    intro x hx _
    have carrier : (stage.initialGroundChronologyFields pairing unions powers separation).value
        0 s = stage.carrier :=
      stage.initialGroundChronologyFields_value pairing unions powers separation 0 hs
    exact carrier ▸ hx

theorem initialSerializedChronology_layers :
    (stage.initialSerializedChronology pairing unions powers separation hInjection injected).layers =
      constantFamilyGraph (chronologyPairs (insert (∅ : ZFSet.{u}) ∅))
        (countableLayerWitness stage.carrier injection) := rfl

theorem initialSerializedChronology_layerWitness {s t : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u}))
    (ht : t ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) (earlier : t = s ∨ t ∈ s) :
    (stage.initialSerializedChronology pairing unions powers separation hInjection injected).layerWitness s t =
      countableLayerWitness stage.carrier injection :=
  ((pair_mem_constantFamilyGraph _ _ _ _).1
    ((stage.initialSerializedChronology pairing unions powers separation hInjection injected).layerWitness_entry
      hs ht earlier)).2

theorem initialSerializedChronology_values {s : ZFSet.{u}}
    (hs : s ∈ (insert (∅ : ZFSet.{u}) ∅ : ZFSet.{u})) :
    let history := (stage.initialSerializedChronology pairing unions powers separation hInjection injected).toHistory
    history.space s = stage.carrier ∧ history.order s = stage.order ∧
      history.meetGraph s = stage.meetGraph ∧ history.birth s = stage.initialBirth ∧
      history.height s = stage.height :=
  ⟨stage.initialGroundChronologyFields_value pairing unions powers separation 0 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 1 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 2 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 3 hs,
    stage.initialGroundChronologyFields_value pairing unions powers separation 4 hs⟩

theorem initialSerializedChronology_code_ground :
    (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code ∈ M.sets :=
  (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code_ground pairing

include pairing unions powers separation in
theorem exists_initialSerializedChronology
    (small : M.groundEmbeddable stage.carrier ZFSet.omega) :
    ∃ serial : GroundSerializedChronology M (insert (∅ : ZFSet.{u}) ∅) C D rD,
      serial.code ∈ M.sets ∧ serial.fields.graph = stage.initialChronologyGraph ∧
        serial.toHistory.space ∅ = stage.carrier ∧
        serial.toHistory.order ∅ = stage.order ∧
        serial.toHistory.meetGraph ∅ = stage.meetGraph ∧
        serial.toHistory.birth ∅ = stage.initialBirth ∧
        serial.toHistory.height ∅ = stage.height := by
  obtain ⟨injection, hInjection, injected⟩ := small
  exact ⟨stage.initialSerializedChronology pairing unions powers separation hInjection injected,
    stage.initialSerializedChronology_code_ground pairing unions powers separation hInjection injected,
    rfl, stage.initialSerializedChronology_values pairing unions powers separation hInjection injected
      (ZFSet.mem_insert _ _)⟩

end GroundMainStage

namespace GroundMainStage
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (stage : GroundMainStage M C D rD)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
variable (points : ZFSet.rank stage.carrier < o) (height : ZFSet.rank stage.height < o)
include limit points height

theorem initialChronologyField_rank_lt : ∀ j, ZFSet.rank (stage.initialChronologyField j) < o := by
  have pp := rank_product_lt limit points points
  have order := (ZFSet.rank_mono stage.meet.order.relation).trans_lt pp
  have meet := rank_functionGraph_lt limit stage.meet.operation pp points
  have zero : ZFSet.rank (∅ : ZFSet.{u}) < o := by simpa only [ZFSet.rank_empty] using limit.pos
  have birth := rank_constantFamilyGraph_lt limit points zero
  exact Fin.cases points (Fin.cases order (Fin.cases meet (Fin.cases birth
    (Fin.cases height (fun i => Fin.elim0 i)))))

theorem initialChronologyBound_rank_lt : ZFSet.rank stage.initialChronologyBound < o :=
  rank_finiteRange_lt limit 5 _ (stage.initialChronologyField_rank_lt limit points height)

theorem initialChronologyGraph_rank_lt : ∀ j, ZFSet.rank (stage.initialChronologyGraph j) < o :=
  fun j => rank_constantFamilyGraph_lt limit (rank_natSetCode_lt limit 1)
    (stage.initialChronologyField_rank_lt limit points height j)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {injection : ZFSet.{u}} (hInjection : injection ∈ M.sets)
variable (injected : InjectionCode stage.carrier ZFSet.omega injection)

theorem initialSerializedChronology_code_rank_lt (omega : ZFSet.rank (ZFSet.omega : ZFSet.{u}) < o) :
    ZFSet.rank (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code < o := by
  let serial := stage.initialSerializedChronology pairing unions powers separation hInjection injected
  have time : ZFSet.rank (insert (∅ : ZFSet.{u}) ∅) < o := rank_natSetCode_lt limit 1
  have fieldsCode : ZFSet.rank serial.fields.code < o :=
    rank_nonemptyTupleCode_lt limit 6 _ (Fin.cases time
      (Fin.cases (stage.initialChronologyBound_rank_lt limit points height)
        (stage.initialChronologyGraph_rank_lt limit points height)))
  have injectionRank := rank_functionGraph_lt limit injected.function points omega
  have witness : ZFSet.rank (countableLayerWitness stage.carrier injection) < o :=
    rank_nonemptyTupleCode_lt limit 2 _
      (Fin.cases (rank_natSetCode_lt limit 0) (Fin.cases points (fun _ => injectionRank)))
  have layerBound : ZFSet.rank serial.layerBound < o := rank_singleton_lt limit witness
  have pairs := (ZFSet.rank_mono (chronologyPairs_subset (insert (∅ : ZFSet.{u}) ∅))).trans_lt
    (rank_product_lt limit time time)
  have layers : ZFSet.rank serial.layers < o := rank_constantFamilyGraph_lt limit pairs witness
  exact rank_nonemptyTupleCode_lt limit 2 _ (Fin.cases fieldsCode (Fin.cases layerBound (fun _ => layers)))

omit limit points height in
theorem initialSerializedChronology_code_rank_lt_inaccessible
    (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (points : ZFSet.rank stage.carrier < ZFSet.rank K)
    (height : ZFSet.rank stage.height < ZFSet.rank K) :
    ZFSet.rank (stage.initialSerializedChronology pairing unions powers separation hInjection injected).code <
      ZFSet.rank K :=
  stage.initialSerializedChronology_code_rank_lt
    (conditions.rank_isLimit pairing unions powers separation infinite hK) points height
    pairing unions powers separation hInjection injected (ZFSet.rank_lt_of_mem conditions.2.1)

end GroundMainStage

end PartitionPilot.Forcing

end OAI
