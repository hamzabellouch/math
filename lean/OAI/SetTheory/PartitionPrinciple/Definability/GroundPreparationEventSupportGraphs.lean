import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStoredPreparedFamilyActions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace BoundedFormula

private def eventSupportSetFormula {n} (nodes event output : Fin n) : BoundedFormula n :=
  .conj (.allMem output (.mem 0 nodes.succ))
    (.allMem nodes (.conj
      (imp (.mem 0 output.succ) (preparationEventSupportFormula 0 event.succ))
      (imp (preparationEventSupportFormula 0 event.succ) (.mem 0 output.succ))))

private theorem truth_eventSupportSetFormula {n} (nodes event output : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (eventSupportSetFormula nodes event output) env ↔
      env output = preparationEventUsedSupports (env nodes) (env event) := by
  simp only [eventSupportSetFormula, Truth, truth_imp, truth_preparationEventSupportFormula]
  change (env output ⊆ env nodes ∧ ∀ v ∈ env nodes,
    (v ∈ env output → _) ∧ (_ → v ∈ env output)) ↔ _
  constructor
  · rintro ⟨inside, exact⟩
    apply ZFSet.ext
    intro v
    rw [preparationEventUsedSupports, ZFSet.mem_sep]
    exact ⟨fun hv => ⟨inside hv, (exact v (inside hv)).1 hv⟩,
      fun hv => (exact v hv.1).2 hv.2⟩
  · intro equal
    refine ⟨fun _ h => (ZFSet.mem_sep.1 (equal ▸ h)).1, ?_⟩
    intro v hv
    exact ⟨fun h => (ZFSet.mem_sep.1 (equal ▸ h)).2,
      fun h => equal.symm ▸ ZFSet.mem_sep.2 ⟨hv, h⟩⟩

private def eventSupportGraphFormula : BoundedFormula 2 :=
  exPairFields 0 (eventSupportSetFormula 3 1 0)

private theorem truth_eventSupportGraphFormula (entry nodes : ZFSet.{u}) :
    Truth eventSupportGraphFormula ![entry, nodes] ↔
      ∃ event support, entry = ZFSet.pair event support ∧
        support = preparationEventUsedSupports nodes event := by
  simp only [eventSupportGraphFormula, truth_exPairFields, truth_eventSupportSetFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem preparationEventUsedSupports_mem (separation : SeparationSchema M.sets)
    {nodes event : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hEvent : event ∈ M.sets) :
    preparationEventUsedSupports nodes event ∈ M.sets := by
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.preparationEventSupportFormula 0 1) ![event]
    (Fin.cases hEvent (fun j => Fin.elim0 j)) hNodes
  have equal : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.preparationEventSupportFormula 0 1) (extend v ![event])) nodes =
        preparationEventUsedSupports nodes event := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, BoundedFormula.truth_preparationEventSupportFormula,
      preparationEventUsedSupports, ZFSet.mem_sep]
    rfl
  exact equal ▸ ground

noncomputable def preparationEventSupportGraph (nodes E : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ event support, z = ZFSet.pair event support ∧
    support = preparationEventUsedSupports nodes event) (ZFSet.prod E (M.groundPower nodes))

theorem pair_mem_preparationEventSupportGraph (nodes E event support : ZFSet.{u}) :
    ZFSet.pair event support ∈ M.preparationEventSupportGraph nodes E ↔
      event ∈ E ∧ support ∈ M.groundPower nodes ∧
        support = preparationEventUsedSupports nodes event := by
  rw [preparationEventSupportGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨he, hs⟩, event', support', equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨he, hs, value⟩
  · rintro ⟨he, hs, value⟩
    exact ⟨⟨he, hs⟩, event, support, rfl, value⟩

theorem preparationEventSupportGraph_function (separation : SeparationSchema M.sets)
    {nodes E : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets) :
    ZFSet.IsFunc E (M.groundPower nodes) (M.preparationEventSupportGraph nodes E) := by
  refine ⟨fun _ h => (ZFSet.mem_sep.1 h).1, ?_⟩
  intro event he
  have hs := (M.mem_groundPower nodes _).2
    ⟨M.preparationEventUsedSupports_mem separation hNodes (M.transitive hE he),
      fun _ h => (ZFSet.mem_sep.1 h).1⟩
  refine ⟨preparationEventUsedSupports nodes event,
    (M.pair_mem_preparationEventSupportGraph nodes E event _).2 ⟨he, hs, rfl⟩, ?_⟩
  intro support entry
  exact (M.pair_mem_preparationEventSupportGraph nodes E event support).1 entry |>.2.2

theorem preparationEventSupportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes E : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets) :
    M.preparationEventSupportGraph nodes E ∈ M.sets := by
  have ground := M.bounded_separation_mem separation BoundedFormula.eventSupportGraphFormula
    ![nodes] (Fin.cases hNodes (fun j => Fin.elim0 j))
    (M.prod_mem pairing unions powers separation hE (M.groundPower_mem powers hNodes))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.eventSupportGraphFormula
      (extend z ![nodes])) (ZFSet.prod E (M.groundPower nodes)) =
        M.preparationEventSupportGraph nodes E := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, preparationEventSupportGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_eventSupportGraphFormula z nodes)
  exact equal ▸ ground

noncomputable def preparationUsedSupportSequence (nodes E events : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose ZFSet.omega E (M.groundPower nodes) events (M.preparationEventSupportGraph nodes E)

theorem preparationUsedSupportSequence_ground_function
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes E events : ZFSet.{u}} (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (omega : ZFSet.omega ∈ M.sets) (whole : events ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) :
    M.preparationUsedSupportSequence nodes E events ∈ M.sets ∧
      ZFSet.IsFunc ZFSet.omega (M.groundPower nodes)
        (M.preparationUsedSupportSequence nodes E events) :=
  ⟨M.relationCompose_mem pairing unions powers separation omega hE
    (M.groundPower_mem powers hNodes) whole
    (M.preparationEventSupportGraph_mem pairing unions powers separation hNodes hE),
    relationCompose_function_of_subset function
      (M.preparationEventSupportGraph_function separation hNodes hE) (fun _ h => h)⟩

theorem pair_mem_preparationUsedSupportSequence
    (separation : SeparationSchema M.sets) {nodes E events : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hE : E ∈ M.sets)
    (function : ZFSet.IsFunc ZFSet.omega E events) (i support : ZFSet.{u}) :
    ZFSet.pair i support ∈ M.preparationUsedSupportSequence nodes E events ↔
      ∃ event, ZFSet.pair i event ∈ events ∧ support = preparationEventUsedSupports nodes event := by
  rw [preparationUsedSupportSequence, pair_mem_relationCompose]
  constructor
  · rintro ⟨_, _, event, _, edge, value⟩
    exact ⟨event, edge, (M.pair_mem_preparationEventSupportGraph nodes E event support).1 value |>.2.2⟩
  · rintro ⟨event, edge, rfl⟩
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    have hs := (M.mem_groundPower nodes _).2
      ⟨M.preparationEventUsedSupports_mem separation hNodes (M.transitive hE bounds.2),
        fun _ h => (ZFSet.mem_sep.1 h).1⟩
    exact ⟨bounds.1, hs, event, bounds.2, edge,
      (M.pair_mem_preparationEventSupportGraph nodes E event _).2 ⟨bounds.2, hs, rfl⟩⟩

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
