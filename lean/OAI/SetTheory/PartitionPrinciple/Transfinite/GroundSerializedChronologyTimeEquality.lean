import OAI.SetTheory.PartitionPrinciple.Definability.BoundedChronologyCodes
import OAI.SetTheory.PartitionPrinciple.Definability.BoundedMeetOrderCodes
import OAI.SetTheory.PartitionPrinciple.Definability.StrictLexHeightFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.TaggedGrowthLayerFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionPrefixGraphs

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internal_chronological_coinitiality
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {L F T C Q r μ birth height qlt : ZFSet.{u}}
    (hF : F ∈ M.sets) (hT : T ∈ M.sets) (hr : r ∈ M.sets) (hBirth : birth ∈ M.sets)
    (hC : C ∈ M.sets) (hQ : Q ∈ M.sets) (hHeight : height ∈ M.sets)
    (meet : MeetOrderCode L r μ) (filter : MeetFilterCode L r μ F)
    (born : ZFSet.IsFunc L T birth) (ordinal : ordinalSetProperty T)
    (oldMeet : OldMeetCode r μ birth)
    (strictHeight : StrictLexHeightCode L C Q r height qlt)
    (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    (localBases : ∀ t ∈ essentialBirthIndices F T r birth,
      M.InternalCountableBelow r F (relationFiber (birthEssentialSet F T r birth)
        (relationConverse (birthEssentialSet F T r birth) (essentialBirthIndices F T r birth) birth) t)) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets,
      InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
        ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ r := by
  have descent := essentialHeightDescent_of_chronological_laws meet filter born oldMeet strictHeight
  have small := M.essentialBirthIndices_countable pairing unions powers separation infinite choice
    hF hT hr hBirth hC hQ hHeight filter.subset ordinal strictHeight.function smallQ irreflexive descent
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    M.internal_countable_basis_of_birth_layers pairing unions powers separation infinite choice
      hF hT hr hBirth meet.order filter.subset born small localBases
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure ChronologyPointCode (T C D rD s L r μ birth height : ZFSet.{u}) : Prop where
  meet : MeetOrderCode L r μ
  birth_function : ZFSet.IsFunc L T birth
  birth_bound : ∀ x ∈ L, ∀ t, ZFSet.pair x t ∈ birth → t = s ∨ t ∈ s
  old_meet : OldMeetCode r μ birth
  strict_height : StrictLexHeightCode L C D r height rD

namespace BoundedFormula

def chronologyPointFormula {n} (T C D rD s L r μ birth height : Fin n) : BoundedFormula n :=
  .conj (meetOrderFormula L r μ) (.conj (functionFormula L T birth)
    (.conj (birthBoundFormula L T birth s) (.conj (oldMeetFormula L T r μ birth)
      (strictLexHeightFormula L C D r height rD))))

theorem truth_chronologyPointFormula {n} (T C D rD s L r μ birth height : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyPointFormula T C D rD s L r μ birth height) env ↔
      ChronologyPointCode (env T) (env C) (env D) (env rD) (env s)
        (env L) (env r) (env μ) (env birth) (env height) := by
  simp only [chronologyPointFormula, Truth, truth_meetOrderFormula,
    truth_functionFormula, truth_strictLexHeightFormula]
  constructor
  · rintro ⟨meet, function, bound, old, strict⟩
    exact ⟨meet, function, (truth_birthBoundFormula L T birth s env function).1 bound,
      (truth_oldMeetFormula L T r μ birth env function).1 old, strict⟩
  · intro code
    exact ⟨code.meet, code.birth_function,
      (truth_birthBoundFormula L T birth s env code.birth_function).2 code.birth_bound,
      (truth_oldMeetFormula L T r μ birth env code.birth_function).2 code.old_meet,
      code.strict_height⟩

theorem realize_chronologyPointFormula (M : TransitiveGround.{u}) {n}
    (T C D rD s L r μ birth height : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyPointFormula T C D rD s L r μ birth height).toFormula env ↔
      ChronologyPointCode (env T) (env C) (env D) (env rD) (env s)
        (env L) (env r) (env μ) (env birth) (env height) :=
  (realize_toFormula M _ env members).trans
    (truth_chronologyPointFormula T C D rD s L r μ birth height env)

end BoundedFormula





structure GroundChronologicalHistory (M : TransitiveGround.{u}) (T C Q qlt : ZFSet.{u}) where
  space : ZFSet.{u} → ZFSet.{u}
  order : ZFSet.{u} → ZFSet.{u}
  meetGraph : ZFSet.{u} → ZFSet.{u}
  birth : ZFSet.{u} → ZFSet.{u}
  height : ZFSet.{u} → ZFSet.{u}
  space_mem : ∀ s ∈ T, space s ∈ M.sets
  order_mem : ∀ s ∈ T, order s ∈ M.sets
  meet_mem : ∀ s ∈ T, meetGraph s ∈ M.sets
  birth_mem : ∀ s ∈ T, birth s ∈ M.sets
  height_mem : ∀ s ∈ T, height s ∈ M.sets
  meet_order : ∀ s ∈ T, MeetOrderCode (space s) (order s) (meetGraph s)
  birth_function : ∀ s ∈ T, ZFSet.IsFunc (space s) T (birth s)
  birth_bound : ∀ s ∈ T, ∀ x ∈ space s, ∀ t,
    ZFSet.pair x t ∈ birth s → t = s ∨ t ∈ s
  old_meet : ∀ s ∈ T, OldMeetCode (order s) (meetGraph s) (birth s)
  strict_height : ∀ s ∈ T, StrictLexHeightCode (space s) C Q (order s) (height s) qlt
  layer : ∀ cutoff ∈ T, ∀ t ∈ T, t = cutoff ∨ t ∈ cutoff →
    CodedGrowthLayer M space order meetGraph (space cutoff) (order cutoff)
      (meetGraph cutoff) (birth cutoff) t

namespace GroundChronologicalHistory

variable {M : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

theorem all_filters_internal_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt) :
    ∀ cutoff ∈ T, ∀ F ∈ M.sets,
      MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F →
        M.InternalCountableBelow (history.order cutoff) F F := by
  intro cutoff
  induction cutoff using ZFSet.inductionOn with
  | h cutoff ih =>
    intro hc F hF filter
    have localBases : ∀ t ∈ essentialBirthIndices F T (history.order cutoff) (history.birth cutoff),
        M.InternalCountableBelow (history.order cutoff) F
          (essentialBirthFiber F T (history.order cutoff) (history.birth cutoff) t) := by
      intro t ht
      obtain ⟨htT, x, hx, xt⟩ :=
        (mem_essentialBirthIndices F T (history.order cutoff) (history.birth cutoff) t).1 ht
      have bounded := history.birth_bound cutoff hc x
        (filter.subset (birthEssentialSet_subset F T (history.order cutoff) (history.birth cutoff) hx)) t xt
      apply (history.layer cutoff hc t htT bounded).internal_countable_essentials
        pairing unions powers separation infinite choice (history.space_mem cutoff hc)
        (history.order_mem cutoff hc) (history.birth_mem cutoff hc) hF hT (M.transitive hT htT)
        (history.meet_order cutoff hc) filter (history.birth_function cutoff hc)
      intro s hs
      have hsT : s ∈ T := ordinal.1 t htT s hs
      have before : s ∈ cutoff := bounded.elim
        (fun equal => equal ▸ hs) (fun earlier => ordinal.2 cutoff hc t earlier s hs)
      exact ⟨history.space_mem s hsT, history.meet_order s hsT, ih s before hsT⟩
    obtain ⟨B, hB, f, hf, injection, positive, below⟩ :=
      M.internal_chronological_coinitiality pairing unions powers separation infinite choice
        hF hT (history.order_mem cutoff hc) (history.birth_mem cutoff hc)
        hC hQ (history.height_mem cutoff hc) (history.meet_order cutoff hc) filter
        (history.birth_function cutoff hc) ordinal (history.old_meet cutoff hc)
        (history.strict_height cutoff hc) smallQ irreflexive localBases
    exact ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩

theorem exists_internal_basis
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ M.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ M.sets, ∃ f ∈ M.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff := by
  obtain ⟨B, hB, ⟨f, hf, injection⟩, positive, below⟩ :=
    history.all_filters_internal_countable pairing unions powers separation infinite choice
      hT hC hQ ordinal smallQ irreflexive cutoff hc F hF filter
  exact ⟨B, hB, f, hf, injection, positive, below⟩

end GroundChronologicalHistory





structure ChronologyCoreCode (T V C D rD : ZFSet.{u})
    (graphs : Fin 5 → ZFSet.{u}) : Prop where
  function : ∀ j, ZFSet.IsFunc T V (graphs j)
  point : ∀ s ∈ T, ∀ L r μ birth height,
    ZFSet.pair s L ∈ graphs 0 → ZFSet.pair s r ∈ graphs 1 →
    ZFSet.pair s μ ∈ graphs 2 → ZFSet.pair s birth ∈ graphs 3 →
    ZFSet.pair s height ∈ graphs 4 → ChronologyPointCode T C D rD s L r μ birth height

namespace BoundedFormula

def chronologyFunctionsFormula {n} (T V : Fin n) (graphs : Fin 5 → Fin n) : BoundedFormula n :=
  .conj (functionFormula T V (graphs 0)) (.conj (functionFormula T V (graphs 1))
    (.conj (functionFormula T V (graphs 2)) (.conj (functionFormula T V (graphs 3))
      (functionFormula T V (graphs 4)))))

theorem truth_chronologyFunctionsFormula {n} (T V : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyFunctionsFormula T V graphs) env ↔
      ∀ j, ZFSet.IsFunc (env T) (env V) (env (graphs j)) := by
  simp only [chronologyFunctionsFormula, Truth, truth_functionFormula]
  exact ⟨fun ⟨a, b, c, d, e⟩ => Fin.cases a (Fin.cases b (Fin.cases c
      (Fin.cases d (Fin.cases e (fun i => Fin.elim0 i))))),
    fun h => ⟨h 0, h 1, h 2, h 3, h 4⟩⟩

def chronologyPointsFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) :
    BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem T (.allMem V.succ (.allMem V.succ.succ
    (.allMem V.succ.succ.succ (.allMem V.succ.succ.succ.succ
      (.allMem V.succ.succ.succ.succ.succ (imp
        (.conj (pairMembershipFormula 5 4 (lift (graphs 0)))
          (.conj (pairMembershipFormula 5 3 (lift (graphs 1)))
            (.conj (pairMembershipFormula 5 2 (lift (graphs 2)))
              (.conj (pairMembershipFormula 5 1 (lift (graphs 3)))
                (pairMembershipFormula 5 0 (lift (graphs 4)))))))
        (chronologyPointFormula (lift T) (lift C) (lift D) (lift rD) 5 4 3 2 1 0)))))))

def chronologyCoreFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) :
    BoundedFormula n :=
  .conj (chronologyFunctionsFormula T V graphs) (chronologyPointsFormula T V C D rD graphs)

theorem truth_chronologyCoreFormula {n} (T V C D rD : Fin n) (graphs : Fin 5 → Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (chronologyCoreFormula T V C D rD graphs) env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) := by
  simp only [chronologyCoreFormula, Truth, truth_chronologyFunctionsFormula,
    chronologyPointsFormula, truth_imp, truth_pairMembershipFormula, truth_chronologyPointFormula]
  constructor
  · rintro ⟨function, point⟩
    refine ⟨function, ?_⟩
    intro s hs L r μ birth height eL er eμ eb eh
    exact point s hs L (ZFSet.pair_mem_prod.1 ((function 0).1 eL)).2
      r (ZFSet.pair_mem_prod.1 ((function 1).1 er)).2
      μ (ZFSet.pair_mem_prod.1 ((function 2).1 eμ)).2
      birth (ZFSet.pair_mem_prod.1 ((function 3).1 eb)).2
      height (ZFSet.pair_mem_prod.1 ((function 4).1 eh)).2 ⟨eL, er, eμ, eb, eh⟩
  · intro code
    exact ⟨code.function, fun s hs L _ r _ μ _ birth _ height _ ⟨eL, er, eμ, eb, eh⟩ =>
      code.point s hs L r μ birth height eL er eμ eb eh⟩

theorem realize_chronologyCoreFormula (M : TransitiveGround.{u}) {n}
    (T V C D rD : Fin n) (graphs : Fin 5 → Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (chronologyCoreFormula T V C D rD graphs).toFormula env ↔
      ChronologyCoreCode (env T) (env V) (env C) (env D) (env rD) (fun j => env (graphs j)) :=
  (realize_toFormula M _ env members).trans (truth_chronologyCoreFormula T V C D rD graphs env)

end BoundedFormula

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
include core

theorem decoded_point {s : ZFSet.{u}} (hs : s ∈ T) :
    ChronologyPointCode T C D rD s (fields.value 0 s) (fields.value 1 s)
      (fields.value 2 s) (fields.value 3 s) (fields.value 4 s) :=
  core.point s hs _ _ _ _ _ (fields.value_entry 0 hs) (fields.value_entry 1 hs)
    (fields.value_entry 2 hs) (fields.value_entry 3 hs) (fields.value_entry 4 hs)

noncomputable def toHistory
    (layers : ∀ cutoff ∈ T, ∀ t ∈ T, t = cutoff ∨ t ∈ cutoff →
      CodedGrowthLayer M (fields.value 0) (fields.value 1) (fields.value 2)
        (fields.value 0 cutoff) (fields.value 1 cutoff) (fields.value 2 cutoff)
          (fields.value 3 cutoff) t) : GroundChronologicalHistory M T C D rD where
  space := fields.value 0
  order := fields.value 1
  meetGraph := fields.value 2
  birth := fields.value 3
  height := fields.value 4
  space_mem := fun s _ => fields.value_ground 0 s
  order_mem := fun s _ => fields.value_ground 1 s
  meet_mem := fun s _ => fields.value_ground 2 s
  birth_mem := fun s _ => fields.value_ground 3 s
  height_mem := fun s _ => fields.value_ground 4 s
  meet_order := fun _ hs => (fields.decoded_point core hs).meet
  birth_function := fun _ hs => (fields.decoded_point core hs).birth_function
  birth_bound := fun _ hs => (fields.decoded_point core hs).birth_bound
  old_meet := fun _ hs => (fields.decoded_point core hs).old_meet
  strict_height := fun _ hs => (fields.decoded_point core hs).strict_height
  layer := layers

end GroundChronologyFields
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundChronologicalHistory

open SetFormula
universe u
variable {M N : TransitiveGround.{u}} {T C Q qlt : ZFSet.{u}}
variable (history : GroundChronologicalHistory M T C Q qlt)

def of_inclusion (includes : M.sets ⊆ N.sets) : GroundChronologicalHistory N T C Q qlt where
  space := history.space
  order := history.order
  meetGraph := history.meetGraph
  birth := history.birth
  height := history.height
  space_mem := fun s hs => includes (history.space_mem s hs)
  order_mem := fun s hs => includes (history.order_mem s hs)
  meet_mem := fun s hs => includes (history.meet_mem s hs)
  birth_mem := fun s hs => includes (history.birth_mem s hs)
  height_mem := fun s hs => includes (history.height_mem s hs)
  meet_order := history.meet_order
  birth_function := history.birth_function
  birth_bound := history.birth_bound
  old_meet := history.old_meet
  strict_height := history.strict_height
  layer := fun cutoff hc t ht bounded => (history.layer cutoff hc t ht bounded).of_inclusion includes

theorem exists_extension_basis
    (includes : M.sets ⊆ N.sets)
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0) (separation : SeparationSchema N.sets)
    (infinite : Realize N.sets SetFormula.infinity Fin.elim0)
    (choice : Realize N.sets SetFormula.choice Fin.elim0)
    (hT : T ∈ M.sets) (hC : C ∈ M.sets) (hQ : Q ∈ M.sets)
    (ordinal : ordinalSetProperty T) (smallQ : M.groundEmbeddable Q ZFSet.omega)
    (irreflexive : ∀ q ∈ Q, ZFSet.pair q q ∉ qlt)
    {cutoff F : ZFSet.{u}} (hc : cutoff ∈ T) (hF : F ∈ N.sets)
    (filter : MeetFilterCode (history.space cutoff) (history.order cutoff) (history.meetGraph cutoff) F) :
    ∃ B ∈ N.sets, ∃ f ∈ N.sets, InjectionCode B ZFSet.omega f ∧ B ⊆ F ∧
      ∀ x ∈ F, ∃ b ∈ B, ZFSet.pair b x ∈ history.order cutoff :=
  (history.of_inclusion includes).exists_internal_basis pairing unions powers separation infinite
    choice (includes hT) (includes hC) (includes hQ) ordinal
    (M.groundEmbeddable_of_inclusion N includes smallQ) irreflexive hc hF filter

end PartitionPilot.Forcing.GroundChronologicalHistory



namespace PartitionPilot.Forcing.GroundChronologyFields
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)

noncomputable def attainedBound : ZFSet.{u} :=
  ZFSet.sUnion (ZFSet.range (fun j : Fin 5 => functionGraphRange T (fields.graph j)))

theorem mem_attainedBound (y : ZFSet.{u}) :
    y ∈ fields.attainedBound ↔ ∃ j : Fin 5, ∃ s ∈ T, ZFSet.pair s y ∈ fields.graph j := by
  constructor
  · intro hy
    obtain ⟨R, hR, hy⟩ := ZFSet.mem_sUnion.1 hy
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 hR
    exact ⟨j, (mem_functionGraphRange T (fields.graph j) y).1 hy⟩
  · rintro ⟨j, s, hs, entry⟩
    exact ZFSet.mem_sUnion.2 ⟨functionGraphRange T (fields.graph j),
      ZFSet.mem_range.2 ⟨j, rfl⟩,
      (mem_functionGraphRange T (fields.graph j) y).2 ⟨s, hs, entry⟩⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)

include pairing unions separation in
theorem attainedBound_ground : fields.attainedBound ∈ M.sets :=
  M.union_mem unions (M.finite_range_mem pairing unions ⟨T, fields.time_ground⟩
    (fun j : Fin 5 => functionGraphRange T (fields.graph j))
    (fun j => M.functionGraphRange_mem unions separation fields.time_ground (fields.graph_ground j)))

noncomputable def normalizeBound : GroundChronologyFields M T where
  time_ground := fields.time_ground
  bound := fields.attainedBound
  bound_ground := fields.attainedBound_ground pairing unions separation
  graph := fields.graph
  graph_ground := fields.graph_ground
  function := by
    intro j
    refine ⟨?_, (fields.function j).2⟩
    intro z hz
    obtain ⟨s, hs, y, rfl⟩ := (fields.graphFunction j).shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hs, (fields.mem_attainedBound y).2 ⟨j, s, hs, hz⟩⟩

theorem normalizeBound_graph :
    (fields.normalizeBound pairing unions separation).graph = fields.graph := rfl

theorem normalizeBound_value (j : Fin 5) (s : ZFSet.{u}) :
    (fields.normalizeBound pairing unions separation).value j s = fields.value j s := rfl

theorem normalizeBound_core (core : ChronologyCoreCode T fields.bound C D rD fields.graph) :
    ChronologyCoreCode T (fields.normalizeBound pairing unions separation).bound C D rD
      (fields.normalizeBound pairing unions separation).graph :=
  ⟨(fields.normalizeBound pairing unions separation).function, core.point⟩

variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem attainedBound_rank_lt (graphs : ∀ j, ZFSet.rank (fields.graph j) < o) :
    ZFSet.rank fields.attainedBound < o :=
  (ZFSet.rank_sUnion_le _).trans_lt (rank_finiteRange_lt limit 5 _
    (fun j => (functionGraphRange_rank_le T (fields.graph j)).trans_lt (graphs j)))

theorem normalizeBound_code_rank_lt (time : ZFSet.rank T < o)
    (graphs : ∀ j, ZFSet.rank (fields.graph j) < o) :
    ZFSet.rank (fields.normalizeBound pairing unions separation).code < o :=
  rank_nonemptyTupleCode_lt limit 6 _
    (Fin.cases time (Fin.cases (fields.attainedBound_rank_lt limit graphs) graphs))

end PartitionPilot.Forcing.GroundChronologyFields



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace ChronologyPointCode
theorem retarget_time {T S C D rD s L r μ birth height : ZFSet.{u}}
    (point : ChronologyPointCode T C D rD s L r μ birth height)
    (transitive : ∀ x ∈ S, ∀ y ∈ x, y ∈ S) (hs : s ∈ S) :
    ChronologyPointCode S C D rD s L r μ birth height := by
  refine ⟨point.meet, ?_, point.birth_bound, point.old_meet, point.strict_height⟩
  refine ⟨?_, point.birth_function.2⟩
  intro z hz
  obtain ⟨x, hx, t, _, equal⟩ := ZFSet.mem_prod.1 (point.birth_function.1 hz)
  subst z
  exact ZFSet.pair_mem_prod.2 ⟨hx, (point.birth_bound x hx t hz).elim
    (fun equal => equal.symm ▸ hs) (fun earlier => transitive s hs t earlier)⟩
end ChronologyPointCode

namespace GroundChronologyFields
variable {M : TransitiveGround.{u}} {T S C D rD : ZFSet.{u}}
variable (fields : GroundChronologyFields M T)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets) (hS : S ∈ M.sets) (subset : S ⊆ T)

noncomputable def restrictTo : GroundChronologyFields M S where
  time_ground := hS
  bound := fields.bound
  bound_ground := fields.bound_ground
  graph := fun j => graphRestriction S (fields.graph j)
  graph_ground := fun j => M.graphRestriction_mem unions separation hS (fields.graph_ground j)
  function := by
    intro j
    refine ⟨?_, ((fields.graphFunction j).restrict subset).to_isFunc.2⟩
    intro z hz
    obtain ⟨s, hs, x, equal, entry⟩ := mem_graphRestriction.1 hz
    subst z
    exact ZFSet.pair_mem_prod.2 ⟨hs, (ZFSet.pair_mem_prod.1 ((fields.function j).1 entry)).2⟩

theorem restrictTo_value (j : Fin 5) {s : ZFSet.{u}} (hs : s ∈ S) :
    (fields.restrictTo unions separation hS subset).value j s = fields.value j s :=
  (fields.restrictTo unions separation hS subset).value_eq_of_entry j
    (pair_mem_graphRestriction.2 ⟨fields.value_entry j (subset hs), hs⟩)

theorem restrictTo_graph (j : Fin 5) :
    (fields.restrictTo unions separation hS subset).graph j = graphRestriction S (fields.graph j) := rfl

theorem restrictTo_core (core : ChronologyCoreCode T fields.bound C D rD fields.graph)
    (transitive : ∀ x ∈ S, ∀ y ∈ x, y ∈ S) :
    ChronologyCoreCode S fields.bound C D rD
      (fields.restrictTo unions separation hS subset).graph := by
  refine ⟨(fields.restrictTo unions separation hS subset).function, ?_⟩
  intro s hs L r μ birth height eL er eμ eb eh
  exact (core.point s (subset hs) L r μ birth height
    (pair_mem_graphRestriction.1 eL).1 (pair_mem_graphRestriction.1 er).1
    (pair_mem_graphRestriction.1 eμ).1 (pair_mem_graphRestriction.1 eb).1
    (pair_mem_graphRestriction.1 eh).1).retarget_time transitive hs

theorem restrictTo_code_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    (fields.restrictTo unions separation hS subset).code ∈ M.sets :=
  (fields.restrictTo unions separation hS subset).code_ground pairing

end GroundChronologyFields





structure GroundSerializedChronology (M : TransitiveGround.{u}) (T C D rD : ZFSet.{u}) where
  fields : GroundChronologyFields M T
  ordinal : ordinalSetProperty T
  core : ChronologyCoreCode T fields.bound C D rD fields.graph
  layerBound : ZFSet.{u}
  layer_bound_ground : layerBound ∈ M.sets
  layers : ZFSet.{u}
  layers_ground : layers ∈ M.sets
  layer_function : ZFSet.IsFunc (chronologyPairs T) layerBound layers
  layer_code : ∀ s ∈ T, ∀ t ∈ T, t = s ∨ t ∈ s → ∀ z,
    ZFSet.pair (ZFSet.pair s t) z ∈ layers →
      GrowthLayerWitnessCode (fields.graph 0) (fields.graph 1) (fields.graph 2)
        (fields.value 0 s) (fields.value 1 s) (fields.value 2 s) (fields.value 3 s) t ZFSet.omega z

namespace GroundSerializedChronology
variable {M : TransitiveGround.{u}} {T C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

noncomputable def layerWitness (s t : ZFSet.{u}) : ZFSet.{u} :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue (ZFSet.pair s t)

theorem layerWitness_entry {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    ZFSet.pair (ZFSet.pair s t) (serial.layerWitness s t) ∈ serial.layers :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue_entry
      ((pair_mem_chronologyPairs T s t).2 ⟨hs, ht, earlier⟩)

theorem layerWitness_ground (s t : ZFSet.{u}) : serial.layerWitness s t ∈ M.sets :=
  (show FunctionGraphOn (chronologyPairs T) serial.layers from
    ⟨serial.layerBound, serial.layer_function⟩).totalValue_ground M serial.layers_ground _

noncomputable def decodedLayer {s t : ZFSet.{u}} (hs : s ∈ T) (ht : t ∈ T)
    (earlier : t = s ∨ t ∈ s) :
    CodedGrowthLayer M (serial.fields.value 0) (serial.fields.value 1) (serial.fields.value 2)
      (serial.fields.value 0 s) (serial.fields.value 1 s) (serial.fields.value 2 s)
        (serial.fields.value 3 s) t :=
  (serial.layer_code s hs t ht earlier _ (serial.layerWitness_entry hs ht earlier)).toLayer
    (serial.layerWitness_ground s t) (serial.fields.value 0) (serial.fields.value 1)
      (serial.fields.value 2) rfl (fun a ha =>
        ⟨serial.fields.value_entry 0 (serial.ordinal.1 t ht a ha),
          serial.fields.value_entry 1 (serial.ordinal.1 t ht a ha),
          serial.fields.value_entry 2 (serial.ordinal.1 t ht a ha)⟩)

noncomputable def toHistory : GroundChronologicalHistory M T C D rD :=
  serial.fields.toHistory serial.core (fun _ hs _ ht earlier => serial.decodedLayer hs ht earlier)

noncomputable def codeFields : Fin 3 → ZFSet.{u} :=
  Fin.cases serial.fields.code (Fin.cases serial.layerBound (fun _ => serial.layers))

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 2 serial.codeFields

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    serial.code ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 2 serial.codeFields
    (Fin.cases (serial.fields.code_ground pairing)
      (Fin.cases serial.layer_bound_ground (fun _ => serial.layers_ground)))

theorem toHistory_values (s : ZFSet.{u}) :
    serial.toHistory.space s = serial.fields.value 0 s ∧
      serial.toHistory.order s = serial.fields.value 1 s ∧
      serial.toHistory.meetGraph s = serial.fields.value 2 s ∧
      serial.toHistory.birth s = serial.fields.value 3 s ∧
      serial.toHistory.height s = serial.fields.value 4 s := ⟨rfl, rfl, rfl, rfl, rfl⟩

end GroundSerializedChronology
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundSerializedChronology
universe u
variable {M : TransitiveGround.{u}} {T T' C D rD : ZFSet.{u}}
variable (serial : GroundSerializedChronology M T C D rD)

def castTime (equal : T = T') : GroundSerializedChronology M T' C D rD := equal ▸ serial

theorem castTime_code (equal : T = T') : (serial.castTime equal).code = serial.code := by
  cases equal
  rfl

theorem castTime_graph (equal : T = T') (j : Fin 5) :
    (serial.castTime equal).fields.graph j = serial.fields.graph j := by
  cases equal
  rfl

theorem castTime_value (equal : T = T') (j : Fin 5) (s : ZFSet.{u}) :
    (serial.castTime equal).fields.value j s = serial.fields.value j s := by
  cases equal
  rfl

theorem castTime_layers (equal : T = T') :
    (serial.castTime equal).layers = serial.layers ∧
      (serial.castTime equal).layerBound = serial.layerBound := by
  cases equal
  exact ⟨rfl,rfl⟩

end PartitionPilot.Forcing.GroundSerializedChronology

end OAI
