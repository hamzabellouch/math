import OAI.SetTheory.PartitionPrinciple.Forcing.NatActionUnions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCoherentHeightUnion
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFinalInsertionExceptions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFiniteAccounting
import OAI.SetTheory.PartitionPrinciple.Geometry.HeightColumnBoundLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleFulfillmentAtBound
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundHistoryFields

namespace OAI


namespace PartitionPilot.Forcing.NatUnionCode
universe u

theorem injection {D C f : Nat → ZFSet.{u}} {U V F : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V) (graph : NatUnionCode f F)
    (injections : ∀ n, InjectionCode (D n) (C n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m) : InjectionCode U V F := by
  refine ⟨domain.isFunc range graph (fun n => (injections n).function) graphMono, ?_⟩
  intro x y z first second
  obtain ⟨n, hn⟩ := (graph _).1 first
  obtain ⟨m, hm⟩ := (graph _).1 second
  exact (injections (max n m)).injective x y z
    (graphMono n _ (le_max_left n m) hn) (graphMono m _ (le_max_right n m) hm)

theorem meetEmbedding {D C rD rC μD μC f : Nat → ZFSet.{u}}
    {U V RU RV MU MV F : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (domainOrder : NatUnionCode rD RU) (rangeOrder : NatUnionCode rC RV)
    (domainMeet : NatUnionCode μD MU) (rangeMeet : NatUnionCode μC MV)
    (graph : NatUnionCode f F)
    (embeddings : ∀ n, MeetEmbeddingCode (D n) (C n) (rD n) (rC n) (μD n) (μC n) (f n))
    (graphMono : ∀ n m, n ≤ m → f n ⊆ f m)
    (orderMono : ∀ n m, n ≤ m → rD n ⊆ rD m)
    (meetMono : ∀ n m, n ≤ m → μD n ⊆ μD m) :
    MeetEmbeddingCode U V RU RV MU MV F := by
  refine ⟨domain.injection range graph (fun n => (embeddings n).injection) graphMono, ?_, ?_⟩
  · intro x y x' y' lower first second
    obtain ⟨n, hn⟩ := (domainOrder _).1 lower
    obtain ⟨j, hj⟩ := (graph _).1 first
    obtain ⟨k, hk⟩ := (graph _).1 second
    let m := max n (max j k)
    have nle : n ≤ m := le_max_left _ _
    have jle : j ≤ m := (le_max_left j k).trans (le_max_right n _)
    have kle : k ≤ m := (le_max_right j k).trans (le_max_right n _)
    exact rangeOrder.subset m ((embeddings m).monotone x y x' y'
      (orderMono n m nle hn) (graphMono j m jle hj) (graphMono k m kle hk))
  · intro x y z x' y' z' meet first second third
    obtain ⟨n, hn⟩ := (domainMeet _).1 meet
    obtain ⟨i, hi⟩ := (graph _).1 first
    obtain ⟨j, hj⟩ := (graph _).1 second
    obtain ⟨k, hk⟩ := (graph _).1 third
    let m := max n (max i (max j k))
    have nle : n ≤ m := le_max_left _ _
    have ile : i ≤ m := (le_max_left i _).trans (le_max_right n _)
    have jle : j ≤ m := ((le_max_left j k).trans (le_max_right i _)).trans (le_max_right n _)
    have kle : k ≤ m := ((le_max_right j k).trans (le_max_right i _)).trans (le_max_right n _)
    exact rangeMeet.subset m ((embeddings m).map_meet x y z x' y' z'
      (meetMono n m nle hn) (graphMono i m ile hi) (graphMono j m jle hj) (graphMono k m kle hk))

theorem shift {stages : Nat → ZFSet.{u}} {union : ZFSet.{u}}
    (code : NatUnionCode stages union) (first : stages 0 ⊆ stages 1) :
    NatUnionCode (fun n => stages (n + 1)) union := by
  intro x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := (code x).1 hx
    cases n with
    | zero => exact ⟨0, first hn⟩
    | succ n => exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact code.subset (n + 1) hn

end PartitionPilot.Forcing.NatUnionCode



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_codes (n : Nat) :
    let data := state.data.iterate M I Sources Reps G T n
    MeetOrderCode data.D data.rD data.μD ∧
      MeetOrderCode data.currentCarrier data.currentOrder data.currentMeet ∧
      PosetActionCode G data.currentCarrier m one data.currentOrder data.A ∧
      FunctionGraphOn I data.Maps ∧
      ∀ i S, ZFSet.pair i S ∈ data.Maps →
        MeetEmbeddingCode data.D data.currentCarrier data.rD data.currentOrder data.μD data.currentMeet S := by
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  rw [← equal]
  exact ⟨current.batch.oldOrder, current.batch.batch_meetOrder, current.inputs.action,
    current.inputs.maps, current.inputs.valid⟩

theorem canonical_iterate_graphs_mono {n k : Nat} (before : n ≤ k) :
    let first := state.data.iterate M I Sources Reps G T n
    let last := state.data.iterate M I Sources Reps G T k
    first.D ⊆ last.D ∧ first.rD ⊆ last.rD ∧ first.μD ⊆ last.μD ∧
      first.currentCarrier ⊆ last.currentCarrier ∧ first.currentOrder ⊆ last.currentOrder ∧
      first.currentMeet ⊆ last.currentMeet ∧ first.A ⊆ last.A ∧
      ∀ i S S', ZFSet.pair i S ∈ first.Maps → ZFSet.pair i S' ∈ last.Maps → S ⊆ S' := by
  let first := state.data.iterate M I Sources Reps G T n
  let last := state.data.iterate M I Sources Reps G T k
  have coherent := state.canonical_iterate_coherent pairing unions powers separation
    hI hSources hReps hG hT before
  obtain ⟨old, current, action, maps, valid⟩ := state.canonical_iterate_codes
    pairing unions powers separation hI hSources hReps hG hT n
  have pair_subset {X Y f g : ZFSet.{u}} (shape : f ⊆ ZFSet.prod X Y)
      (transfer : ∀ x ∈ X, ∀ y ∈ Y, ZFSet.pair x y ∈ f → ZFSet.pair x y ∈ g) : f ⊆ g := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shape hz)
    exact transfer x hx y hy hz
  refine ⟨coherent.carrier, ?_, ?_, coherent.currentCarrier, ?_, ?_, ?_, ?_⟩
  · exact pair_subset old.order.relation
      (fun x hx y hy entry => (coherent.order x hx y hy).2 entry)
  · apply pair_subset old.operation.1
    intro xy hxy z _ entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact (coherent.meet x hx y hy z).2 entry
  · exact pair_subset current.order.relation
      (fun x hx y hy entry => (coherent.currentOrder x hx y hy).2 entry)
  · apply pair_subset current.operation.1
    intro xy hxy z _ entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact (coherent.currentMeet x hx y hy z).2 entry
  · apply pair_subset action.function.1
    intro gx hgx y _ entry
    obtain ⟨g, _, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact (coherent.action g x hx y).2 entry
  · intro i S S' oldEntry newEntry
    apply pair_subset (valid i S oldEntry).injection.function.1
    intro x hx y _ entry
    exact (coherent.maps i (maps.pair_source oldEntry) S S' oldEntry newEntry x hx y).2 entry

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem canonical_iterate_profile {c e K F : ZFSet.{u}}
    (hc : c ∈ state.data.currentCarrier) (he : e ∈ state.data.currentCarrier)
    (hK : K ∈ state.data.currentCarrier) (subset : F ⊆ state.data.currentCarrier)
    (nonempty : ∃ f, f ∈ F)
    (profile : CodedInsertionProfile state.data.currentCarrier state.data.currentOrder
      state.data.currentMeet c e K F)
    (separated : ZFSet.pair e K ∉ state.data.currentOrder) (n : Nat) :
    CodedInsertionProfile (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).currentMeet c e K F := by
  induction n with
  | zero => exact profile
  | succ n ih =>
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT (n + 1)
    have coherent := state.canonical_iterate_coherent pairing unions powers separation
      hI hSources hReps hG hT (Nat.zero_le n)
    have hcOld : c ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier hc
    have heOld : e ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier he
    have hKOld : K ∈ current.data.D := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier hK
    have subsetOld : F ⊆ current.data.D := by
      intro f hf
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor]
        using coherent.currentCarrier (subset hf)
    have profileOld : CodedInsertionProfile current.data.D current.data.rD current.data.μD c e K F := by
      simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using ih
    have separatedOld : ZFSet.pair e K ∉ current.data.rD := by
      intro below
      have later : ZFSet.pair e K ∈ (state.data.iterate M I Sources Reps G T n).currentOrder := by
        simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using below
      exact separated ((coherent.currentOrder e he K hK).1 later)
    have result := current.batch.insertion_profile_persists hcOld heOld hKOld
      subsetOld nonempty profileOld separatedOld
    change CodedInsertionProfile current.data.currentCarrier current.data.currentOrder
      current.data.currentMeet c e K F at result
    simpa only [equal] using result

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundCompressionUnionData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u}) where
  fields : Fin 13 → ZFSet.{u}
  ground : ∀ j, fields j ∈ M.sets
  fieldUnion : ∀ j, NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).field j) (fields j)
  currentCarrier : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentCarrier) (fields 0)
  currentOrder : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentOrder) (fields 1)
  currentMeet : NatUnionCode
    (fun n => (initial.iterate M I Sources Reps G T n).currentMeet) (fields 2)
  meet : MeetOrderCode (fields 0) (fields 1) (fields 2)
  action : PosetActionCode G (fields 0) m one (fields 1) (fields 12)

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundUnion
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    Nonempty (GroundCompressionUnionData M state.data I Sources Reps G m one T) := by
  classical
  let stages := state.data.iterate M I Sources Reps G T
  obtain ⟨history, hHistory, _, entries, _, _⟩ := state.exists_groundHistory
    pairing unions powers separation collection infinite hI hSources hReps hG hT
  have allFields : ∀ j : Fin 13, ∃ U ∈ M.sets,
      NatUnionCode (fun n => (stages n).field j) U := by
    intro j
    obtain ⟨_, _, _, _, U, hU, _, _, _, _, exactUnion⟩ :=
      M.exists_groundStateFieldUnion pairing unions separation collection
        (M.omega_mem separation infinite) hHistory stages entries j
    exact ⟨U, hU, exactUnion⟩
  choose fields ground exactFields using allFields
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT
  have mono {n k : Nat} (h : n ≤ k) :=
    state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT h
  have carrierUnion : NatUnionCode (fun n => (stages n).D) (fields 0) := exactFields 0
  have orderUnion : NatUnionCode (fun n => (stages n).rD) (fields 1) := exactFields 1
  have meetUnion : NatUnionCode (fun n => (stages n).μD) (fields 2) := exactFields 2
  have actionUnion : NatUnionCode (fun n => (stages n).A) (fields 12) := exactFields 12
  have currentCarrier : NatUnionCode (fun n => (stages n).currentCarrier) (fields 0) :=
    carrierUnion.shift (mono (Nat.zero_le 1)).1
  have currentOrder : NatUnionCode (fun n => (stages n).currentOrder) (fields 1) :=
    orderUnion.shift (mono (Nat.zero_le 1)).2.1
  have currentMeet : NatUnionCode (fun n => (stages n).currentMeet) (fields 2) :=
    meetUnion.shift (mono (Nat.zero_le 1)).2.2.1
  have unionMeet : MeetOrderCode (fields 0) (fields 1) (fields 2) :=
    carrierUnion.meetOrder orderUnion meetUnion (fun n => (codes n).1)
      (fun _ _ h => (mono h).1) (fun _ _ h => (mono h).2.1) (fun _ _ h => (mono h).2.2.1)
  have unionAction : PosetActionCode G (fields 0) m one (fields 1) (fields 12) :=
    currentCarrier.posetAction currentOrder actionUnion (fun n => (codes n).2.2.1)
      (fun _ _ h => (mono h).2.2.2.2.1) (fun _ _ h => (mono h).2.2.2.2.2.2.1)
  exact ⟨⟨fields, ground, exactFields, currentCarrier, currentOrder, currentMeet, unionMeet, unionAction⟩⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem rank_taggedExtension_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    {P N : ZFSet.{u}} (points : ZFSet.rank P < o) (fresh : ZFSet.rank N < o) :
    ZFSet.rank (taggedExtension P N) < o := by
  rw [taggedExtension, ZFSet.rank_union]
  exact max_lt points (rank_product_lt limit (rank_singleton_lt limit points) fresh)

namespace RecursiveTemplateConstancy
variable {P r μ : ZFSet.{u}} {initial : RecursiveStateData.{u}}
variable (constant : RecursiveTemplateConstancy P r μ initial)
include constant

theorem fresh_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (indices : ZFSet.rank initial.J < o) (templates : ZFSet.rank P < o) :
    ZFSet.rank initial.fresh < o := by
  have subset : initial.fresh ⊆ ZFSet.prod initial.J P := by
    intro z hz
    have domain := indexedAttachmentFresh_subset initial.J initial.Qs initial.rs initial.As hz
    obtain ⟨i, hi, q, rfl, Q, entry, hq⟩ := (mem_indexedAttachmentDomain _ _ _).1 domain
    exact ZFSet.pair_mem_prod.2 ⟨hi, (constant.space_entry_iff i Q).1 entry |>.2 ▸ hq⟩
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit indices templates)

theorem currentCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) : ZFSet.rank initial.currentCarrier < o :=
  rank_taggedExtension_lt limit points (constant.fresh_rank_lt limit indices templates)

theorem iterate_carrier_ranks (M : TransitiveGround.{u}) (I Sources Reps G T : ZFSet.{u})
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) (n : Nat) :
    ZFSet.rank (initial.iterate M I Sources Reps G T n).D < o ∧
      ZFSet.rank (initial.iterate M I Sources Reps G T n).J < o := by
  induction n with
  | zero => exact ⟨points, indices⟩
  | succ n ih =>
    rw [RecursiveStateData.iterate_succ]
    refine ⟨(constant.iterate M I Sources Reps G T n).currentCarrier_rank_lt limit ih.1 ih.2 templates, ?_⟩
    exact (ZFSet.rank_mono (recursiveAttachmentIndices_subset _ _ _ _ _ _)).trans_lt
      (rank_product_lt limit tasks ih.2)

end RecursiveTemplateConstancy

theorem NatUnionCode.rank_le {sets : Nat → ZFSet.{u}} {U : ZFSet.{u}} (code : NatUnionCode sets U)
    {o : Ordinal.{u}} (bounds : ∀ n, ZFSet.rank (sets n) < o) : ZFSet.rank U ≤ o := by
  apply ZFSet.rank_le_iff.2
  intro x hx
  obtain ⟨n, member⟩ := (code x).1 hx
  exact (ZFSet.rank_lt_of_mem member).trans (bounds n)

namespace GroundCompressionUnionData
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (data : GroundCompressionUnionData M initial I Sources Reps G m one T)

theorem carrier_rank_le {P r μ : ZFSet.{u}} (constant : RecursiveTemplateConstancy P r μ initial)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank initial.D < o) (indices : ZFSet.rank initial.J < o)
    (templates : ZFSet.rank P < o) (tasks : ZFSet.rank I < o) :
    ZFSet.rank (data.fields 0) ≤ o :=
  (data.fieldUnion 0).rank_le
    (fun n => (constant.iterate_carrier_ranks M I Sources Reps G T limit points indices templates tasks n).1)

end GroundCompressionUnionData

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)

theorem union_original_subset : P0 ⊆ data.fields 0 := by
  intro x hx
  exact (data.fieldUnion 0).subset 0 (state.invariant.originalSubset hx)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_order_iff (n : Nat) {x y : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).D)
    (hy : y ∈ (state.data.iterate M I Sources Reps G T n).D) :
    ZFSet.pair x y ∈ data.fields 1 ↔ ZFSet.pair x y ∈ (state.data.iterate M I Sources Reps G T n).rD :=
  (data.fieldUnion 1).order_entry_iff
    (fun _ _ h => (state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT h).2.1)
    (fun _ _ h => (state.canonical_iterate_coherent pairing unions powers separation hI hSources hReps hG hT h).order)
    n hx hy

theorem union_meet_iff (n : Nat) {x y z : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).D)
    (hy : y ∈ (state.data.iterate M I Sources Reps G T n).D) :
    ZFSet.pair (ZFSet.pair x y) z ∈ data.fields 2 ↔
      ZFSet.pair (ZFSet.pair x y) z ∈ (state.data.iterate M I Sources Reps G T n).μD :=
  (data.fieldUnion 2).meet_entry_iff data.meet
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).1) n hx hy

theorem union_action_iff (n : Nat) {g x y : ZFSet.{u}}
    (hx : x ∈ (state.data.iterate M I Sources Reps G T n).currentCarrier) :
    ZFSet.pair (ZFSet.pair g x) y ∈ data.fields 12 ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ (state.data.iterate M I Sources Reps G T n).A :=
  (data.fieldUnion 12).action_entry_iff data.action
    (fun n => (state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n).2.2.1) n hx

theorem union_original_order_iff {x y : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair x y ∈ data.fields 1 ↔ ZFSet.pair x y ∈ r0 :=
  (state.union_order_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (state.invariant.originalSubset hx) (state.invariant.originalSubset hy)).trans
      (state.invariant.originalOrder x hx y hy)

theorem union_original_meet_iff {x y z : ZFSet.{u}} (hx : x ∈ P0) (hy : y ∈ P0) :
    ZFSet.pair (ZFSet.pair x y) z ∈ data.fields 2 ↔ ZFSet.pair (ZFSet.pair x y) z ∈ μ0 :=
  (state.union_meet_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (state.invariant.originalSubset hx) (state.invariant.originalSubset hy)).trans
      (state.invariant.originalMeet x hx y hy z)

theorem union_original_action_iff {g x y : ZFSet.{u}} (hx : x ∈ P0) :
    ZFSet.pair (ZFSet.pair g x) y ∈ data.fields 12 ↔ ZFSet.pair (ZFSet.pair g x) y ∈ A0 :=
  (state.union_action_iff data pairing unions powers separation hI hSources hReps hG hT 0
    (old_mem_taggedExtension (state.invariant.originalSubset hx))).trans
      (state.invariant.originalAction g x hx y)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
universe u

structure GroundCompressionHeightData (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u})
    (union : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (P0 C D rD original : ZFSet.{u}) where
  family : ZFSet.{u}
  family_ground : family ∈ M.sets
  function : FunctionGraphOn ZFSet.omega family
  zero : function.natValue 0 = original
  finite : ∀ n, StrictLexHeightCode (initial.iterate M I Sources Reps G T n).D C D
    (initial.iterate M I Sources Reps G T n).rD (function.natValue n) rD
  adjacent : ∀ n, function.natValue n ⊆ function.natValue (n + 1)
  height : ZFSet.{u}
  height_ground : height ∈ M.sets
  exact_union : NatUnionCode function.natValue height
  code : StrictLexHeightCode (union.fields 0) C D (union.fields 1) height rD
  finite_entries : ∀ n x, x ∈ (initial.iterate M I Sources Reps G T n).D → ∀ y,
    ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ function.natValue n
  original_entries : ∀ x ∈ P0, ∀ y, ZFSet.pair x y ∈ height ↔ ZFSet.pair x y ∈ original
  range_ground : relationImage (union.fields 0) (ZFSet.prod C D) height ∈ M.sets
  range_countable : M.groundEmbeddable (relationImage (union.fields 0) (ZFSet.prod C D) height) ZFSet.omega
  columns : ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns P0 C D original





structure CompressionOriginalData (P r μ A G U u ν B : ZFSet.{u}) : Prop where
  subset : P ⊆ U
  order : ∀ x ∈ P, ∀ y ∈ P, ZFSet.pair x y ∈ u ↔ ZFSet.pair x y ∈ r
  meet : ∀ x ∈ P, ∀ y ∈ P, ∀ z, ZFSet.pair (ZFSet.pair x y) z ∈ ν ↔
    ZFSet.pair (ZFSet.pair x y) z ∈ μ
  action : ∀ g x, x ∈ P → ∀ y, ZFSet.pair (ZFSet.pair g x) y ∈ B ↔
    ZFSet.pair (ZFSet.pair g x) y ∈ A
  agreement : ∀ g ∈ G, ∀ h ∈ G, ∀ v ∈ P, ActionAgreementBelow P r A g h v →
    ActionAgreementBelow U u B g h v

namespace GroundCompressionState
open SetFormula
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_original_agreement {g h v : ZFSet.{u}} (hg : g ∈ G) (hh : h ∈ G) (hv : v ∈ P0)
    (agreement : ActionAgreementBelow P0 r0 A0 g h v) :
    ActionAgreementBelow (data.fields 0) (data.fields 1) (data.fields 12) g h v := by
  intro x _ y _ below
  obtain ⟨n, lower⟩ := (data.currentOrder _).1 below
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT n
  have hx := (ZFSet.pair_mem_prod.1 (codes.2.1.order.relation lower)).1
  have finiteAgreement : ActionAgreementBelow
      (state.data.iterate M I Sources Reps G T n).currentCarrier
      (state.data.iterate M I Sources Reps G T n).currentOrder
      (state.data.iterate M I Sources Reps G T n).A g h v := by
    obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
      hI hSources hReps hG hT n
    have agree := current.invariant.agreement g hg h hh v hv agreement
    change ActionAgreementBelow current.data.currentCarrier current.data.currentOrder current.data.A g h v at agree
    simpa only [equal] using agree
  have restrict (k : ZFSet.{u}) := state.union_action_iff data pairing unions powers separation
    hI hSources hReps hG hT n (g := k) (y := y) hx
  constructor
  · intro entry
    have first := (restrict g).1 entry
    have hy := (ZFSet.pair_mem_prod.1 (codes.2.2.1.function.1 first)).2
    exact (restrict h).2 ((finiteAgreement x hx y hy lower).1 first)
  · intro entry
    have second := (restrict h).1 entry
    have hy := (ZFSet.pair_mem_prod.1 (codes.2.2.1.function.1 second)).2
    exact (restrict g).2 ((finiteAgreement x hx y hy lower).2 second)

theorem union_original_data :
    CompressionOriginalData P0 r0 μ0 A0 G (data.fields 0) (data.fields 1) (data.fields 2) (data.fields 12) :=
  ⟨state.union_original_subset data,
    fun _ hx _ hy => state.union_original_order_iff data pairing unions powers separation hI hSources hReps hG hT hx hy,
    fun _ hx _ hy _ => state.union_original_meet_iff data pairing unions powers separation hI hSources hReps hG hT hx hy,
    fun _ _ hx _ => state.union_original_action_iff data pairing unions powers separation hI hSources hReps hG hT hx,
    fun _ hg _ hh _ hv agree => state.union_original_agreement data pairing unions powers separation
      hI hSources hReps hG hT hg hh hv agree⟩

end GroundCompressionState






theorem ExternalRectangleCode.lift_compression
    {P r μ A G U u ν B m one c b d g h : ZFSet.{u}}
    (rectangle : ExternalRectangleCode P G r μ A c b d g h)
    (compression : CompressionOriginalData P r μ A G U u ν B)
    (action : PosetActionCode G P m one r A) :
    ExternalRectangleCode U G u ν B c b d g h := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, w, hw, cb, agree, separated⟩ := rectangle
  refine ⟨compression.subset hc, compression.subset hb, compression.subset hd, hg, hh,
    (compression.order c hc d hd).2 cd, (compression.order b hb d hd).2 bd,
    w, compression.subset hw, (compression.meet c hc b hb w).2 cb,
    compression.agreement g hg h hh w hw agree, ?_⟩
  intro y _ z _ v _ entries
  have dy := (compression.action g d hd y).1 entries.1
  have dz := (compression.action h d hd z).1 entries.2.1
  have wv := (compression.action g w hw v).1 entries.2.2
  have hy := (ZFSet.pair_mem_prod.1 (action.function.1 dy)).2
  have hz := (ZFSet.pair_mem_prod.1 (action.function.1 dz)).2
  have hv := (ZFSet.pair_mem_prod.1 (action.function.1 wv)).2
  exact (compression.meet y hy z hz v).2 (separated y hy z hz v hv ⟨dy, dz, wv⟩)

theorem externalRectangles_subset_compression
    {P r μ A G U u ν B m one : ZFSet.{u}}
    (compression : CompressionOriginalData P r μ A G U u ν B)
    (action : PosetActionCode G P m one r A) :
    externalRectangles P G r μ A ⊆ externalRectangles U G u ν B := by
  intro x hx
  obtain ⟨c, b, d, g, h, rfl, rectangle⟩ := (mem_externalRectangles P G r μ A x).1 hx
  exact (externalRectangleCode_mem U G u ν B c b d g h).2
    (rectangle.lift_compression compression action)





structure GroundCompressionOrigin (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}) where
  seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters
  state : GroundCompressionState M seed
  initial_data : state.data = initial

namespace GroundCompressionOrigin
open SetFormula
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable (origin : GroundCompressionOrigin M initial P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters)

include origin in
theorem union_original_data
    (data : GroundCompressionUnionData M initial I Sources Reps G m one T)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    CompressionOriginalData P0 r0 μ0 A0 G (data.fields 0) (data.fields 1) (data.fields 2) (data.fields 12) := by
  obtain ⟨seed, state, equal⟩ := origin
  cases equal
  exact state.union_original_data data pairing unions powers separation hI hSources hReps hG hT

end GroundCompressionOrigin

end PartitionPilot.Forcing

end OAI
