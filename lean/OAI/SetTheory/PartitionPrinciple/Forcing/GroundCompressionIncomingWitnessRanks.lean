import OAI.SetTheory.PartitionPrinciple.Geometry.GroundConstantBatchLayers
import OAI.SetTheory.PartitionPrinciple.Transfinite.CompressionPrefixCoinitiality

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchLayerWitness
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one HQs Hrs Hμs HTime T birth stamp τ N : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hStamp : stamp ∈ M.sets) (before : τ ∈ stamp)
    (source : ZFSet.pair τ P ∈ HQs ∧ ZFSet.pair τ r ∈ Hrs ∧ ZFSet.pair τ μ ∈ Hμs) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    d.constantBatchLayerWitness M τ ∈ M.sets ∧
      GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
        (d.batchBirth birth stamp) stamp N (d.constantBatchLayerWitness M τ) := by
  let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
  have fields := M.groundEligibleTaskFields pairing unions powers separation hP hG hr hμ hA hLabels meet
  apply d.constantBatchLayerWitness_spec pairing unions powers separation hP fields.1 fields.2.1
    fields.2.2.1 (fields.2.2.2.2 0).1 (fields.2.2.2.2 2).1
    historySpaces historyOrders historyMeets born earlier hStamp before ?_ source
  intro i
  exact ⟨((pair_mem_constantFamilyGraph _ _ _ _).1 (d.space_entry i)).2,
    ((pair_mem_constantFamilyGraph _ _ _ _).1 (d.rel_entry i)).2,
    ((pair_mem_constantFamilyGraph _ _ _ _).1 (d.meet_entry i)).2⟩

end TransitiveGround

section
open SetRealization
universe u

theorem batchFamilyPointBound_rank_le (Qs : ZFSet.{u}) :
    ZFSet.rank (familyPointBound Qs) ≤ ZFSet.rank Qs :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem batchTemplateFamilyBound_rank_lt {I P Qs : ZFSet.{u}} (rs As : ZFSet.{u})
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) :
    ZFSet.rank (M.batchTemplateFamilyBound I P Qs rs As) < o := by
  have source := (batchFamilyPointBound_rank_le Qs).trans_lt spaces
  have fresh := (ZFSet.rank_mono (fun z hz => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hz))).trans_lt (rank_product_lt limit indices source)
  exact M.groundRelations_rank_lt limit source (rank_taggedExtension_lt limit points fresh)

theorem batchTemplateFamily_rank_lt {I P Qs : ZFSet.{u}} (rs As Es : ZFSet.{u})
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) :
    ZFSet.rank (M.batchTemplateFamily I P Qs rs As Es) < o := by
  have subset : M.batchTemplateFamily I P Qs rs As Es ⊆
      ZFSet.prod I (M.batchTemplateFamilyBound I P Qs rs As) := by
    intro z hz
    unfold batchTemplateFamily indexedRelationSections at hz
    exact (ZFSet.mem_sep.1 hz).1
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit indices
    (M.batchTemplateFamilyBound_rank_lt limit rs As points indices spaces))

end TransitiveGround

namespace AttachmentBatchInputs
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem batchIncomingFiber_rank_lt
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) : ZFSet.rank d.batchIncomingFiber < o := by
  have fresh := (ZFSet.rank_mono (fun z hz => indexedAttachmentDomain_subset I Qs
    (indexedAttachmentFresh_subset I Qs rs As hz))).trans_lt
      (rank_product_lt limit indices ((batchFamilyPointBound_rank_le Qs).trans_lt spaces))
  exact rank_product_lt limit (rank_singleton_lt limit points) fresh

theorem constantBatchLayerWitness_rank_lt (M : TransitiveGround.{u}) {τ : ZFSet.{u}}
    (points : ZFSet.rank P < o) (indices : ZFSet.rank I < o)
    (spaces : ZFSet.rank Qs < o) (time : ZFSet.rank τ < o) :
    ZFSet.rank (d.constantBatchLayerWitness M τ) < o := by
  have fiber := d.batchIncomingFiber_rank_lt limit points indices spaces
  exact separatedLayerWitness_rank_lt limit indices
    (rank_constantFamilyGraph_lt limit indices time)
    (M.batchTemplateFamily_rank_lt limit rs As Es points indices spaces)
    (M.batchTemplateFamilyBound_rank_lt limit rs As points indices spaces)
    (rank_functionGraph_lt limit d.batchIncomingComponents_function fiber indices) fiber

end AttachmentBatchInputs

end

namespace TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem groundEligibleBatchLayerWitness_rank_lt
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank P < o) (labels : ZFSet.rank Labels < o)
    (time : ZFSet.rank τ < o) :
    ZFSet.rank ((M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).constantBatchLayerWitness M τ) < o := by
  have tasks := M.groundEligibleTasks_rank_lt limit G r μ A points labels
  exact (M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet).constantBatchLayerWitness_rank_lt
    limit M points tasks (rank_constantFamilyGraph_lt limit tasks points) time

theorem groundEligibleBatchLayerWitness_ranked
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one HQs Hrs Hμs HTime T birth stamp τ N : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ)
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (born : ZFSet.IsFunc P T birth)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ stamp)
    (hStamp : stamp ∈ M.sets) (before : τ ∈ stamp)
    (source : ZFSet.pair τ P ∈ HQs ∧ ZFSet.pair τ r ∈ Hrs ∧ ZFSet.pair τ μ ∈ Hμs)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (points : ZFSet.rank P < o)
    (labels : ZFSet.rank Labels < o) (time : ZFSet.rank τ < o) :
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    d.constantBatchLayerWitness M τ ∈ M.sets ∧
      ZFSet.rank (d.constantBatchLayerWitness M τ) < o ∧
      GrowthLayerWitnessCode HQs Hrs Hμs d.batchCarrier d.batchOrder d.batchMeetGraph
        (d.batchBirth birth stamp) stamp N (d.constantBatchLayerWitness M τ) := by
  have code := M.groundEligibleBatchLayerWitness pairing unions powers separation hP hG hr hμ hA hLabels
    group action meet historySpaces historyOrders historyMeets born earlier hStamp before source (N := N)
  exact ⟨code.1, M.groundEligibleBatchLayerWitness_rank_lt group action meet limit points labels time, code.2⟩

end TransitiveGround

namespace GroundCompressionState
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)

theorem exists_canonicalIncomingRankedWitness
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {HQs Hrs Hμs HTime N : ZFSet.{u}}
    (historySpaces : FunctionGraphOn HTime HQs)
    (historyOrders : FunctionGraphOn HTime Hrs)
    (historyMeets : FunctionGraphOn HTime Hμs)
    (source : ZFSet.pair base P0 ∈ HQs ∧ ZFSet.pair base r0 ∈ Hrs ∧ ZFSet.pair base μ0 ∈ Hμs)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (points : ZFSet.rank state.data.D < o) (indices : ZFSet.rank state.data.J < o)
    (templates : ZFSet.rank P0 < o) (tasks : ZFSet.rank I < o)
    (time : ZFSet.rank base < o) (n : Nat) :
    ∃ z ∈ M.sets, ZFSet.rank z < o ∧ GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T (n + 1)).D
      (state.data.iterate M I Sources Reps G T (n + 1)).rD
      (state.data.iterate M I Sources Reps G T (n + 1)).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T (n + 1)).D births.birth)
      (compressionStamp base n) N z := by
  let current := state.iterate pairing unions powers separation hI hSources hReps hG hT n
  have equal : current.data = state.data.iterate M I Sources Reps G T n :=
    state.iterate_data pairing unions powers separation hI hSources hReps hG hT n
  have currentConstant : RecursiveTemplateConstancy P0 r0 μ0 current.data := by
    simpa only [equal] using constant.iterate M I Sources Reps G T n
  have finite : ZFSet.IsFunc current.data.D births.limit
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) := by
    simpa only [equal] using state.canonical_birth_function data pairing unions powers separation
      hI hSources hReps hG hT births.extension births.initial_function births.times n
  have earlier : ∀ x t, ZFSet.pair x t ∈
      graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth →
      t ∈ compressionStamp base n := fun _ _ entry =>
    state.canonical_birth_before_stamp pairing unions powers separation hI hSources hReps hG hT
      births.extension births.initial_bound n entry
  have result := current.batch.constantBatchLayerWitness_spec pairing unions powers separation
    current.ground.carrier current.ground.indices current.ground.spaces current.ground.relations
    current.ground.anchors current.ground.embeddings historySpaces historyOrders historyMeets finite earlier
    (M.transitive births.limit_ground (births.times.stamp_mem_limit n)) (compressionStamp_base_mem base n)
    (fun i => ⟨((currentConstant.space_entry_iff _ _).1 (current.batch.space_entry i)).2,
      ((currentConstant.relation_entry_iff _ _).1 (current.batch.rel_entry i)).2,
      ((currentConstant.meet_entry_iff _ _).1 (current.batch.meet_entry i)).2⟩) source (N := N)
  have finiteRanks := constant.iterate_carrier_ranks M I Sources Reps G T limit
    points indices templates tasks n
  have pointRank : ZFSet.rank current.data.D < o := by simpa only [equal] using finiteRanks.1
  have indexRank : ZFSet.rank current.data.J < o := by simpa only [equal] using finiteRanks.2
  have spaceRank : ZFSet.rank current.data.Qs < o := by
    rw [currentConstant.spaces]
    exact rank_constantFamilyGraph_lt limit indexRank templates
  have witnessRank := current.batch.constantBatchLayerWitness_rank_lt limit M
    pointRank indexRank spaceRank time
  refine ⟨current.batch.constantBatchLayerWitness M base, result.1, witnessRank, ?_⟩
  have code := result.2
  change GrowthLayerWitnessCode HQs Hrs Hμs current.data.currentCarrier
    current.data.currentOrder current.data.currentMeet
    (taggedBirth current.data.D current.data.fresh
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth)
      (compressionStamp base n)) (compressionStamp base n) N _ at code
  rw [state.canonical_birth_step pairing unions powers separation hI hSources hReps hG hT
    births.extension births.initial_function n]
  simpa only [equal, RecursiveStateData.iterate_succ, RecursiveStateData.successor] using code

end GroundCompressionState

end PartitionPilot.Forcing

end OAI
