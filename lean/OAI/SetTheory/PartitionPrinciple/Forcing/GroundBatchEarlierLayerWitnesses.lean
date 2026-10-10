import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCompressionBirthData

namespace OAI

namespace PartitionPilot.Forcing

section
open SetFormula
universe u

theorem CountableLayerCode.of_literal_extension
    {A B old born t D N injection : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    CountableLayerCode B born t D N injection :=
  ⟨code.small, fun x hx entry => code.cover x (fiber x hx entry).1 (fiber x hx entry).2⟩

theorem CopyLayerCode.of_literal_extension
    {Qs rs μs A B rA rB μA μB old born t I parts Indices Maps W N injection : ZFSet.{u}}
    (code : CopyLayerCode Qs rs μs A rA μA old t I parts Indices Maps W N injection)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    CopyLayerCode Qs rs μs B rB μB born t I
      (ZFSet.sep (fun p => p ∈ ZFSet.prod I A) parts) Indices Maps W N injection := by
  refine ⟨code.small, code.indices, code.maps, ?_, ?_, ?_⟩
  · intro i hi s hs e P R V index map qField rField mField
    exact (code.embedding i hi s hs e P R V index map qField rField mField).enlarge_target
      carrier order meets
  · intro x hx entry
    have retained := fiber x hx entry
    obtain ⟨i, hi, part⟩ := code.cover x retained.1 retained.2
    exact ⟨i, hi, ZFSet.mem_sep.2 ⟨part, ZFSet.pair_mem_prod.2 ⟨hi, retained.1⟩⟩⟩
  · intro i hi s hs e P x _ index map qField part
    have retained := ZFSet.mem_sep.1 part
    exact relationImage_enlarge_target carrier
      (code.inCopy i hi s hs e P x (ZFSet.pair_mem_prod.1 retained.2).2 index map qField retained.1)

theorem SeparatedLayerCode.of_literal_extension
    {Qs rs μs A B rA rB μA μB old born t I Indices Maps W Components F : ZFSet.{u}}
    (code : SeparatedLayerCode Qs rs μs A rA μA old t I Indices Maps W Components F)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB) (births : old ⊆ born)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    SeparatedLayerCode Qs rs μs B rB μB born t I Indices Maps W Components F := by
  refine ⟨code.indices, code.maps, ?_, code.components, ?_, ?_, ?_⟩
  · rw [code.fiber]
    apply ZFSet.ext
    intro x
    rw [mem_layerBirthFiber, mem_layerBirthFiber]
    exact ⟨fun h => ⟨carrier h.1, births h.2⟩, fun h => fiber x h.1 h.2⟩
  · intro i hi s hs e P R V index map qField rField mField
    exact (code.embedding i hi s hs e P R V index map qField rField mField).enlarge_target
      carrier order meets
  · intro i hi s hs e P x _ index map qField component
    have inF := (ZFSet.pair_mem_prod.1 (code.components.1 component)).1
    have hx : x ∈ A := ((mem_layerBirthFiber A old t x).1 (code.fiber ▸ inF)).1
    exact relationImage_enlarge_target carrier (code.cover i hi s hs e P x hx index map qField component)
  · intro x hx y hy i hi j hj first second different
    exact (code.separated x hx y hy i hi j hj first second different).of_literal_extension
      carrier order meets births

namespace GrowthLayerWitnessCode

theorem exists_literal_extension {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hz : z ∈ M.sets)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB) (births : old ⊆ born)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' := by
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · exact ⟨countableLayerWitness D injection, hz, Or.inl ⟨D, injection, rfl, code.of_literal_extension fiber⟩⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    let retained := ZFSet.sep (fun p => p ∈ ZFSet.prod I A) parts
    have ground : retained ∈ M.sets := M.injection_restriction_mem separation (fields 1) hA (fields 2)
    exact ⟨copyLayerWitness I retained Indices Maps W injection,
      M.copyLayerWitness_mem pairing unions (fields 1) ground (fields 3) (fields 4) (fields 5) (fields 6),
      Or.inr (Or.inl ⟨I, retained, Indices, Maps, W, injection, rfl,
        code.of_literal_extension carrier order meets fiber⟩)⟩
  · exact ⟨separatedLayerWitness I Indices Maps W Components F, hz,
      Or.inr (Or.inr ⟨I, Indices, Maps, W, Components, F, rfl,
        code.of_literal_extension carrier order meets births fiber⟩)⟩

end GrowthLayerWitnessCode

theorem GrowthLayerWitnessCode.exists_fixedTop_earlier {M : TransitiveGround.{u}}
    {Qs rs μs P r μ T birth s t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs P r μ birth t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hz : z ∈ M.sets)
    (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth) (before : t ∈ s) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t N z' := by
  apply code.exists_literal_extension pairing unions separation hP hz
    (fixedTopCarrier_subset P) (fixedTopOrder_subset P r) (fixedTopMeet_subset meet)
    (fixedTopBirth_subset P birth s)
  intro x _ entry
  have old := (fixedTopBirth_earlier_iff before).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩

noncomputable def fixedTopLayerWitness (P : ZFSet.{u}) : ZFSet.{u} :=
  countableLayerWitness {P} {ZFSet.pair P ∅}

theorem fixedTopLayerWitness_code {Qs rs μs P r birth s : ZFSet.{u}}
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s) :
    GrowthLayerWitnessCode Qs rs μs (fixedTopCarrier P) (fixedTopOrder P r)
      (fixedTopMeet P r) (fixedTopBirth P birth s) s ZFSet.omega (fixedTopLayerWitness P) := by
  refine Or.inl ⟨{P}, {ZFSet.pair P ∅}, rfl, fixedTopBirth_singleton_injection P, ?_⟩
  intro x _ entry
  exact ZFSet.mem_singleton.2 ((fixedTopBirth_new_time_iff earlier).1 entry)

theorem TransitiveGround.fixedTopLayerWitness_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : fixedTopLayerWitness P ∈ M.sets := by
  have singleton (x : ZFSet.{u}) (hx : x ∈ M.sets) : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.countableLayerWitness_mem pairing (singleton P hP)
    (singleton _ (M.orderedPair_mem pairing hP (M.empty_mem ⟨P, hP⟩)))

end

namespace GrowthLayerWitnessCode
open SetFormula
universe u

theorem exists_literal_extension_rank_lt {M : TransitiveGround.{u}}
    {Qs rs μs A B rA rB μA μB old born t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (carrier : A ⊆ B) (order : rA ⊆ rB) (meets : μA ⊆ μB) (births : old ⊆ born)
    (fiber : ∀ x ∈ B, ZFSet.pair x t ∈ born → x ∈ A ∧ ZFSet.pair x t ∈ old) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' ∧
      ZFSet.rank z' < o := by
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · exact ⟨countableLayerWitness D injection, hz,
      Or.inl ⟨D, injection, rfl, code.of_literal_extension fiber⟩, rank⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    let retained := ZFSet.sep (fun p => p ∈ ZFSet.prod I A) parts
    have ground : retained ∈ M.sets :=
      M.injection_restriction_mem separation (fields 1) hA (fields 2)
    have retainedRank : ZFSet.rank retained < o :=
      (ZFSet.rank_mono (show retained ⊆ parts from fun _ hp => (ZFSet.mem_sep.1 hp).1)).trans_lt (ranks 2)
    exact ⟨copyLayerWitness I retained Indices Maps W injection,
      M.copyLayerWitness_mem pairing unions (fields 1) ground (fields 3) (fields 4) (fields 5) (fields 6),
      Or.inr (Or.inl ⟨I, retained, Indices, Maps, W, injection, rfl,
        code.of_literal_extension carrier order meets fiber⟩),
      copyLayerWitness_rank_lt limit (ranks 1) retainedRank (ranks 3) (ranks 4) (ranks 5) (ranks 6)⟩
  · exact ⟨separatedLayerWitness I Indices Maps W Components F, hz,
      Or.inr (Or.inr ⟨I, Indices, Maps, W, Components, F, rfl,
        code.of_literal_extension carrier order meets births fiber⟩), rank⟩

end GrowthLayerWitnessCode

section
open SetFormula SetRealization
universe u

theorem GrowthLayerWitnessCode.exists_fixedTop_earlier_rank_lt
    {M : TransitiveGround.{u}} {Qs rs μs P r μ T birth s t N z : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs P r μ birth t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (meet : MeetOrderCode P r μ) (born : ZFSet.IsFunc P T birth) (before : t ∈ s) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs (fixedTopCarrier P)
      (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t N z' ∧
      ZFSet.rank z' < o := by
  apply code.exists_literal_extension_rank_lt pairing unions separation hP hz limit rank
    (fixedTopCarrier_subset P) (fixedTopOrder_subset P r) (fixedTopMeet_subset meet)
    (fixedTopBirth_subset P birth s)
  intro x _ entry
  have old := (fixedTopBirth_earlier_iff before).1 entry
  exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩

theorem fixedTopLayerWitness_rank_lt {P : ZFSet.{u}} {o : Ordinal.{u}}
    (limit : Order.IsSuccLimit o) (points : ZFSet.rank P < o) :
    ZFSet.rank (fixedTopLayerWitness P) < o :=
  countableLayerWitness_rank_lt limit (rank_singleton_lt limit points)
    (rank_singleton_lt limit (rank_orderedPair_lt limit points
      (by simpa only [ZFSet.rank_empty] using limit.pos)))

end

namespace AttachmentBatchInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P r μ I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P r μ I Qs rs μs As Es Fs Ss)

theorem exists_batchEarlierLayerWitness
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    {HQs Hrs Hμs T birth stamp t N z : ZFSet.{u}} (hP : P ∈ M.sets) (hz : z ∈ M.sets)
    (born : ZFSet.IsFunc P T birth) (before : t ∈ stamp)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs P r μ birth t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      d.batchCarrier d.batchOrder d.batchMeetGraph (d.batchBirth birth stamp) t N z' := by
  have meetSubset : μ ⊆ d.batchMeetGraph := by
    intro z hz
    obtain ⟨xy, hxy, v, hv, rfl⟩ := ZFSet.mem_prod.1 (d.oldOrder.operation.1 hz)
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hxy
    exact d.old_meet_entry hz
  apply code.exists_literal_extension pairing unions separation hP hz
    (fun _ => old_mem_taggedExtension) ?_ meetSubset (taggedBirth_subset _ _ _ _)
  · intro x _ entry
    have old := (taggedBirth_earlier_iff before).1 entry
    exact ⟨(ZFSet.pair_mem_prod.1 (born.1 old)).1, old⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (d.oldOrder.order.relation hz)
    exact (d.old_order_iff hx hy).2 hz

end AttachmentBatchInputs

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old HQs Hrs Hμs t N z : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include pairing unions powers separation hI hSources hReps hG hT limit

theorem exists_birthWitness_to_finite_rank_lt (n k : Nat) (before : n ≤ k)
    (earlier : t ∈ compressionStamp base n) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' ∧ ZFSet.rank z' < o := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have growth := state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT before
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension_rank_lt pairing unions separation ground hz limit rank growth.1 growth.2.1 growth.2.2.1
    (NatBirthExtensionCode.restriction_mono mono before)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n earlier
      (pair_mem_graphRestriction.1 entry).1)

theorem exists_birthWitness_to_union_rank_lt (n : Nat) (before : t ∈ compressionStamp base n)
    (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' ∧ ZFSet.rank z' < o := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension_rank_lt pairing unions separation ground hz limit rank
    ((data.fieldUnion 0).subset n) ((data.fieldUnion 1).subset n) ((data.fieldUnion 2).subset n)
    (graphRestriction_subset (state.data.iterate M I Sources Reps G T n).D births.birth)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n before entry)

theorem exists_priorWitness_to_finite_rank_lt (k : Nat) (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' ∧ ZFSet.rank z' < o := by
  apply state.exists_birthWitness_to_finite_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
    0 k (Nat.zero_le k) (compressionStamp_old_mem before 0) hz rank
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

theorem exists_priorWitness_to_union_rank_lt (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets) (rank : ZFSet.rank z < o)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' ∧ ZFSet.rank z' < o := by
  apply state.exists_birthWitness_to_union_rank_lt data births pairing unions powers separation hI hSources hReps hG hT limit
    0 (compressionStamp_old_mem before 0) hz rank
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

omit unions powers separation hI hSources hReps hG hT in
theorem exists_limitWitness_rank_lt :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth births.limit N z ∧ ZFSet.rank z < o := by
  have hEmpty := M.empty_mem ⟨data.fields 0, data.ground 0⟩
  exact ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
    Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty N, fun x _ entry => (births.no_limit_birth x entry).elim⟩⟩,
    countableLayerWitness_rank_lt limit (by simpa only [ZFSet.rank_empty] using limit.pos)
      (by simpa only [ZFSet.rank_empty] using limit.pos)⟩

end GroundCompressionState

namespace GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (data : GroundCompressionUnionData M state.data I Sources Reps G m one T)
variable {base old HQs Hrs Hμs t N z : ZFSet.{u}}
variable (births : GroundCompressionBirthData M state.data I Sources Reps G m one T data base old)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem exists_birthWitness_to_finite (n k : Nat) (before : n ≤ k)
    (earlier : t ∈ compressionStamp base n) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  have growth := state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT before
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension pairing unions separation ground hz growth.1 growth.2.1 growth.2.2.1
    (NatBirthExtensionCode.restriction_mono mono before)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n earlier
      (pair_mem_graphRestriction.1 entry).1)

theorem exists_birthWitness_to_union (n : Nat) (before : t ∈ compressionStamp base n)
    (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T n).D
      (state.data.iterate M I Sources Reps G T n).rD
      (state.data.iterate M I Sources Reps G T n).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T n).D births.birth) t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' := by
  have mono := fun n k h => (state.canonical_iterate_graphs_mono pairing unions powers separation
    hI hSources hReps hG hT (n := n) (k := k) h).1
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have ground : (state.data.iterate M I Sources Reps G T n).D ∈ M.sets := equal ▸ current.ground.carrier
  exact code.exists_literal_extension pairing unions separation ground hz
    ((data.fieldUnion 0).subset n) ((data.fieldUnion 1).subset n) ((data.fieldUnion 2).subset n)
    (graphRestriction_subset (state.data.iterate M I Sources Reps G T n).D births.birth)
    (fun _ _ entry => births.extension.earlier_fiber mono births.initial_function
      (fun _ _ h => compressionStamp_subset base h) n before entry)

theorem exists_priorWitness_to_finite (k : Nat) (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (state.data.iterate M I Sources Reps G T k).D
      (state.data.iterate M I Sources Reps G T k).rD
      (state.data.iterate M I Sources Reps G T k).μD
      (graphRestriction (state.data.iterate M I Sources Reps G T k).D births.birth) t N z' := by
  apply state.exists_birthWitness_to_finite data births pairing unions powers separation hI hSources hReps hG hT
    0 k (Nat.zero_le k) (compressionStamp_old_mem before 0) hz
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

theorem exists_priorWitness_to_union (before : t ∈ base ∨ t = base) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode HQs Hrs Hμs state.data.D state.data.rD state.data.μD old t N z) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth t N z' := by
  apply state.exists_birthWitness_to_union data births pairing unions powers separation hI hSources hReps hG hT
    0 (compressionStamp_old_mem before 0) hz
  simpa only [RecursiveStateData.iterate_zero, births.original] using code

omit unions powers separation hI hSources hReps hG hT in
theorem exists_limitWitness :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode HQs Hrs Hμs
      (data.fields 0) (data.fields 1) (data.fields 2) births.birth births.limit N z := by
  have hEmpty := M.empty_mem ⟨data.fields 0, data.ground 0⟩
  exact ⟨countableLayerWitness ∅ ∅, M.countableLayerWitness_mem pairing hEmpty hEmpty,
    Or.inl ⟨∅, ∅, rfl, ⟨InjectionCode.empty N, fun x _ entry => (births.no_limit_birth x entry).elim⟩⟩⟩

end GroundCompressionState

end PartitionPilot.Forcing

end OAI
