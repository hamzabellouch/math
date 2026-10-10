import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionOrigins

namespace OAI


namespace PartitionPilot.Forcing
universe u

theorem mapFamilySection_union {D C families : Nat → ZFSet.{u}}
    {I U V allFamilies : ZFSet.{u}}
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (functions : ∀ n i f, ZFSet.pair i f ∈ families n → ZFSet.IsFunc (D n) (C n) f)
    (i : {i : ZFSet.{u} // i ∈ I}) :
    NatUnionCode (fun n => (maps n).value i)
      (indexedRelationSection U V (mapFamilyApplicationGraph I U V allFamilies) i.val) := by
  intro z
  constructor
  · intro member
    obtain ⟨x, _, y, _, rfl, entry⟩ := (mem_indexedRelationSection _ _ _ _ _).1 member
    obtain ⟨_, _, _, f, indexed, value⟩ := (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 entry
    obtain ⟨n, oldIndexed⟩ := (familyUnion _).1 indexed
    have equal := (maps n).value_eq_of_entry i oldIndexed
    refine ⟨n, ?_⟩
    change ZFSet.pair x y ∈ (maps n).value i
    rw [equal]
    exact value
  · rintro ⟨n, member⟩
    have indexed := (maps n).value_entry i
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 ((functions n i.val _ indexed).1 member)
    apply (pair_mem_indexedRelationSection _ _ _ _ _ _).2
    refine ⟨domain.subset n hx, range.subset n hy, ?_⟩
    exact (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
      ⟨i.property, domain.subset n hx, range.subset n hy, (maps n).value i,
        familyUnion.subset n indexed, member⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem exists_groundMapUnionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {D C families : Nat → ZFSet.{u}} {I U V allFamilies : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets) (hFamilies : allFamilies ∈ M.sets)
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (functions : ∀ n i f, ZFSet.pair i f ∈ families n → ZFSet.IsFunc (D n) (C n) f) :
    ∃ result ∈ M.sets, FunctionGraphOn I result ∧
      ∀ i : {i : ZFSet.{u} // i ∈ I}, ∀ f, ZFSet.pair i.val f ∈ result →
        NatUnionCode (fun n => (maps n).value i) f := by
  let flat := mapFamilyApplicationGraph I U V allFamilies
  have hFlat := M.mapFamilyApplicationGraph_mem pairing unions powers separation hI hU hV hFamilies
  obtain ⟨hResult, resultFunction, entries⟩ :=
    M.indexedRelationSections_spec pairing unions powers separation hI hU hV hFlat
  refine ⟨M.indexedRelationSections I U V flat, hResult, ⟨_, resultFunction⟩, ?_⟩
  intro i f entry
  have equal := ((entries i.val f).1 entry).2
  rw [equal]
  exact mapFamilySection_union domain range familyUnion maps functions i

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundMeetEmbeddingUnionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {D C rD rC μD μC families : Nat → ZFSet.{u}}
    {I U V RU RV MU MV allFamilies : ZFSet.{u}}
    (hI : I ∈ M.sets) (hU : U ∈ M.sets) (hV : V ∈ M.sets) (hFamilies : allFamilies ∈ M.sets)
    (domain : NatUnionCode D U) (range : NatUnionCode C V)
    (domainOrder : NatUnionCode rD RU) (rangeOrder : NatUnionCode rC RV)
    (domainMeet : NatUnionCode μD MU) (rangeMeet : NatUnionCode μC MV)
    (familyUnion : NatUnionCode families allFamilies)
    (maps : ∀ n, FunctionGraphOn I (families n))
    (embeddings : ∀ n i f, ZFSet.pair i f ∈ families n →
      MeetEmbeddingCode (D n) (C n) (rD n) (rC n) (μD n) (μC n) f)
    (mapMono : ∀ n m, n ≤ m → ∀ i f g,
      ZFSet.pair i f ∈ families n → ZFSet.pair i g ∈ families m → f ⊆ g)
    (orderMono : ∀ n m, n ≤ m → rD n ⊆ rD m)
    (meetMono : ∀ n m, n ≤ m → μD n ⊆ μD m) :
    ∃ result ∈ M.sets, FunctionGraphOn I result ∧
      ∀ i f, ZFSet.pair i f ∈ result →
        MeetEmbeddingCode U V RU RV MU MV f ∧
        (∀ z, z ∈ f ↔ ∃ n, ∃ old, ZFSet.pair i old ∈ families n ∧ z ∈ old) ∧
        ∀ n old, ZFSet.pair i old ∈ families n → ∀ x ∈ D n, ∀ y,
          ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old := by
  obtain ⟨result, hResult, resultFunction, sections⟩ :=
    M.exists_groundMapUnionFamily pairing unions powers separation hI hU hV hFamilies
      domain range familyUnion maps (fun n i f entry => (embeddings n i f entry).injection.function)
  refine ⟨result, hResult, resultFunction, ?_⟩
  intro i f entry
  have hi : i ∈ I := resultFunction.pair_source entry
  let task : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have graph := sections task f entry
  have finiteEmbedding (n : Nat) := embeddings n i _ ((maps n).value_entry task)
  have increasing : ∀ n m, n ≤ m → (maps n).value task ⊆ (maps m).value task :=
    fun n m lower => mapMono n m lower i _ _ ((maps n).value_entry task) ((maps m).value_entry task)
  have full := domain.meetEmbedding range domainOrder rangeOrder domainMeet rangeMeet
    graph finiteEmbedding increasing orderMono meetMono
  refine ⟨full, ?_, ?_⟩
  · intro z
    rw [graph z]
    constructor
    · rintro ⟨n, member⟩
      exact ⟨n, (maps n).value task, (maps n).value_entry task, member⟩
    · rintro ⟨n, old, indexed, member⟩
      have equal := (maps n).value_eq_of_entry task indexed
      refine ⟨n, ?_⟩
      change z ∈ (maps n).value task
      rw [equal]
      exact member
  · intro n old indexed x hx y
    have equal := (maps n).value_eq_of_entry task indexed
    exact (graph.function_entry_iff full.injection.function
      (fun n => (finiteEmbedding n).injection.function) n hx).trans
        (by rw [equal])

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundUnionMaps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets)
    (union : GroundCompressionUnionData M state.data I Sources Reps G m one T) :
    ∃ maps ∈ M.sets, FunctionGraphOn I maps ∧
      ∀ i f, ZFSet.pair i f ∈ maps →
        MeetEmbeddingCode (union.fields 0) (union.fields 0) (union.fields 1) (union.fields 1)
          (union.fields 2) (union.fields 2) f ∧
        (∀ z, z ∈ f ↔ ∃ n, ∃ old,
          ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps ∧ z ∈ old) ∧
        ∀ n old, ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps →
          ∀ x ∈ (state.data.iterate M I Sources Reps G T n).D, ∀ y,
            ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old := by
  have codes := state.canonical_iterate_codes pairing unions powers separation hI hSources hReps hG hT
  have mono {n k : Nat} (before : n ≤ k) :=
    state.canonical_iterate_graphs_mono pairing unions powers separation hI hSources hReps hG hT before
  exact M.exists_groundMeetEmbeddingUnionFamily pairing unions powers separation
    hI (union.ground 0) (union.ground 0) (union.ground 11)
    (union.fieldUnion 0) union.currentCarrier (union.fieldUnion 1) union.currentOrder
    (union.fieldUnion 2) union.currentMeet (union.fieldUnion 11)
    (fun n => (codes n).2.2.2.1) (fun n => (codes n).2.2.2.2)
    (fun _ _ before => (mono before).2.2.2.2.2.2.2)
    (fun _ _ before => (mono before).2.1) (fun _ _ before => (mono before).2.2.1)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing
open SetFormula
universe u

structure GroundCompressionAlgebra (M : TransitiveGround.{u}) (initial : RecursiveStateData.{u})
    (I Sources Reps G m one T : ZFSet.{u}) where
  union : GroundCompressionUnionData M initial I Sources Reps G m one T
  maps : ZFSet.{u}
  ground : maps ∈ M.sets
  function : FunctionGraphOn I maps
  embedding : ∀ i f, ZFSet.pair i f ∈ maps →
    MeetEmbeddingCode (union.fields 0) (union.fields 0) (union.fields 1) (union.fields 1)
      (union.fields 2) (union.fields 2) f
  entries : ∀ i f, ZFSet.pair i f ∈ maps → ∀ z,
    z ∈ f ↔ ∃ n, ∃ old, ZFSet.pair i old ∈ (initial.iterate M I Sources Reps G T n).Maps ∧ z ∈ old
  restrict : ∀ i f, ZFSet.pair i f ∈ maps → ∀ n old,
    ZFSet.pair i old ∈ (initial.iterate M I Sources Reps G T n).Maps →
      ∀ x ∈ (initial.iterate M I Sources Reps G T n).D, ∀ y,
        ZFSet.pair x y ∈ f ↔ ZFSet.pair x y ∈ old

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_groundAlgebra
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hG : G ∈ M.sets) (hT : T ∈ M.sets) :
    Nonempty (GroundCompressionAlgebra M state.data I Sources Reps G m one T) := by
  obtain ⟨union⟩ := state.exists_groundUnion pairing unions powers separation collection infinite
    hI hSources hReps hG hT
  obtain ⟨maps, ground, function, correct⟩ := state.exists_groundUnionMaps
    pairing unions powers separation hI hSources hReps hG hT union
  exact ⟨⟨union, maps, ground, function, fun i f entry => (correct i f entry).1,
    fun i f entry => (correct i f entry).2.1, fun i f entry => (correct i f entry).2.2⟩⟩

end GroundCompressionState

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_fresh_accounting
    (initial : FiniteCompressionAccounting P0 I Sources τ state.data) :
    ∀ x ∈ algebra.union.fields 0, x ∈ P0 ∨
      ∃ i ∈ I, ∃ f a k b, ∃ y ∈ algebra.union.fields 0,
        ZFSet.pair i f ∈ algebra.maps ∧ ZFSet.pair i a ∈ Sources ∧
        ZFSet.pair τ k ∈ f ∧ ZFSet.pair a b ∈ f ∧ ZFSet.pair y x ∈ f ∧
        ZFSet.pair x k ∈ algebra.union.fields 1 ∧ ZFSet.pair x b ∉ algebra.union.fields 1 := by
  intro x hx
  obtain ⟨n, hn⟩ := (algebra.union.currentCarrier x).1 hx
  rcases state.canonical_iterate_accounting pairing unions powers separation hI hSources hReps hG hT
    initial n x hn with original | accounted
  · exact Or.inl original
  · obtain ⟨i, hi, S, a, k, b, y, hy, indexed, source, cap, base, image, lower, outside⟩ := accounted
    obtain ⟨f, unionIndexed⟩ := algebra.function.total hi
    have finite := (state.canonical_iterate_codes pairing unions powers separation
      hI hSources hReps hG hT n).2.2.2.2 i S indexed
    have hb := (ZFSet.pair_mem_prod.1 (finite.injection.function.1 base)).2
    have reflect := algebra.union.currentOrder.order_entry_iff
      (fun _ _ before => (state.canonical_iterate_graphs_mono pairing unions powers separation
        hI hSources hReps hG hT before).2.2.2.2.1)
      (fun _ _ before => (state.canonical_iterate_coherent pairing unions powers separation
        hI hSources hReps hG hT before).currentOrder) n hn hb
    refine Or.inr ⟨i, hi, f, a, k, b, y, (algebra.union.fieldUnion 0).subset n hy,
      unionIndexed, source,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, cap⟩,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, base⟩,
      (algebra.entries i f unionIndexed _).2 ⟨n, S, indexed, image⟩,
      algebra.union.currentOrder.subset n lower, ?_⟩
    exact fun unionLower => outside (reflect.1 unionLower)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_map_equivariant {g i j f f' x y z : ZFSet.{u}}
    (transport : ZFSet.pair (ZFSet.pair g i) j ∈ T)
    (firstMap : ZFSet.pair i f ∈ algebra.maps) (secondMap : ZFSet.pair j f' ∈ algebra.maps)
    (first : ZFSet.pair x y ∈ f) (second : ZFSet.pair x z ∈ f') :
    ZFSet.pair (ZFSet.pair g y) z ∈ algebra.union.fields 12 := by
  have hx := (ZFSet.pair_mem_prod.1 ((algebra.embedding i f firstMap).injection.function.1 first)).1
  obtain ⟨n, hn⟩ := (algebra.union.fieldUnion 0 x).1 hx
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  obtain ⟨old, oldEntry⟩ := current.inputs.maps.total (algebra.function.pair_source firstMap)
  obtain ⟨old', oldEntry'⟩ := current.inputs.maps.total (algebra.function.pair_source secondMap)
  have canonicalOld : ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry
  have canonicalOld' : ZFSet.pair j old' ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry'
  have firstOld := (algebra.restrict i f firstMap n old canonicalOld x hn y).1 first
  have secondOld := (algebra.restrict j f' secondMap n old' canonicalOld' x hn z).1 second
  apply (algebra.union.fieldUnion 12).subset n
  have intertwined := current.task.intertwine g i j old old' x y z
    transport oldEntry oldEntry' firstOld secondOld
  rw [equal] at intertwined
  exact intertwined

theorem union_map_agrees_on_source {i f a g x y : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (source : ZFSet.pair i a ∈ Sources)
    (representative : ZFSet.pair i g ∈ Reps)
    (below : ZFSet.pair x a ∈ algebra.union.fields 1) :
    ZFSet.pair x y ∈ f ↔ ZFSet.pair (ZFSet.pair g x) y ∈ algebra.union.fields 12 := by
  obtain ⟨n, lower⟩ := (algebra.union.fieldUnion 1 (ZFSet.pair x a)).1 below
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have lowerCurrent : ZFSet.pair x a ∈ current.data.rD := by
    rw [equal]
    exact lower
  have hx := (ZFSet.pair_mem_prod.1 (current.batch.oldOrder.order.relation lowerCurrent)).1
  have hxCanonical : x ∈ (state.data.iterate M I Sources Reps G T n).D := by
    simpa only [equal] using hx
  obtain ⟨old, oldEntry⟩ := current.inputs.maps.total (algebra.function.pair_source map)
  have canonicalOld : ZFSet.pair i old ∈ (state.data.iterate M I Sources Reps G T n).Maps := by
    simpa only [equal] using oldEntry
  have agreement : ZFSet.pair x y ∈ old ↔
      ZFSet.pair (ZFSet.pair g x) y ∈ (state.data.iterate M I Sources Reps G T n).A := by
    simpa only [equal] using current.inputs.agreement i a g old x y
      source representative oldEntry hx lowerCurrent
  exact (algebra.restrict i f map n old canonicalOld x hxCanonical y).trans
    (agreement.trans (state.union_action_iff algebra.union pairing unions powers separation
      hI hSources hReps hG hT n (old_mem_taggedExtension hxCanonical)).symm)

end PartitionPilot.Forcing.GroundCompressionState



namespace PartitionPilot.Forcing.GroundCompressionAlgebra
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)

theorem map_eq_section {i f : ZFSet.{u}} (entry : ZFSet.pair i f ∈ algebra.maps) :
    f = indexedRelationSection (algebra.union.fields 0) (algebra.union.fields 0)
      (mapFamilyApplicationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
        (algebra.union.fields 11)) i := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1
      ((algebra.embedding i f entry).injection.function.1 hz)
    obtain ⟨n, old, indexed, oldEntry⟩ := (algebra.entries i f entry _).1 hz
    exact (pair_mem_indexedRelationSection _ _ _ _ _ _).2 ⟨hx, hy,
      (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).2
        ⟨algebra.function.pair_source entry, hx, hy, old,
          (algebra.union.fieldUnion 11).subset n indexed, oldEntry⟩⟩
  · intro hz
    obtain ⟨x, hx, y, hy, rfl, flat⟩ := (mem_indexedRelationSection _ _ _ _ _).1 hz
    obtain ⟨_, _, _, old, indexed, oldEntry⟩ :=
      (pair_mem_mapFamilyApplicationGraph _ _ _ _ _ _ _).1 flat
    obtain ⟨n, atStage⟩ := (algebra.union.fieldUnion 11 _).1 indexed
    exact (algebra.entries i f entry _).2 ⟨n, old, atStage, oldEntry⟩

theorem maps_eq_sections :
    algebra.maps = M.indexedRelationSections I (algebra.union.fields 0) (algebra.union.fields 0)
      (mapFamilyApplicationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
        (algebra.union.fields 11)) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, _, f, rfl⟩ := algebra.function.shape z hz
    exact (M.pair_mem_indexedRelationSections _ _ _ _ _ _).2
      ⟨algebra.function.pair_source hz,
        (M.mem_groundRelations _ _ _).2
          ⟨M.pair_right (M.transitive algebra.ground hz),
            (algebra.embedding i f hz).injection.function.1⟩,
        algebra.map_eq_section hz⟩
  · intro hz
    obtain ⟨_, i, hi, f, _, rfl, equal⟩ := ZFSet.mem_sep.1 hz
    obtain ⟨old, entry⟩ := algebra.function.total hi
    have same : old = f := (algebra.map_eq_section entry).trans equal.symm
    exact same ▸ entry

end PartitionPilot.Forcing.GroundCompressionAlgebra



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundCompressionAlgebra
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}

def bases (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T) : ZFSet.{u} :=
  familyEvaluationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
    (ZFSet.sUnion (ZFSet.sUnion algebra.maps)) algebra.maps Sources

noncomputable def caps (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)
    (τ : ZFSet.{u}) : ZFSet.{u} :=
  familyEvaluationGraph I (algebra.union.fields 0) (algebra.union.fields 0)
    (ZFSet.sUnion (ZFSet.sUnion algebra.maps)) algebra.maps (constantFamilyGraph I τ)

end GroundCompressionAlgebra

namespace GroundCompressionState
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)

theorem union_sources_function : ZFSet.IsFunc I (algebra.union.fields 0) Sources := by
  refine ⟨?_, seed.sources.2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (seed.sources.1 hz)
  exact ZFSet.pair_mem_prod.2 ⟨hi, state.union_original_subset algebra.union ha⟩

theorem union_top_arguments_function :
    ZFSet.IsFunc I (algebra.union.fields 0) (constantFamilyGraph I τ) := by
  refine ⟨?_, (constantFamilyGraph_function I τ).2⟩
  intro z hz
  obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 ((constantFamilyGraph_function I τ).1 hz)
  have equal := ZFSet.mem_singleton.1 ha
  subst a
  exact ZFSet.pair_mem_prod.2 ⟨hi, state.union_original_subset algebra.union seed.top_mem⟩

theorem union_bases_function : ZFSet.IsFunc I (algebra.union.fields 0) algebra.bases :=
  familyEvaluationGraph_function algebra.function.to_isFunc (state.union_sources_function algebra)
    (fun i f entry => (algebra.embedding i f entry).injection.function)

theorem union_caps_function : ZFSet.IsFunc I (algebra.union.fields 0) (algebra.caps τ) :=
  familyEvaluationGraph_function algebra.function.to_isFunc (state.union_top_arguments_function algebra)
    (fun i f entry => (algebra.embedding i f entry).injection.function)

theorem union_base_entry_iff {i f a b : ZFSet.{u}} (map : ZFSet.pair i f ∈ algebra.maps)
    (source : ZFSet.pair i a ∈ Sources) :
    ZFSet.pair i b ∈ algebra.bases ↔ ZFSet.pair a b ∈ f := by
  rw [GroundCompressionAlgebra.bases,
    familyEvaluationGraph_entry_iff algebra.function.to_isFunc (state.union_sources_function algebra) map source]
  exact ⟨fun h => h.2, fun h => ⟨(ZFSet.pair_mem_prod.1
    ((algebra.embedding i f map).injection.function.1 h)).2, h⟩⟩

theorem union_cap_entry_iff {i f k : ZFSet.{u}} (map : ZFSet.pair i f ∈ algebra.maps) :
    ZFSet.pair i k ∈ algebra.caps τ ↔ ZFSet.pair τ k ∈ f := by
  have argument := (pair_mem_constantFamilyGraph I τ i τ).2
    ⟨(ZFSet.pair_mem_prod.1 (algebra.function.to_isFunc.1 map)).1, rfl⟩
  rw [GroundCompressionAlgebra.caps,
    familyEvaluationGraph_entry_iff algebra.function.to_isFunc (state.union_top_arguments_function algebra) map argument]
  exact ⟨fun h => h.2, fun h => ⟨(ZFSet.pair_mem_prod.1
    ((algebra.embedding i f map).injection.function.1 h)).2, h⟩⟩

theorem union_markings_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) :
    algebra.bases ∈ M.sets ∧ algebra.caps τ ∈ M.sets := by
  have hValues := M.union_mem unions (M.union_mem unions algebra.ground)
  have hτ := M.transitive state.ground.carrier (state.invariant.originalSubset seed.top_mem)
  exact ⟨M.familyEvaluationGraph_mem pairing unions powers separation hI (algebra.union.ground 0)
      (algebra.union.ground 0) hValues algebra.ground hSources,
    M.familyEvaluationGraph_mem pairing unions powers separation hI (algebra.union.ground 0)
      (algebra.union.ground 0) hValues algebra.ground
      (M.constantFamilyGraph_mem pairing unions powers separation hI hτ)⟩

end GroundCompressionState
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialCompressionAlgebra
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P G r μ A Labels m inv one τ : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hτ : τ ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x τ ∈ r) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let Sources := literalTaskSourceGraph I P R U Labels
    let Filters := literalTaskFilterGraph I P R U Labels
    let T := M.groundTaskTransport P G r μ A Labels
    I ∈ M.sets ∧ Sources ∈ M.sets ∧ Filters ∈ M.sets ∧ T ∈ M.sets ∧
      ∃ Reps ∈ M.sets,
        ∃ _seed : FixedCompressionSeed P r μ A τ I Sources Reps G m inv one T Filters,
        Nonempty (GroundCompressionAlgebra M (M.initialCompressionData P G r μ A Labels)
          I Sources Reps G m one T) := by
  dsimp only
  obtain ⟨hI, hSources, hFilters, hG, hT, Reps, hReps, seed, initial, initialData⟩ :=
    M.exists_groundInitialCompressionState pairing unions powers separation choice
      hP hG hr hμ hA hLabels group action meet hτ top
  refine ⟨hI, hSources, hFilters, hT, Reps, hReps, seed, ?_⟩
  rw [← initialData]
  exact initial.exists_groundAlgebra pairing unions powers separation collection infinite
    hI hSources hReps hG hT

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)
variable (algebra : GroundCompressionAlgebra M state.data I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
variable (hG : G ∈ M.sets) (hT : T ∈ M.sets)
include pairing unions powers separation hI hSources hReps hG hT

theorem union_top {x : ZFSet.{u}} (hx : x ∈ algebra.union.fields 0) :
    ZFSet.pair x τ ∈ algebra.union.fields 1 := by
  obtain ⟨n, hn⟩ := (algebra.union.fieldUnion 0 x).1 hx
  obtain ⟨current, equal⟩ := state.canonical_iterate_valid pairing unions powers separation
    hI hSources hReps hG hT n
  have hxCurrent : x ∈ current.data.D := by
    rw [equal]
    exact hn
  apply (algebra.union.fieldUnion 1).subset n
  have belowTop := current.invariant.top x hxCurrent
  rw [equal] at belowTop
  exact belowTop

theorem union_map_base_filling {i f a g b x : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (source : ZFSet.pair i a ∈ Sources)
    (representative : ZFSet.pair i g ∈ Reps) (base : ZFSet.pair a b ∈ f)
    (hx : x ∈ algebra.union.fields 0) (below : ZFSet.pair x b ∈ algebra.union.fields 1) :
    ∃ y ∈ algebra.union.fields 0, ZFSet.pair y x ∈ f := by
  have hg := (ZFSet.pair_mem_prod.1 (state.inputs.representatives.1 representative)).2
  have ha := (ZFSet.pair_mem_prod.1 ((algebra.embedding i f map).injection.function.1 base)).1
  have actedBase := (state.union_map_agrees_on_source algebra pairing unions powers separation
    hI hSources hReps hG hT map source representative (algebra.union.meet.order.refl a ha)).1 base
  obtain ⟨y, hy, acted⟩ := algebra.union.action.raw_preimage state.inputs.group hg hx
  have belowSource := (algebra.union.action.raw_order_iff state.inputs.group
    algebra.union.meet.order hg acted actedBase).1 below
  exact ⟨y, hy, (state.union_map_agrees_on_source algebra pairing unions powers separation
    hI hSources hReps hG hT map source representative belowSource).2 acted⟩

theorem union_map_range_below_cap {i f k x y : ZFSet.{u}}
    (map : ZFSet.pair i f ∈ algebra.maps) (cap : ZFSet.pair τ k ∈ f)
    (image : ZFSet.pair x y ∈ f) : ZFSet.pair y k ∈ algebra.union.fields 1 := by
  have embedding := algebra.embedding i f map
  have hx := (ZFSet.pair_mem_prod.1 (embedding.injection.function.1 image)).1
  exact embedding.monotone x τ y k
    (state.union_top algebra pairing unions powers separation hI hSources hReps hG hT hx) image cap

end PartitionPilot.Forcing.GroundCompressionState

end OAI
