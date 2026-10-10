import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLayerSourceCongruence
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainPrefixLimitChronologyCore

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

theorem familyPointBound_rank_le (Qs : ZFSet.{u}) :
    ZFSet.rank (familyPointBound Qs) ≤ ZFSet.rank Qs :=
  (ZFSet.rank_sUnion_le _).trans ((ZFSet.rank_sUnion_le _).trans (ZFSet.rank_sUnion_le _))

namespace CountableLayerCode

theorem ground_pushforward_rank_lt
    {M : TransitiveGround.{u}} {A B old born t D N injection e : ZFSet.{u}}
    (code : CountableLayerCode A old t D N injection)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (he : e ∈ M.sets)
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o)
    (embedding : InjectionCode A B e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ D' ∈ M.sets, ∃ injection' ∈ M.sets, CountableLayerCode B born t D' N injection' ∧
      ZFSet.rank D' < o ∧ ZFSet.rank injection' < o := by
  obtain ⟨E, hE, f, hf, copied⟩ := code.ground_pushforward pairing unions powers separation
    hA hB hN he hD hInjection embedding preserves noNew
  let D' := ZFSet.sep (fun x => x ∈ B) E
  let f' := ZFSet.sep (fun z => z ∈ ZFSet.prod D' N) f
  have hD' : D' ∈ M.sets := M.bounded_separation_mem separation (.mem 0 1)
    (extend B Fin.elim0) (Fin.cases hB (fun i => Fin.elim0 i)) hE
  have hf' : f' ∈ M.sets := M.injection_restriction_mem separation hD' hN hf
  have injected : InjectionCode D' N f' :=
    copied.small.restrict (fun _ hx => (ZFSet.mem_sep.1 hx).1)
  have rankD : ZFSet.rank D' < o :=
    (ZFSet.rank_mono (show D' ⊆ B from fun _ hx => (ZFSet.mem_sep.1 hx).2)).trans_lt target
  refine ⟨D', hD', f', hf', ⟨injected, ?_⟩, rankD,
    rank_functionGraph_lt limit injected.function rankD numbers⟩
  intro x hx entry
  exact ZFSet.mem_sep.2 ⟨copied.cover x hx entry, hx⟩
end CountableLayerCode

namespace GrowthLayerWitnessCode

theorem ground_pushforward_rank_lt
    {M : TransitiveGround.{u}} {Qs rs μs A B rA rB μA μB old born t N z e : ZFSet.{u}}
    (code : GrowthLayerWitnessCode Qs rs μs A rA μA old t N z)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (sourceGraphs : ZFSet.rank Qs < o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o)
    (source : MeetOrderCode A rA μA) (embedding : MeetEmbeddingCode A B rA rB μA μB e)
    (preserves : ∀ x y a, ZFSet.pair x y ∈ e →
      (ZFSet.pair y a ∈ born ↔ ZFSet.pair x a ∈ old))
    (noNew : ∀ y ∈ B, ZFSet.pair y t ∈ born → ∃ x ∈ A, ZFSet.pair x y ∈ e) :
    ∃ z' ∈ M.sets, GrowthLayerWitnessCode Qs rs μs B rB μB born t N z' ∧
      ZFSet.rank z' < o := by
  have rankU := (familyPointBound_rank_le Qs).trans_lt sourceGraphs
  have rankW := M.groundRelations_rank_lt limit rankU target
  rcases code with ⟨D, injection, rfl, code⟩ |
    ⟨I, parts, Indices, Maps, W, injection, rfl, code⟩ |
    ⟨I, Indices, Maps, W, Components, F, rfl, code⟩
  · have fields := M.nonemptyTupleCode_field_mem 2 _ hz
    obtain ⟨D', hD', injection', hInjection', copied, rankD, rankInjection⟩ :=
      code.ground_pushforward_rank_lt pairing unions powers separation hA hB hN he
        (fields 1) (fields 2) limit target numbers embedding.injection preserves noNew
    exact ⟨countableLayerWitness D' injection', M.countableLayerWitness_mem pairing hD' hInjection',
      Or.inl ⟨D', injection', rfl, copied⟩,
      countableLayerWitness_rank_lt limit rankD rankInjection⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    obtain ⟨hMaps', hW', hParts', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 2) (fields 4)
      embedding preserves noNew
    have rankMaps := rank_functionGraph_lt limit copied.maps (ranks 1) rankW
    have rankParts : ZFSet.rank (relationCompose I A B parts e) < o :=
      (ZFSet.rank_mono (show relationCompose I A B parts e ⊆ ZFSet.prod I B from
        fun _ hx => (ZFSet.mem_sep.1 hx).1)).trans_lt (rank_product_lt limit (ranks 1) target)
    exact ⟨copyLayerWitness I (relationCompose I A B parts e) Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B) injection,
      M.copyLayerWitness_mem pairing unions (fields 1) hParts' (fields 3) hMaps' hW' (fields 6),
      Or.inr (Or.inl ⟨I, _, Indices, _, _, injection, rfl, copied⟩),
      copyLayerWitness_rank_lt limit (ranks 1) rankParts (ranks 3) rankMaps rankW (ranks 6)⟩
  · have fields := M.nonemptyTupleCode_field_mem 6 _ hz
    have ranks := fun j => (rank_nonemptyTupleCode_field_le 6 _ j).trans_lt rank
    obtain ⟨hMaps', hW', hComponents', hF', copied⟩ := code.ground_pushforward
      pairing unions powers separation hA hB he hQs (fields 1) (fields 3) (fields 5) (fields 6)
      source embedding preserves noNew
    have rankMaps := rank_functionGraph_lt limit copied.maps (ranks 1) rankW
    have rankF : ZFSet.rank (relationImage F B (layerFiberEmbedding F B e)) < o :=
      (ZFSet.rank_mono (show relationImage F B (layerFiberEmbedding F B e) ⊆ B from
        fun _ hx => ((mem_relationImage _ _ _ _).1 hx).1)).trans_lt target
    have rankComponents := rank_functionGraph_lt limit copied.components rankF (ranks 1)
    exact ⟨separatedLayerWitness I Indices
        (M.mapFamilyPushforward I (familyPointBound Qs) A B Maps e)
        (M.groundRelations (familyPointBound Qs) B)
        (pushedHeightGraph F B I (layerFiberEmbedding F B e) Components)
        (relationImage F B (layerFiberEmbedding F B e)),
      M.separatedLayerWitness_mem pairing unions (fields 1) (fields 2) hMaps' hW' hComponents' hF',
      Or.inr (Or.inr ⟨I, Indices, _, _, _, _, rfl, copied⟩),
      separatedLayerWitness_rank_lt limit (ranks 1) (ranks 2) rankMaps rankW rankComponents rankF⟩

end GrowthLayerWitnessCode

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P0 r0 μ0 A0 oldTimes oldBirth : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
local notation "U" => completion.algebra.union.fields 0
local notation "B" => completion.externalPointCarrier P0 r0 μ0 A0
local notation "E" => completion.externalIdentityCopyGraph P0 r0 μ0 A0
include births data group action pairing unions powers separation infinite hG hP0

theorem ranked_rawPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank z < o) (sourceGraphs : ZFSet.rank Qs < o)
    (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o) :
    ∃ z' ∈ M.sets, ZFSet.rank z' < o ∧ GrowthLayerWitnessCode Qs rs μs B
      (completion.externalPointOrder P0 r0 μ0 A0) (completion.externalPointMeet P0 r0 μ0 A0)
      births.birth t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  obtain ⟨z', hz', code', rank'⟩ := code.ground_pushforward_rank_lt pairing unions powers separation
    (completion.algebra.union.ground 0) geometry.carrier_ground
    (geometry.copies_ground _ data.group.group_code.identity_mem) hQs hN hz
    limit rank sourceGraphs target numbers completion.algebra.union.meet embedding.toMeetEmbeddingCode
    (fun x y a copied => births.preserves_seed x y a copied)
    (fun _ _ entry => births.priorFiber_image oldTime entry)
  exact ⟨z', hz', rank', code'⟩

theorem ranked_rawCutoffPriorWitness {Qs rs μs t N z : ZFSet.{u}}
    (hQs : Qs ∈ M.sets) (hN : N ∈ M.sets) (hz : z ∈ M.sets)
    (code : GrowthLayerWitnessCode Qs rs μs U (completion.algebra.union.fields 1)
      (completion.algebra.union.fields 2) oldBirth t N z)
    (oldTime : t ∈ oldTimes ∨ t = oldTimes) (n : Nat)
    {o : Ordinal.{u}} (limit : Order.IsSuccLimit o) (rank : ZFSet.rank z < o)
    (sourceGraphs : ZFSet.rank Qs < o) (target : ZFSet.rank B < o) (numbers : ZFSet.rank N < o) :
    ∃ z' ∈ M.sets, ZFSet.rank z' < o ∧ GrowthLayerWitnessCode Qs rs μs (births.cutoff n)
      (births.cutoffOrder n) (births.cutoffMeet n) (births.cutoffBirth n) t N z' := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have embedding := data.externalIdentityCopy_ideal group action pairing unions powers separation infinite hG
  have contained : ∀ x y, ZFSet.pair x y ∈ E → y ∈ births.cutoff n := by
    intro x y copied
    have bounds := ZFSet.pair_mem_prod.1 (embedding.injection.function.1 copied)
    exact births.cutoff_old n ((mem_relationImage U B E y).2 ⟨bounds.2, x, bounds.1, copied⟩)
  have restricted := embedding.toMeetEmbeddingCode.restrictTarget (Q := births.cutoff n) contained
  have family := births.cutoffFamily_spec data group action pairing unions powers separation infinite hG hP0
  have hCut := M.pair_right (M.transitive family.1 ((family.2.2 n _).2 rfl))
  have preserves : ∀ x y a, ZFSet.pair x y ∈ E →
      (ZFSet.pair y a ∈ births.cutoffBirth n ↔ ZFSet.pair x a ∈ oldBirth) := by
    intro x y a copied
    change ZFSet.pair y a ∈ graphRestriction (births.cutoff n) births.birth ↔ _
    rw [pair_mem_graphRestriction]
    exact (and_iff_left (contained x y copied)).trans (births.preserves_seed x y a copied)
  obtain ⟨z', hz', code', rank'⟩ := code.ground_pushforward_rank_lt pairing unions powers separation
    (completion.algebra.union.ground 0) hCut
    (geometry.copies_ground _ data.group.group_code.identity_mem) hQs hN hz
    limit rank sourceGraphs ((ZFSet.rank_mono (births.cutoff_subset n)).trans_lt target) numbers
    completion.algebra.union.meet restricted preserves
    (fun _ _ entry => births.priorFiber_image oldTime (pair_mem_graphRestriction.1 entry).1)
  exact ⟨z', hz', rank', code'⟩

end PartitionPilot.Forcing.GroundExternalBirthData

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitTerminal_raw_witness_rank_lt (i : I) {t Qs rs μs : ZFSet.{u}}
    (before : t = (run.diagram.stage i).cutoff ∨ t ∈ (run.diagram.stage i).cutoff)
    (spaces : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 0 ↔
      ZFSet.pair s y ∈ Qs)
    (orders : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 1 ↔
      ZFSet.pair s y ∈ rs)
    (meets : ∀ s ∈ t, ∀ y, ZFSet.pair s y ∈ (run.linked i).serial.fields.graph 2 ↔
      ZFSet.pair s y ∈ μs)
    (hOmega : ZFSet.omega ∈ M.sets) {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank run.code < o) (numbers : ZFSet.rank ZFSet.omega < o) :
    ∃ z ∈ M.sets, GrowthLayerWitnessCode Qs rs μs run.limitPoints run.limitOrder
      run.limitMeetGraph run.limitBirth t ZFSet.omega z ∧ ZFSet.rank z < o := by
  have prior : t = (run.linked i).main.cutoff ∨ t ∈ (run.linked i).main.cutoff := by
    simpa only [run.linked_main] using before
  have hs := ZFSet.mem_insert (run.linked i).main.cutoff (run.linked i).main.cutoff
  have ht := ZFSet.mem_insert_iff.2 prior
  have raw := (run.linked i).serial.layer_code _ hs _ ht prior _
    ((run.linked i).serial.layerWitness_entry hs ht prior)
  have terminal := (run.linked i).terminal_values
  have code : GrowthLayerWitnessCode
      ((run.linked i).serial.fields.graph 0) ((run.linked i).serial.fields.graph 1)
      ((run.linked i).serial.fields.graph 2)
      (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.order
      (run.diagram.stage i).stage.meetGraph (run.diagram.stage i).birth t ZFSet.omega
      ((run.linked i).serial.layerWitness (run.linked i).main.cutoff t) := by
    rw [terminal.1, terminal.2.1, terminal.2.2.1, terminal.2.2.2.1] at raw
    simpa only [run.linked_main] using raw
  have serialBound : ZFSet.rank (run.linked i).serial.code ≤ ZFSet.rank (run.linked i).code := by
    simpa only [GroundLinkedMainStage.code, linkedMainStageCode, Fin.cases_succ] using
      (rank_nonemptyTupleCode_field_le 2 (Fin.cases (run.linked i).main.stage.code
        (Fin.cases (run.linked i).main.cutoff (fun _ => (run.linked i).serial.code)))
        (0 : Fin 1).succ.succ)
  have serialRank : ZFSet.rank (run.linked i).serial.code < o :=
    serialBound.trans_lt ((run.linkedCode_rank_lt_code i).trans rank)
  have witnessRank := ((run.linked i).serial.layerWitness_rank_lt_code hs ht prior).trans serialRank
  have sourceRank := ((run.linked i).serial.fieldGraph_rank_le_code 0).trans_lt serialRank
  obtain ⟨z, hz, copied, ranked⟩ := code.ground_pushforward_rank_lt
    pairing unions powers separation (run.diagram.stage i).stage.carrier_ground
    run.limitPoints_ground (run.limitPointMap_ground i)
    ((run.linked i).serial.fields.graph_ground 0) hOmega
    ((run.linked i).serial.layerWitness_ground _ _) limit witnessRank sourceRank
    (run.limitPoints_rank_lt limit rank) numbers (run.diagram.stage i).stage.meet
    (run.limitPointMap_meetEmbedding i) (run.limitPointMap_birth_iff i) (by
      intro q _ birth
      obtain ⟨x, hx, _, image⟩ := (run.limitBirth_old_fiber i q t before).1 birth
      exact ⟨x, hx, image⟩)
  exact ⟨z, hz, copied.congr_source_entries spaces orders meets, ranked⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
