import OAI.SetTheory.PartitionPrinciple.Definability.CodedProfileImageTests
import OAI.SetTheory.PartitionPrinciple.Definability.MainLimitCoverageFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.FixedTopProfilePreservation
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalRowTerms

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem limitPointMap_later_entry {i j : I} (before : i ≤ j) {x y q : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ (run.diagram.transition before).map.points)
    (image : ZFSet.pair x q ∈ run.limitPointMap i) :
    ZFSet.pair y q ∈ run.limitPointMap j :=
  (run.pointPresentation.inclusion_entry j y q).2
    ⟨(run.pointSystem.map_entry_bounds before entry).2,
      ((run.pointPresentation.inclusion_entry i x q).1 image).2.trans
        (run.pointPresentation.limitPoint_transition before entry)⟩

theorem limitPointMap_oldProfilePreservation (preserved : run.PreservesOldProfiles) (i : I) :
    OldProfilePreservationCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      run.limitPoints run.limitOrder run.limitMeetGraph (run.limitPointMap i)
      (M.groundPower (run.diagram.stage i).stage.carrier) := by
  intro F hF c hc E hE cap hcap profile c' hc' E' hE' cap' hcap' imageC imageE imageCap
  let embedding := run.limitPointMap_meetEmbedding i
  refine ⟨hc', hE', hcap', fun _ member => ((mem_relationImage _ _ _ _).1 member).1,
    ?_, ?_, embedding.monotone c cap c' cap' profile.target_below_cap imageC imageCap,
    fun lower => profile.cap_not_below_target
      ((run.limitPointMap_order_iff i cap c cap' c' imageCap imageC).1 lower),
    fun lower => profile.separator_not_below_cap
      ((run.limitPointMap_order_iff i E cap E' cap' imageE imageCap).1 lower)⟩
  · obtain ⟨f, hf⟩ := profile.nonempty
    obtain ⟨f', entry, _⟩ := embedding.injection.function.2 f (profile.filter_subset hf)
    exact ⟨f', (mem_relationImage _ _ _ _).2
      ⟨(ZFSet.pair_mem_prod.1 (embedding.injection.function.1 entry)).2, f, hf, entry⟩⟩
  · intro q hq above
    obtain ⟨j, x, hx, equal⟩ := run.pointPresentation.limitPoint_coverage hq
    have imageX : ZFSet.pair x q ∈ run.limitPointMap j :=
      (run.pointPresentation.inclusion_entry j x q).2 ⟨hx, equal⟩
    obtain ⟨k, ik, jk⟩ := run.common_upper i j
    obtain ⟨cK, cEntry⟩ := run.pointSystem.map_entry_total ik hc
    obtain ⟨eK, eEntry⟩ := run.pointSystem.map_entry_total ik hE
    obtain ⟨capK, capEntry⟩ := run.pointSystem.map_entry_total ik hcap
    obtain ⟨xK, xEntry⟩ := run.pointSystem.map_entry_total jk hx
    have atStage := preserved i k ik F hF c hc E hE cap hcap profile
      cK (run.pointSystem.map_entry_bounds ik cEntry).2
      eK (run.pointSystem.map_entry_bounds ik eEntry).2
      capK (run.pointSystem.map_entry_bounds ik capEntry).2 cEntry eEntry capEntry
    have tested := atStage.profile.at_embedding (run.limitPointMap_meetEmbedding k)
      (run.diagram.stage k).stage.meet run.limitMeet_code atStage.filter_subset
      (run.limitPointMap_later_entry ik cEntry imageC)
      (run.limitPointMap_later_entry ik eEntry imageE)
      (run.limitPointMap_later_entry ik capEntry imageCap)
      (run.limitPointMap_later_entry jk xEntry imageX) above
    have imageEqual :
        relationImage (relationImage F (run.diagram.stage k).stage.carrier
          (run.diagram.transition ik).map.points) run.limitPoints (run.limitPointMap k) =
        relationImage F run.limitPoints (run.limitPointMap i) :=
      (relationImage_composition_on profile.filter_subset).trans
        (congrArg (relationImage F run.limitPoints) (run.limitPointMap_comp ik))
    rw [imageEqual] at tested
    exact tested

end GroundMainPrefix

section
open SetFormula SetRealization
universe u v

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def preservedMainPrefixCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (PreservedMainPrefixCode M K Labels C D rD) B

theorem mem_preservedMainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.preservedMainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ PreservedMainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

theorem preservedMainPrefixCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.preservedMainPrefixCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (preservedMainPrefixFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (preservedMainPrefixFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.preservedMainPrefixCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_preservedMainPrefixCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_preservedMainPrefixFormula pairing unions powers separation collection 1 2 3 4 5 6 0
      (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def preservedMainPrefixes (Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.preservedMainPrefixCandidates level.carrier K Labels C D rD

theorem preservedMainPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.preservedMainPrefixes Labels C D rD ∈ M.sets :=
  M.preservedMainPrefixCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_preservedMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.preservedMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ PreservedMainPrefixCode M K Labels C D rD z :=
  M.mem_preservedMainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_preservedMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (preserved : run.PreservesOldProfiles)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.preservedMainPrefixes Labels C D rD :=
  level.mem_preservedMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.preserved_code preserved⟩

theorem exists_preservedPrefix_of_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Labels C D rD z : ZFSet.{u}}
    (member : z ∈ level.preservedMainPrefixes Labels C D rD) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z ∧ run.PreservesOldProfiles ∧ ZFSet.rank run.code < ZFSet.rank K := by
  obtain ⟨carrier, code⟩ := level.mem_preservedMainPrefixes.1 member
  obtain ⟨ground, rank⟩ := (level.membership z).1 carrier
  obtain ⟨T, hT, ordinal, run, indices, equal, preserved⟩ :=
    code.exists_decodedPrefix pairing unions powers separation ground
  exact ⟨T, hT, ordinal, run, indices, equal, preserved, equal.symm ▸ rank⟩

end GroundMainCandidateLevel
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialPreservedPrefixCandidate
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ level : GroundMainCandidateLevel M K,
      ∃ seed : GroundInitialMainSeedData M K C,
        ∃ certificate : GroundInitialMainSuccessorData M C (rationalCarrier seed.fractionCode)
            (rationalLtGraph seed.fractionCode) seed.source C,
          ∃ run : GroundMainPrefix M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) pairing unions powers separation (Fin 2),
            level.preservedMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            run.code ∈ level.preservedMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.PreservesOldProfiles ∧
            ZFSet.rank run.code < ZFSet.rank K ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
              certificate.transition.map.code := by
  dsimp only
  obtain ⟨level, seed, certificate, run, _, preserved, _, indices, _, rank, first, second, crossing⟩ :=
    M.exists_groundInitialPreservedMainPrefix pairing unions powers separation collection infinite choice hK standard
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  exact ⟨level, seed, certificate, run,
    level.preservedMainPrefixes_ground pairing unions powers separation collection infinite
      hK standard.1.1 hC hC seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_preservedMainPrefixes run preserved rank, indices, preserved, rank, first, second, crossing⟩

end TransitiveGround

namespace MainPrefixGraphFamily
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem exists_rankedPreservedUnionPrefix
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
    (limit : Order.IsSuccLimit (ZFSet.rank K))
    (key : I → ZFSet.{u}) (injective : Function.Injective key)
    (domain : ZFSet.range key ∈ M.sets)
    (whole : familyCodeGraph key family.code ∈ M.sets)
    (small : GroundBelow M (ZFSet.range key) K)
    (ranks : ∀ i, ZFSet.rank (family.code i) < ZFSet.rank K)
    (preserved : ∀ i, MainPrefixProfileGraphCode M K Labels C D rD
      (family.stages i) (family.transitions i))
    (level : GroundMainCandidateLevel M K) :
    letI := ordinalMainIndexPreorder family.indexUnion_ordinal
    ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation
        (SetMembers family.indexUnion),
      run.indices = family.indexUnion ∧ run.stageGraph = family.stageUnion ∧
      run.transitionGraph = family.transitionUnion ∧ run.code = family.unionCode ∧
      run.PreservesOldProfiles ∧ run.code ∈ M.sets ∧
      ZFSet.rank run.code < ZFSet.rank K ∧
      run.code ∈ level.preservedMainPrefixes Labels C D rD ∧
      (∀ i, graphRestriction (family.indices i) run.stageGraph = family.stages i) ∧
      (∀ i, graphRestriction (chronologyPairs (family.indices i)) run.transitionGraph =
        family.transitions i) := by
  let := ordinalMainIndexPreorder family.indexUnion_ordinal
  obtain ⟨run, indices, stages, transitions, equal, preservation⟩ :=
    family.exists_preservedUnionPrefix pairing unions powers separation key injective domain whole preserved
  have rank : ZFSet.rank run.code < ZFSet.rank K := by
    rw [equal]
    exact family.unionCode_rank_lt_small pairing unions powers separation collection hK ordinal
      regular limit key injective domain whole small ranks
  refine ⟨run, indices, stages, transitions, equal, preservation, run.code_ground, rank,
    level.prefix_mem_preservedMainPrefixes run preservation rank, ?_, ?_⟩
  · intro i
    rw [stages]
    exact family.stageUnion_restrict i
  · intro i
    rw [transitions]
    exact family.transitionUnion_restrict i

end MainPrefixGraphFamily

namespace GroundMainPrefix.FixedTopStage
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {i₀ : I} (data : run.FixedTopStage i₀)

theorem transition_oldProfilePreservation (preserved : run.PreservesOldProfiles) (i : I) :
    OldProfilePreservationCode (run.diagram.stage i).stage.carrier
      (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
      data.stage.carrier data.stage.order data.stage.meetGraph (data.transition i).points
      (M.groundPower (run.diagram.stage i).stage.carrier) := by
  rw [data.carrier_eq, data.order_eq, data.meet_eq, data.transition_points]
  exact (run.limitPointMap_oldProfilePreservation preserved i).fixedTop run.limitMeet_code
    (run.limitPointMap_injection i).function.1

namespace RankedChronology
variable {data} {level : GroundMainCandidateLevel M K} (chronology : data.RankedChronology level)

theorem transition_preservesOldProfiles (preserved : run.PreservesOldProfiles) (i : I) :
    (chronology.transition i).PreservesOldProfiles :=
  data.transition_oldProfilePreservation preserved i

end RankedChronology
end GroundMainPrefix.FixedTopStage

namespace GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_rawCoveredPreservedAppendLimit (preserved : run.PreservesOldProfiles) (i₀ : I)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns_eq : C = M.groundOmegaOne pairing unions powers separation collection infinite)
    (indexMember : run.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (level : GroundMainCandidateLevel M K) :
    ∃ data : run.FixedTopStage i₀,
      ∃ chronology : data.RankedChronology level,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
          (∀ i : I, extended.key (i : WithTop I) = run.key i) ∧
          extended.key ⊤ = run.indices ∧
          (∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ extended.transitionGraph ↔
            z = (chronology.cone.leg i).map.code) ∧
          run.LimitCoverage chronology.main chronology.cone ∧
          MainLimitCoverageGraphCode run.indices run.stageGraph extended.transitionGraph
            target.main.stage.carrier target.main.stage.actors target.main.stage.order
            target.main.stage.top target.main.cutoff target.main.birth ∧
          target.main = chronology.main ∧
          target.serial.code = chronology.serial.code ∧
          extended.PreservesOldProfiles ∧
          target.main.stage = data.stage ∧ target.main.cutoff = run.cutoffLimit ∧
          target.main.birth = fixedTopBirth run.limitPoints run.limitBirth run.cutoffLimit ∧
          target.serial.code ∈ level.validChronologies C D rD ∧
          extended.indices = insert run.indices run.indices ∧
          extended.indices ∈ M.groundOmegaOne pairing unions powers separation collection infinite ∧
          extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
          extended.code ∈ level.validMainPrefixes Labels C D rD ∧
          extended.code ∈ level.preservedMainPrefixes Labels C D rD ∧
          (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
          extended.linked ⊤ = target ∧
          extended.stageGraph = insert (ZFSet.pair run.indices target.code) run.stageGraph ∧
          graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
          graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
          (∀ (i j : I) (before : i ≤ j),
            (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
              (run.diagram.transition before).map.code) ∧
          (∀ i : I,
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.points = run.limitPointMap i ∧
            (extended.diagram.transition (show (i : WithTop I) ≤ ⊤ from le_top)).map.actors = run.limitActorMap i) ∧
          (∀ (i : I) (x y : ZFSet.{u}), ZFSet.pair x y ∈ run.limitPointMap i →
            ZFSet.pair y target.main.stage.top ∈ target.main.stage.order ∧
              ZFSet.pair target.main.stage.top y ∉ target.main.stage.order) := by
  have indices := M.groundOmegaOne_member_countable pairing unions powers separation collection infinite indexMember
  have below : GroundBelow M run.indices K :=
    ⟨ZFSet.omega, standard.omega_mem pairing unions powers separation hK, indices⟩
  obtain ⟨data⟩ := run.exists_fixedTopMainStage i₀ collection infinite choice columns_eq indices
  obtain ⟨chronology⟩ := data.exists_rankedChronology collection infinite choice hK standard below oldRank level
  let target := chronology.linked infinite choice hK standard below oldRank
  have conditions := standard.to_conditions pairing unions powers separation hK
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  obtain ⟨row, ground, function, entries, rowRank⟩ := run.exists_limitTransitionRow limit oldRank
  have rowEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ row ↔
      z = (chronology.cone.leg i).map.code := entries
  let extended := run.appendCone target chronology.cone ground function rowEntries chronology.cone_coverage
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendCone_code_rank_lt target chronology.cone ground function rowEntries chronology.cone_coverage
      limit oldRank (target.code_rank_lt pairing unions powers separation infinite hK conditions) rowRank
  have preservedExtended : extended.PreservesOldProfiles :=
    run.appendCone_preservesOldProfiles preserved target chronology.cone ground function
      rowEntries chronology.cone_coverage
      (fun i => chronology.transition_preservesOldProfiles preserved i)
  have wholeEntries : ∀ i z, ZFSet.pair (ZFSet.pair run.indices (run.key i)) z ∈ extended.transitionGraph ↔
      z = (chronology.cone.leg i).map.code := by
    intro i z
    exact extended.transitionGraph_entry (show (i : WithTop I) ≤ ⊤ from le_top) z
  have rawCoverage := (run.limitCoverage_graph_iff chronology.cone wholeEntries).2 chronology.limitCoverage
  have indexEqual := run.appendCone_indices target chronology.cone ground function rowEntries chronology.cone_coverage
  have extendedIndexMember : extended.indices ∈
      M.groundOmegaOne pairing unions powers separation collection infinite := by
    rw [indexEqual]
    exact M.groundOmegaOne_successor pairing unions powers separation collection infinite indexMember
  refine ⟨data, chronology, target, extended, (fun _ => rfl), rfl, wholeEntries,
    chronology.limitCoverage, rawCoverage, rfl, rfl, preservedExtended,
    rfl, rfl, chronology.main_birth, chronology.code_member,
    indexEqual, extendedIndexMember,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    level.prefix_mem_preservedMainPrefixes extended preservedExtended rank,
    run.appendCone_linked_old target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_linked_top target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_stageGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    run.appendCone_transitionGraph_restrict target chronology.cone ground function rowEntries chronology.cone_coverage,
    ?_, ?_, ?_⟩
  · intro i j before
    rfl
  · intro i
    exact ⟨rfl, rfl⟩
  · intro i x y entry
    exact data.point_strict_top i entry

end GroundMainPrefix

end PartitionPilot.Forcing

end OAI
