import OAI.SetTheory.PartitionPrinciple.Definability.MainPrefixValidityFormulas
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSmallFamilyRangeRanks
import OAI.SetTheory.PartitionPrinciple.Transfinite.MainPrefixHistoryUnionRecognition

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def mainPrefixGraphBodyFormula {n} (K Labels C D rD N T S E J : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula T).toFormula
    (.conj (functionGraphOnFormula T S)
      (.conj (functionGraphOnFormula J E)
        (.conj (mainPrefixStagesFormula K Labels C D rD N S)
          (.conj (mainPrefixTransitionsFormula K Labels C D rD N S E)
            (.conj (mainPrefixIdentityFormula E) (mainPrefixCompositionFormula E))))))

def mainPrefixGraphFormula {n} (K Labels C D rD N T S E : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.chronologyPairsEquationFormula 0 T.succ).toFormula
    (mainPrefixGraphBodyFormula K.succ Labels.succ C.succ D.succ rD.succ N.succ
      T.succ S.succ E.succ 0))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_mainPrefixGraphBodyFormula {n} (K Labels C D rD N T S E J : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K))
    (pairs : env J = chronologyPairs (env T)) :
    Realize M.sets (mainPrefixGraphBodyFormula K Labels C D rD N T S E J) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula T).toFormula env ∧
    Realize M.sets (functionGraphOnFormula T S) env ∧
    Realize M.sets (functionGraphOnFormula J E) env ∧
    Realize M.sets (mainPrefixStagesFormula K Labels C D rD N S) env ∧
    Realize M.sets (mainPrefixTransitionsFormula K Labels C D rD N S E) env ∧
    Realize M.sets (mainPrefixIdentityFormula E) env ∧
    Realize M.sets (mainPrefixCompositionFormula E) env) ↔ _
  rw [BoundedFormula.realize_ordinalFormula M T env members, ← ordinalSetProperty_iff,
    M.realize_functionGraphOnFormula unions T S env members,
    M.realize_functionGraphOnFormula unions J E env members,
    M.realize_mainPrefixStagesFormula pairing unions powers separation collection K Labels C D rD N S env members omega ordinal,
    M.realize_mainPrefixTransitionsFormula pairing unions powers separation collection K Labels C D rD N S E env members omega ordinal,
    M.realize_mainPrefixIdentityFormula E env members,
    M.realize_mainPrefixCompositionFormula E env members, pairs]
  constructor
  · rintro ⟨ord, stages, transitions, valid, maps, self, comp⟩
    exact ⟨ord, stages, transitions, valid, maps, self, comp⟩
  · intro code
    exact ⟨code.ordinal, code.stages, code.transitions, code.stage_valid,
      code.transition_valid, code.identity, code.composition⟩

theorem realize_mainPrefixGraphFormula {n} (K Labels C D rD N T S E : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixGraphFormula K Labels C D rD N T S E) env ↔
      MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (env T) (env S) (env E) := by
  rw [mainPrefixGraphFormula, realize_ex]
  constructor
  · rintro ⟨J, hJ, equation, body⟩
    have pairs := (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
      (extend J env) (Fin.cases hJ members)).1 equation
    exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
      K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
      (extend J env) (Fin.cases hJ members) omega ordinal pairs).1 body
  · intro code
    have ground := M.chronologyPairs_mem pairing unions powers separation (members T)
    refine ⟨chronologyPairs (env T), ground, ?_, ?_⟩
    · exact (BoundedFormula.realize_chronologyPairsEquationFormula M 0 T.succ
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members)).2 rfl
    · exact (M.realize_mainPrefixGraphBodyFormula pairing unions powers separation collection
        K.succ Labels.succ C.succ D.succ rD.succ N.succ T.succ S.succ E.succ 0
        (extend (chronologyPairs (env T)) env) (Fin.cases ground members) omega ordinal rfl).2 code

end TransitiveGround

namespace SetFormula
def mainPrefixFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
    (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1) (field 2)))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_mainPrefixFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (mainPrefixFormula K Labels C D rD N z) env ↔
      MainPrefixCode M (env K) (env Labels) (env C) (env D) (env rD) (env z) := by
  rw [mainPrefixFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env)) ↔
      env z = mainPrefixCode (f 0) (f 1) (f 2) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    have tuple := BoundedFormula.realize_mainPrefixTupleFormula M
      (old z) (field 0) (field 1) (field 2) (extendMany 3 f env) mems
    have code := M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 0) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    rw [tuple, code]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 recognized⟩
  · rintro ⟨T, S, E, encoded, code⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members z)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have fieldsGround : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, fieldsGround, (actual f fieldsGround).2 ⟨encoded, code⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetFormula
universe u v

namespace GroundMainPrefix
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem code_eq_mainPrefixCode : run.code = mainPrefixCode run.indices run.stageGraph run.transitionGraph := rfl

theorem code_valid : MainPrefixCode M K Labels C D rD run.code :=
  ⟨run.indices, run.stageGraph, run.transitionGraph, rfl, run.graph_code⟩

end GroundMainPrefix

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def mainPrefixCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (MainPrefixCode M K Labels C D rD) B

theorem mem_mainPrefixCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.mainPrefixCandidates B K Labels C D rD ↔
      z ∈ B ∧ MainPrefixCode M K Labels C D rD z := ZFSet.mem_sep

theorem mainPrefixCandidates_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.mainPrefixCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (mainPrefixFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (mainPrefixFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.mainPrefixCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_mainPrefixCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_mainPrefixFormula pairing unions powers separation collection 1 2 3 4 5 6 0
      (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validMainPrefixes (Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.mainPrefixCandidates level.carrier K Labels C D rD

theorem validMainPrefixes_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validMainPrefixes Labels C D rD ∈ M.sets :=
  M.mainPrefixCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_validMainPrefixes {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.validMainPrefixes Labels C D rD ↔
      z ∈ level.carrier ∧ MainPrefixCode M K Labels C D rD z :=
  M.mem_mainPrefixCandidates level.carrier K Labels C D rD z

theorem prefix_mem_validMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (rank : ZFSet.rank run.code < ZFSet.rank K) : run.code ∈ level.validMainPrefixes Labels C D rD :=
  level.mem_validMainPrefixes.2 ⟨(level.membership _).2 ⟨run.code_ground, rank⟩, run.code_valid⟩

theorem finite_prefix_mem_validMainPrefixes
    {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
    {unions : Realize M.sets SetFormula.union Fin.elim0}
    {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
    (infinite : Realize M.sets infinity Fin.elim0) (hK : K ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    {Labels C D rD : ZFSet.{u}} {I : Type v} [Small.{u} I] [Preorder I] [Finite I]
    (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)
    (keys : ∀ i, ZFSet.rank (run.key i) < ZFSet.rank K) :
    run.code ∈ level.validMainPrefixes Labels C D rD :=
  level.prefix_mem_validMainPrefixes run (run.finite_code_rank_lt infinite hK conditions keys)

end GroundMainCandidateLevel
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_initialMainPrefixCandidate
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
            level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
            run.code ∈ level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
            (run.linked 0).main = seed.source ∧ (run.linked 1).main = certificate.target ∧
            (run.linked 0).serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            (run.linked 1).serial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (∀ z, ZFSet.pair (ZFSet.pair (natSetCode 1) (natSetCode 0)) z ∈ run.transitionGraph ↔
              z = certificate.transition.map.code) ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.points =
              certificate.transition.map.points ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.actors =
              certificate.transition.map.actors := by
  dsimp only
  obtain ⟨level, seed, certificate, first, second, run, firstMain, secondMain,
    firstMember, secondMember, indices, ground, rank, firstLinked, secondLinked,
    stageZero, stageOne, _entryZero, _entryOne, entryTransition, points, actors⟩ :=
    M.exists_groundInitialTwoStageMainPrefix pairing unions powers separation
      collection infinite choice hK standard
  have conditions := standard.to_conditions pairing unions powers separation hK
  refine ⟨level, seed, certificate, run,
    level.validMainPrefixes_ground pairing unions powers separation collection infinite hK
      conditions.1 seed.source.stage.columns_ground seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    level.prefix_mem_validMainPrefixes run rank, indices, ground, rank,
    ?_, ?_, ?_, ?_, stageZero, stageOne, entryTransition, points, actors⟩
  · exact firstLinked ▸ firstMain
  · exact secondLinked ▸ secondMain
  · exact firstLinked ▸ firstMember
  · exact secondLinked ▸ secondMember

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {K Labels C D rD z : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

theorem MainPrefixCode.exists_decodedPrefix
    (valid : MainPrefixCode M K Labels C D rD z) (ground : z ∈ M.sets) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z := by
  obtain ⟨T, S, E, equal, raw⟩ := valid
  obtain ⟨hT, hS, hE⟩ := M.mainPrefixCode_fields_mem (equal ▸ ground)
  refine ⟨T, hT, raw.ordinal, raw.decodedPrefix pairing unions powers separation hT hS hE,
    raw.decodedPrefix_indices pairing unions powers separation hT hS hE, ?_⟩
  exact (raw.decodedPrefix_code pairing unions powers separation hT hS hE).trans equal.symm

theorem GroundMainCandidateLevel.exists_prefix_of_mem
    (level : GroundMainCandidateLevel M K)
    (member : z ∈ level.validMainPrefixes Labels C D rD) :
    ∃ T ∈ M.sets, ∃ ordinal : ordinalSetProperty T,
      letI := ordinalMainIndexPreorder ordinal
      ∃ run : GroundMainPrefix M K Labels C D rD pairing unions powers separation (SetMembers T),
        run.indices = T ∧ run.code = z ∧ ZFSet.rank run.code < ZFSet.rank K := by
  obtain ⟨carrier, valid⟩ := level.mem_validMainPrefixes.1 member
  obtain ⟨ground, rank⟩ := (level.membership z).1 carrier
  obtain ⟨T, hT, ordinal, run, indices, code⟩ :=
    valid.exists_decodedPrefix pairing unions powers separation ground
  exact ⟨T, hT, ordinal, run, indices, code, code.symm ▸ rank⟩

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem exists_rankedAppendTaskBearing (last : I) (greatest : ∀ i, i ≤ last)
    (oldRank : ZFSet.rank run.code < ZFSet.rank K) (limit : Order.IsSuccLimit (ZFSet.rank K))
    (level : GroundMainCandidateLevel M K) {targetCode z : ZFSet.{u}}
    (targetRank : ZFSet.rank targetCode < ZFSet.rank K)
    (code : TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked last).code targetCode z) :
    ∃ target : GroundLinkedMainStage M K Labels C D rD,
      ∃ step : GroundChronologicalMainTransition (run.diagram.stage last) target.main,
        ∃ covered : step.CoversOldBirths,
          ∃ extended : GroundMainPrefix M K Labels C D rD pairing unions powers separation (WithTop I),
            extended = run.appendLast last greatest target step covered ∧
            target.code = targetCode ∧ step.map.code = z ∧ step.PreservesOldProfiles ∧
            extended.code ∈ M.sets ∧ ZFSet.rank extended.code < ZFSet.rank K ∧
            extended.code ∈ level.validMainPrefixes Labels C D rD ∧
            extended.indices = insert run.indices run.indices ∧
            (∀ i : I, extended.linked (i : WithTop I) = run.linked i) ∧
            extended.linked ⊤ = target ∧
            extended.stageGraph = insert (ZFSet.pair run.indices targetCode) run.stageGraph ∧
            graphRestriction run.indices extended.stageGraph = run.stageGraph ∧
            graphRestriction (chronologyPairs run.indices) extended.transitionGraph = run.transitionGraph ∧
            (∀ (i j : I) (before : i ≤ j),
              (extended.diagram.transition (WithTop.coe_le_coe.mpr before)).map.code =
                (run.diagram.transition before).map.code) ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.points = step.map.points ∧
            (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.actors = step.map.actors ∧
            TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
              (run.linked last).code (extended.linked ⊤).code
              (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code := by
  obtain ⟨target, targetEqual, transition, mapEqual, coverage, profiles⟩ :=
    code.exists_from_linked pairing unions powers separation
  let step : GroundChronologicalMainTransition (run.diagram.stage last) target.main :=
    transition.retargetEq (run.linked_main last) rfl
  have covered : step.CoversOldBirths :=
    (transition.retargetEq_coversOldBirths_iff (run.linked_main last) rfl).2 coverage
  have stepCode : step.map.code = z :=
    (transition.retargetEq_code (run.linked_main last) rfl).trans mapEqual
  have stepProfiles : step.PreservesOldProfiles :=
    (transition.retargetEq_preservesOldProfiles_iff (run.linked_main last) rfl).2 profiles
  let extended := run.appendLast last greatest target step covered
  have rank : ZFSet.rank extended.code < ZFSet.rank K :=
    run.appendLast_code_rank_lt last greatest target step covered limit oldRank
      (targetEqual.symm ▸ targetRank)
  have lastStep := run.appendLast_transition_last last greatest target step covered
  have lastCode :
      (extended.diagram.transition (show (last : WithTop I) ≤ ⊤ from le_top)).map.code = z := by
    rw [lastStep]
    exact stepCode
  refine ⟨target, step, covered, extended, rfl, targetEqual, stepCode, stepProfiles,
    extended.code_ground, rank, level.prefix_mem_validMainPrefixes extended rank,
    run.appendLast_indices last greatest target step covered,
    run.appendLast_linked_old last greatest target step covered,
    run.appendLast_linked_top last greatest target step covered, ?_,
    run.appendLast_stageGraph_restrict last greatest target step covered,
    run.appendLast_transitionGraph_restrict last greatest target step covered,
    (fun _ _ _ => rfl), lastCode, ?_, ?_, ?_⟩
  · rw [run.appendLast_stageGraph last greatest target step covered, targetEqual]
  · rw [lastStep]
  · rw [lastStep]
  · rw [run.appendLast_linked_top last greatest target step covered, targetEqual, lastCode]
    exact code

end PartitionPilot.Forcing.GroundMainPrefix

namespace PartitionPilot.Forcing.MainPrefixGraphFamily
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {I : Type v} [Small.{u} I]
variable (family : MainPrefixGraphFamily M K Labels C D rD I)

theorem fieldUnions_rank_le_codeRange :
    ZFSet.rank family.indexUnion ≤ ZFSet.rank (ZFSet.range family.code) ∧
      ZFSet.rank family.stageUnion ≤ ZFSet.rank (ZFSet.range family.code) ∧
      ZFSet.rank family.transitionUnion ≤ ZFSet.rank (ZFSet.range family.code) := by
  let entries (i : I) : Fin 3 → ZFSet.{u} :=
    Fin.cases (family.indices i) (Fin.cases (family.stages i) (fun _ => family.transitions i))
  have fields (i : I) (j : Fin 3) :
      ZFSet.rank (entries i j) ≤ ZFSet.rank (family.code i) := by
    simpa only [code, mainPrefixCode, entries] using rank_nonemptyTupleCode_field_le 2
      (Fin.cases (family.indices i) (Fin.cases (family.stages i) (fun _ => family.transitions i))) j
  have bound (value : I → ZFSet.{u}) (ranks : ∀ i, ZFSet.rank (value i) ≤ ZFSet.rank (family.code i)) :
      ZFSet.rank (⋃₀ ZFSet.range value) ≤ ZFSet.rank (ZFSet.range family.code) := by
    apply ZFSet.rank_le_iff.2
    intro x hx
    obtain ⟨i, hi⟩ := (familyCodeGraph_valueUnion_mem_iff value x).1 hx
    exact ((ZFSet.rank_lt_of_mem hi).trans_le (ranks i)).trans
      (ZFSet.rank_lt_of_mem (ZFSet.mem_range.2 ⟨i, rfl⟩))
  refine ⟨bound family.indices ?_, bound family.stages ?_, bound family.transitions ?_⟩
  · intro i
    simpa only [entries, Fin.cases_zero] using fields i 0
  · intro i
    exact fields i 1
  · intro i
    exact fields i 2

theorem unionCode_rank_lt_of_codeRange {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (rank : ZFSet.rank (ZFSet.range family.code) < o) : ZFSet.rank family.unionCode < o := by
  have fields := family.fieldUnions_rank_le_codeRange
  exact rank_nonemptyTupleCode_lt limit 2 _
    (Fin.cases (fields.1.trans_lt rank)
      (Fin.cases (fields.2.1.trans_lt rank) (fun _ => fields.2.2.trans_lt rank)))

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (hK : K ∈ M.sets)
variable (ordinal : ordinalSetProperty K) (regular : GroundRegular M K)
variable (limit : Order.IsSuccLimit (ZFSet.rank K))
variable (key : I → ZFSet.{u}) (injective : Function.Injective key)
variable (domain : ZFSet.range key ∈ M.sets)
variable (whole : familyCodeGraph key family.code ∈ M.sets)
variable (small : GroundBelow M (ZFSet.range key) K)
variable (ranks : ∀ i, ZFSet.rank (family.code i) < ZFSet.rank K)
include pairing unions powers separation collection hK ordinal regular limit injective domain whole small ranks

theorem unionCode_rank_lt_small : ZFSet.rank family.unionCode < ZFSet.rank K :=
  family.unionCode_rank_lt_of_codeRange limit
    (regular.familyCodeGraph_valueRange_rank_lt pairing unions powers separation collection hK ordinal
      key family.code injective domain whole small ranks)

theorem unionCode_mem_validMainPrefixes (level : GroundMainCandidateLevel M K) :
    family.unionCode ∈ level.validMainPrefixes Labels C D rD :=
  level.mem_validMainPrefixes.2 ⟨(level.membership _).2
    ⟨family.unionCode_ground pairing unions powers separation key injective domain whole,
      family.unionCode_rank_lt_small pairing unions powers separation collection hK ordinal regular limit
        key injective domain whole small ranks⟩, family.unionCode_valid⟩

end PartitionPilot.Forcing.MainPrefixGraphFamily

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def preservedMainPrefixFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  exBlock 3 (.conj (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
    (.conj (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
      (field 0) (field 1) (field 2))
      (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
        (field 1) (field 2))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_preservedMainPrefixFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (preservedMainPrefixFormula K Labels C D rD N z) env ↔
      PreservedMainPrefixCode M (env K) (env Labels) (env C) (env D) (env rD) (env z) := by
  rw [preservedMainPrefixFormula, realize_exBlock]
  let old := suffixIndex n 3
  let field := prefixIndex n 3
  have actual (f : Fin 3 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :
      (Realize M.sets (BoundedFormula.mainPrefixTupleFormula (old z) (field 0) (field 1) (field 2)).toFormula
          (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixGraphFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
          (field 0) (field 1) (field 2)) (extendMany 3 f env) ∧
        Realize M.sets (mainPrefixProfileGraphFormula (old K) (old Labels) (old C) (old D)
          (old rD) (old N) (field 1) (field 2)) (extendMany 3 f env)) ↔
      env z = mainPrefixCode (f 0) (f 1) (f 2) ∧
        MainPrefixGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 0) (f 1) (f 2) ∧
        MainPrefixProfileGraphCode M (env K) (env Labels) (env C) (env D) (env rD) (f 1) (f 2) := by
    have mems := extendMany_members 3 f env ground members
    have tuple := BoundedFormula.realize_mainPrefixTupleFormula M
      (old z) (field 0) (field 1) (field 2) (extendMany 3 f env) mems
    have code := M.realize_mainPrefixGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 0) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    have profiles := M.realize_mainPrefixProfileGraphFormula pairing unions powers separation collection
      (old K) (old Labels) (old C) (old D) (old rD) (old N) (field 1) (field 2)
      (extendMany 3 f env) mems
      (by simpa only [old, extendMany_suffix] using omega)
      (by simpa only [old, extendMany_suffix] using ordinal)
    rw [tuple, code, profiles]
    simp only [old, field, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f 0, f 1, f 2, (actual f ground).1 recognized⟩
  · rintro ⟨T, S, E, encoded, code, preserved⟩
    have ground := M.mainPrefixCode_fields_mem (encoded ▸ members z)
    let f : Fin 3 → ZFSet.{u} := Fin.cases T (Fin.cases S (fun _ => E))
    have fieldsGround : ∀ j, f j ∈ M.sets := Fin.cases ground.1 (Fin.cases ground.2.1 (fun _ => ground.2.2))
    exact ⟨f, fieldsGround, (actual f fieldsGround).2 ⟨encoded, code, preserved⟩⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialPreservedMainPrefix
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
            PreservedMainPrefixCode M K C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) run.code ∧
            run.PreservesOldProfiles ∧
            run.code ∈ level.validMainPrefixes C C (rationalCarrier seed.fractionCode)
              (rationalLtGraph seed.fractionCode) ∧
            run.indices = natSetCode 2 ∧ run.code ∈ M.sets ∧ ZFSet.rank run.code < ZFSet.rank K ∧
            run.diagram.stage 0 = seed.source ∧ run.diagram.stage 1 = certificate.target ∧
            (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
              certificate.transition.map.code := by
  dsimp only
  obtain ⟨level, seed, certificate, run, _, member, indices, ground, rank,
    _, _, _, _, first, second, _entry, points, actors⟩ :=
    M.exists_initialMainPrefixCandidate pairing unions powers separation collection infinite choice hK standard
  have crossing : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).PreservesOldProfiles := by
    unfold GroundChronologicalMainTransition.PreservesOldProfiles
    rw [points, first, second]
    exact certificate.oldProfilePreservation pairing unions powers separation infinite
      (M.groundPower seed.source.stage.carrier)
  have preserved := run.preservesOldProfiles_of_zero_one crossing
  have exactMap : (run.diagram.transition (show (0 : Fin 2) ≤ 1 from by decide)).map.code =
      certificate.transition.map.code := congrArg₂ ZFSet.pair points actors
  exact ⟨level, seed, certificate, run, run.preserved_code preserved, preserved, member,
    indices, ground, rank, first, second, exactMap⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
