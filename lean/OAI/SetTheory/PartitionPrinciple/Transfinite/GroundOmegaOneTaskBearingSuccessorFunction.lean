import OAI.SetTheory.PartitionPrinciple.Definability.GroundRankedBoundedSerialization
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundTaskBearingSuccessorWitness
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRankedCompressionSerialization
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRankedExternalSerialization
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundLinkedMainStageLevels

namespace OAI


namespace PartitionPilot.Forcing.GroundInitialMainSuccessorData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD Labels K : ZFSet.{u}}
variable {source : GroundChronologicalMainStage M C D rD}
variable (certificate : GroundInitialMainSuccessorData M C D rD source Labels)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
variable (invariant : source.Invariant K Labels) (level : GroundMainCandidateLevel M K)
local notation "births" => certificate.births
include pairing unions powers separation collection infinite choice hK conditions invariant

theorem exists_rankedTargetSerialization
    (prior : GroundSerializedChronology M (insert source.cutoff source.cutoff) C D rD)
    (priorRank : ZFSet.rank prior.code < ZFSet.rank K)
    (agreement : ∀ j s, s ∈ insert source.cutoff source.cutoff →
      prior.fields.value j s = source.history.fieldValue j s) :
    ∃ serial : GroundSerializedChronology M (insert certificate.target.cutoff certificate.target.cutoff) C D rD,
      serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
      serial.code ∈ level.validChronologies C D rD ∧
      (∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
        serial.fields.value j s = certificate.target.history.fieldValue j s) ∧
      serial.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
      serial.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
      serial.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
      serial.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
      serial.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  obtain ⟨compressionSerial, _, compressionRank, _, compressionValues, _⟩ := certificate.exists_rankedCompressionSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level prior priorRank agreement
  obtain ⟨externalSerial, _, externalRank, _, externalValues, _⟩ := certificate.exists_rankedExternalSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level
    prior priorRank agreement compressionSerial compressionRank compressionValues
  obtain ⟨bounded, _, boundedRank, _, values⟩ := certificate.exists_rankedBoundedSerialization
    pairing unions powers separation collection infinite choice hK conditions invariant level
    externalSerial externalRank externalValues
  have times : insert (births).limit (births).limit = insert certificate.target.cutoff certificate.target.cutoff :=
    congrArg (fun t : ZFSet.{u} => insert t t) certificate.target_cutoff.symm
  let serial := bounded.castTime times
  have serialValues : ∀ j s, s ∈ insert certificate.target.cutoff certificate.target.cutoff →
      serial.fields.value j s = certificate.target.history.fieldValue j s := by
    intro j s hs
    rw [GroundSerializedChronology.castTime_value]
    have old := values j s (times.symm ▸ hs)
    have same := GroundChronologicalHistory.fieldValue_eq_of_heq times.symm certificate.target_history j s
    exact old.trans same.symm
  have rank : ZFSet.rank serial.code < ZFSet.rank K := by
    rw [GroundSerializedChronology.castTime_code]
    exact boundedRank
  refine ⟨serial, serial.code_ground pairing, rank,
    level.ranked_mem_validChronologies pairing serial rank, serialValues, ?_, ?_, ?_, ?_, ?_⟩
  · exact (serialValues 0 _ (ZFSet.mem_insert _ _)).trans certificate.target.carrier_eq
  · exact (serialValues 1 _ (ZFSet.mem_insert _ _)).trans certificate.target.order_eq
  · exact (serialValues 2 _ (ZFSet.mem_insert _ _)).trans certificate.target.meet_eq
  · exact serialValues 3 _ (ZFSet.mem_insert _ _)
  · exact (serialValues 4 _ (ZFSet.mem_insert _ _)).trans certificate.target.height_eq

end PartitionPilot.Forcing.GroundInitialMainSuccessorData



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def taskBearingSuccessorPairFormula {n}
    (K Labels C D rD N S V source output : Fin n) : SetFormula n :=
  .ex (.conj (.mem 0 S.succ) (.ex (.conj (.mem 0 V.succ.succ)
    (.conj (BoundedFormula.orderedPairFormula output.succ.succ 1 0).toFormula
      (taskBearingMainSuccessorFormula K.succ.succ Labels.succ.succ C.succ.succ
        D.succ.succ rD.succ.succ N.succ.succ source.succ.succ 1 0)))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_taskBearingSuccessorPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D rD N S V source output : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (omega : env N = ZFSet.omega)
    (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (taskBearingSuccessorPairFormula K Labels C D rD N S V source output) env ↔
      ∃ target ∈ env S, ∃ z ∈ env V, env output = ZFSet.pair target z ∧
        TaskBearingMainSuccessorCode M (env K) (env Labels) (env C) (env D) (env rD)
          (env N) (env source) target z := by
  simp only [taskBearingSuccessorPairFormula, realize_ex, Realize]
  have recognized (target z : ZFSet.{u}) (ht : target ∈ M.sets) (hz : z ∈ M.sets) :=
    M.realize_taskBearingMainSuccessorFormula pairing unions powers separation collection
      K.succ.succ Labels.succ.succ C.succ.succ D.succ.succ rD.succ.succ N.succ.succ
      source.succ.succ 1 0 (extend z (extend target env)) (Fin.cases hz (Fin.cases ht members)) omega ordinal
  have pair (target z : ZFSet.{u}) (ht : target ∈ M.sets) (hz : z ∈ M.sets) :=
    (BoundedFormula.realize_toFormula M
      (BoundedFormula.orderedPairFormula output.succ.succ 1 0)
      (extend z (extend target env)) (Fin.cases hz (Fin.cases ht members))).trans
      (BoundedFormula.truth_orderedPairFormula output.succ.succ 1 0 (extend z (extend target env)))
  constructor
  · rintro ⟨target, ht, inS, z, hz, inV, shape, code⟩
    exact ⟨target, inS, z, inV, (pair target z ht hz).1 shape, (recognized target z ht hz).1 code⟩
  · rintro ⟨target, inS, z, inV, shape, code⟩
    have ht := M.transitive (members S) inS
    have hz := M.transitive (members V) inV
    exact ⟨target, ht, inS, z, hz, inV, (pair target z ht hz).2 shape, (recognized target z ht hz).2 code⟩

def taskBearingSuccessorParams (S V K Labels C D rD : ZFSet.{u}) : Fin 8 → ZFSet.{u} :=
  extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega
    (extend S (extend V Fin.elim0)))))))

theorem taskBearingSuccessorParams_ground
    (separation : SeparationSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    ∀ j, taskBearingSuccessorParams S V K Labels C D rD j ∈ M.sets :=
  Fin.cases hK (Fin.cases hLabels (Fin.cases hC (Fin.cases hD (Fin.cases hrD
    (Fin.cases (M.omega_mem separation infinite) (Fin.cases hS (Fin.cases hV (fun j => Fin.elim0 j))))))))

noncomputable def taskBearingSuccessorRelation (S V K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.definableRelation (taskBearingSuccessorPairFormula 2 3 4 5 6 7 8 9 (0 : Fin 10) 1)
    (taskBearingSuccessorParams S V K Labels C D rD) S (ZFSet.prod V V)

theorem taskBearingSuccessorRelation_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    M.taskBearingSuccessorRelation S V K Labels C D rD ∈ M.sets :=
  M.definableRelation_mem pairing unions powers separation _ _
    (M.taskBearingSuccessorParams_ground separation infinite hS hV hK hLabels hC hD hrD)
    hS (M.prod_mem pairing unions powers separation hV hV)

theorem taskBearingSuccessorRelation_entry
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (ordinal : ordinalSetProperty K)
    (subset : S ⊆ V) (source target z : ZFSet.{u}) :
    ZFSet.pair source (ZFSet.pair target z) ∈ M.taskBearingSuccessorRelation S V K Labels C D rD ↔
      source ∈ S ∧ target ∈ S ∧ z ∈ V ∧
        TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z := by
  rw [taskBearingSuccessorRelation, M.pair_mem_definableRelation]
  have params := M.taskBearingSuccessorParams_ground separation infinite hS hV hK hLabels hC hD hrD
  have hVV := M.prod_mem pairing unions powers separation hV hV
  have recognized (hs : source ∈ S) (hp : ZFSet.pair target z ∈ ZFSet.prod V V) :=
    M.realize_taskBearingSuccessorPairFormula pairing unions powers separation collection
      2 3 4 5 6 7 8 9 0 1
      (extend source (extend (ZFSet.pair target z) (taskBearingSuccessorParams S V K Labels C D rD)))
      (Fin.cases (M.transitive hS hs) (Fin.cases (M.transitive hVV hp) params)) rfl ordinal
  constructor
  · rintro ⟨hs, hp, relation⟩
    obtain ⟨t, ht, w, hw, equal, code⟩ := (recognized hs hp).1 relation
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hs, ht, hw, code⟩
  · rintro ⟨hs, ht, hz, code⟩
    have hp := ZFSet.pair_mem_prod.2 ⟨subset ht, hz⟩
    exact ⟨hs, hp, (recognized hs hp).2 ⟨target, ht, z, hz, rfl, code⟩⟩

theorem choose_taskBearingSuccessors
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {S V K Labels C D rD : ZFSet.{u}} (hS : S ∈ M.sets) (hV : V ∈ M.sets)
    (hK : K ∈ M.sets) (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (ordinal : ordinalSetProperty K) (subset : S ⊆ V)
    (total : ∀ source ∈ S, ∃ target ∈ S, ∃ z ∈ V,
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z) :
    ∃ f ∈ M.sets, ZFSet.IsFunc S (ZFSet.prod V V) f ∧
      f ⊆ M.taskBearingSuccessorRelation S V K Labels C D rD ∧
      ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
        target ∈ S ∧ z ∈ V ∧
          TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z := by
  have entries := M.taskBearingSuccessorRelation_entry pairing unions powers separation collection infinite
    hS hV hK hLabels hC hD hrD ordinal subset
  obtain ⟨f, hf, function, included⟩ := M.uniformize_relation pairing unions powers separation choice
    hS (M.prod_mem pairing unions powers separation hV hV)
    (M.taskBearingSuccessorRelation_ground pairing unions powers separation infinite hS hV hK hLabels hC hD hrD)
    (by
      intro source hs
      obtain ⟨target, ht, z, hz, code⟩ := total source hs
      exact ⟨ZFSet.pair target z, ZFSet.pair_mem_prod.2 ⟨subset ht, hz⟩,
        (entries source target z).2 ⟨hs, ht, hz, code⟩⟩)
  exact ⟨f, hf, function, included, fun source target z entry =>
    ((entries source target z).1 (included entry)).2⟩

end TransitiveGround
end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialMainSeedSuccessorRanked
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
          ∃ initial : GroundSerializedChronology M (insert seed.source.cutoff seed.source.cutoff)
              C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
            ∃ successor : GroundSerializedChronology M
                (insert certificate.target.cutoff certificate.target.cutoff)
                C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
              level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∈ M.sets ∧
              initial.code ∈ M.sets ∧ ZFSet.rank initial.code < ZFSet.rank K ∧
              initial.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              (∀ j t, t ∈ insert seed.source.cutoff seed.source.cutoff →
                initial.fields.value j t = seed.source.history.fieldValue j t) ∧
              successor.code ∈ M.sets ∧ ZFSet.rank successor.code < ZFSet.rank K ∧
              successor.code ∈ level.validChronologies C (rationalCarrier seed.fractionCode)
                (rationalLtGraph seed.fractionCode) ∧
              (∀ j t, t ∈ insert certificate.target.cutoff certificate.target.cutoff →
                successor.fields.value j t = certificate.target.history.fieldValue j t) ∧
              certificate.target.Invariant K C ∧
              ZFSet.rank certificate.transition.map.code < ZFSet.rank K ∧
              successor.fields.value 0 certificate.target.cutoff = certificate.target.stage.carrier ∧
              successor.fields.value 1 certificate.target.cutoff = certificate.target.stage.order ∧
              successor.fields.value 2 certificate.target.cutoff = certificate.target.stage.meetGraph ∧
              successor.fields.value 3 certificate.target.cutoff = certificate.target.birth ∧
              successor.fields.value 4 certificate.target.cutoff = certificate.target.stage.height := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨level⟩ := M.exists_groundMainCandidateLevel pairing unions powers separation collection hK conditions.1
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite collection hK conditions
  obtain ⟨initial, initialGround, initialRank, initialAgreement⟩ :=
    seed.exists_matchedInitialSerialization pairing unions powers separation infinite hK conditions
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice seed.source hC seed.injection_ground seed.dense
    (fun lo hlo => (seed.no_endpoints lo hlo).2) seed.injection_code
  obtain ⟨successor, successorGround, successorRank, successorMember, successorAgreement, terminal⟩ :=
    certificate.exists_rankedTargetSerialization pairing unions powers separation collection infinite choice
      hK conditions seed.invariant level initial initialRank initialAgreement
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite
    choice hC hK standard seed.invariant
  have transitionRank := certificate.transition.map.code_rank_lt_inaccessible pairing unions powers separation infinite
    hK conditions seed.invariant.points_rank invariant.points_rank seed.invariant.actors_rank invariant.actors_rank
  exact ⟨level, seed, certificate, initial, successor,
    level.validChronologies_ground pairing unions powers separation infinite seed.source.stage.columns_ground
      seed.source.stage.coordinates_ground seed.source.stage.coordinate_order_ground,
    initialGround, initialRank, level.ranked_mem_validChronologies pairing initial initialRank, initialAgreement,
    successorGround, successorRank, successorMember, successorAgreement, invariant, transitionRank, terminal⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_rankedTaskBearingSuccessor {K Labels D rD c : ZFSet.{u}}
    (source : GroundLinkedMainStage M K Labels C D rD)
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hLabels : Labels ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K) :
    ∃ certificate : GroundInitialMainSuccessorData M C D rD source.main Labels,
      ∃ target : GroundLinkedMainStage M K Labels C D rD,
        target.main = certificate.target ∧
        target.code ∈ M.linkedMainStageCandidates level.carrier K Labels C D rD ∧
        certificate.transition.map.code ∈ level.carrier ∧
        TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
          source.code target.code certificate.transition.map.code := by
  obtain ⟨certificate⟩ := M.exists_groundInitialMainSuccessor pairing unions powers separation
    collection infinite choice source.main hLabels hc dense above coordinateInjection
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨serial, _, serialRank, _, agreement, _⟩ :=
    certificate.exists_rankedTargetSerialization pairing unions powers separation collection infinite choice
      hK conditions source.invariant level source.serial source.serial_rank source.agreement
  have invariant := certificate.target_invariant pairing unions powers separation collection infinite choice
    hLabels hK standard source.invariant
  obtain ⟨target, same, code⟩ := certificate.exists_taskBearingLinkedTarget
    pairing unions powers separation infinite hLabels serial agreement invariant serialRank
  have targetBound : target.code ∈ level.carrier := (level.membership _).2
    ⟨target.code_ground pairing, target.code_rank_lt pairing unions powers separation infinite hK conditions⟩
  have transitionBound : certificate.transition.map.code ∈ level.carrier := (level.membership _).2
    ⟨certificate.transition.map.code_mem pairing,
      certificate.transition_code_rank_lt pairing unions powers separation collection infinite
        hK conditions source.invariant.points_rank source.invariant.labels_rank source.invariant.actors_rank⟩
  exact ⟨certificate, target, same,
    (M.mem_linkedMainStageCandidates level.carrier K Labels C D rD target.code).2
      ⟨targetBound, target, rfl⟩, transitionBound, code⟩

include choice in
theorem omegaOne_taskBearingSuccessor_total {K D rD c : ZFSet.{u}}
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K)
    {s : ZFSet.{u}} (hs : s ∈ M.linkedMainStageCandidates level.carrier K C C D rD) :
    ∃ t ∈ M.linkedMainStageCandidates level.carrier K C C D rD, ∃ z ∈ level.carrier,
      TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega s t z := by
  obtain ⟨_, source, sourceEq⟩ := (M.mem_linkedMainStageCandidates level.carrier K C C D rD s).1 hs
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  obtain ⟨certificate, target, _, targetMember, mapMember, code⟩ :=
    M.exists_rankedTaskBearingSuccessor pairing unions powers separation collection infinite choice
      source hK standard hC hc dense above coordinateInjection level
  exact ⟨target.code, targetMember, certificate.transition.map.code, mapMember, sourceEq ▸ code⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "C" => M.groundOmegaOne pairing unions powers separation collection infinite

include choice in
theorem exists_groundOmegaOneTaskBearingSuccessorFunction {K D rD c : ZFSet.{u}}
    (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K)
    (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (dense : DenseOrderCode D rD) (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c) (level : GroundMainCandidateLevel M K) :
    ∃ f ∈ M.sets,
      ZFSet.IsFunc (M.linkedMainStageCandidates level.carrier K C C D rD)
        (ZFSet.prod level.carrier level.carrier) f ∧
      f ⊆ M.taskBearingSuccessorRelation
        (M.linkedMainStageCandidates level.carrier K C C D rD) level.carrier K C C D rD ∧
      ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
        target ∈ M.linkedMainStageCandidates level.carrier K C C D rD ∧ z ∈ level.carrier ∧
          TaskBearingMainSuccessorCode M K C C D rD ZFSet.omega source target z := by
  have hC := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  have hS := M.linkedMainStageCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hC hC hD hrD standard.1.1
  apply M.choose_taskBearingSuccessors pairing unions powers separation collection infinite choice
    hS level.carrier_ground hK hC hC hD hrD standard.1.1
  · intro s hs
    exact ((M.mem_linkedMainStageCandidates level.carrier K C C D rD s).1 hs).1
  · intro s hs
    exact M.omegaOne_taskBearingSuccessor_total pairing unions powers separation collection infinite choice
      hK standard hc dense above coordinateInjection level hs

end PartitionPilot.Forcing.TransitiveGround

end OAI
