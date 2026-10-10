import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundInitialMainStage
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageInvariant

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
open scoped ZFSet
universe u

theorem fractionCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (omega : ZFSet.rank ZFSet.omega < o) : ZFSet.rank (fractionCarrier.{u}) < o := by
  have subset : fractionCarrier.{u} ⊆ ZFSet.prod ZFSet.omega ZFSet.omega := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, (ZFSet.mem_sep.1 hy).1⟩
  exact (ZFSet.rank_mono subset).trans_lt (rank_product_lt limit omega omega)

theorem rationalCarrier_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (c : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o) :
    ZFSet.rank (rationalCarrier c) < o :=
  (ZFSet.rank_mono (rationalCarrier_subset c)).trans_lt (fractionCarrier_rank_lt limit omega)

theorem rationalLtGraph_rank_lt {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
    (c : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o) :
    ZFSet.rank (rationalLtGraph c) < o :=
  (ZFSet.rank_mono (rationalLtGraph_subset c)).trans_lt
    (rank_product_lt limit (rationalCarrier_rank_lt limit c omega)
      (rationalCarrier_rank_lt limit c omega))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rational_seed_pair {c : ZFSet.{u}}
    (carrier : rationalCarrier c ∈ M.sets) (code : InjectionCode fractionCarrier ZFSet.omega c) :
    ∃ d0 ∈ M.sets, ∃ d1 ∈ M.sets,
      d0 ∈ rationalCarrier c ∧ d1 ∈ rationalCarrier c ∧ ZFSet.pair d0 d1 ∈ rationalLtGraph c := by
  obtain ⟨d0, h0⟩ := rationalCarrier_nonempty code
  obtain ⟨d1, h1, gap⟩ := (rational_no_endpoints code d0 h0).2
  exact ⟨d0, M.transitive carrier h0, d1, M.transitive carrier h1, h0, h1, gap⟩

theorem exists_groundRationalSeed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    ∃ c ∈ M.sets, InjectionCode fractionCarrier ZFSet.omega c ∧
      rationalCarrier c ∈ M.sets ∧ rationalLtGraph c ∈ M.sets ∧
      ∃ f ∈ M.sets, InjectionCode (rationalCarrier c) ZFSet.omega f ∧
        DenseOrderCode (rationalCarrier c) (rationalLtGraph c) ∧
        ZFSet.rank (rationalCarrier c) < ZFSet.rank K ∧
        ZFSet.rank (rationalLtGraph c) < ZFSet.rank K ∧
        (∀ x ∈ rationalCarrier c,
          (∃ y ∈ rationalCarrier c, ZFSet.pair y x ∈ rationalLtGraph c) ∧
          (∃ y ∈ rationalCarrier c, ZFSet.pair x y ∈ rationalLtGraph c)) ∧
        ∃ d0 ∈ M.sets, ∃ d1 ∈ M.sets,
          d0 ∈ rationalCarrier c ∧ d1 ∈ rationalCarrier c ∧ ZFSet.pair d0 d1 ∈ rationalLtGraph c := by
  obtain ⟨c, hc, code⟩ := M.fractionCarrier_countable pairing unions powers separation infinite
  have carrier := M.rationalCarrier_mem pairing unions powers separation infinite hc
  have relation := M.rationalLtGraph_mem pairing unions powers separation infinite hc
  have injection := M.canonicalRepresentativesInjection_mem separation
    (M.fractionCarrier_mem pairing unions powers separation infinite)
    (M.fractionEquivGraph_mem pairing unions powers separation infinite) hc
    (M.omega_mem separation infinite)
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have omega := ZFSet.rank_lt_of_mem conditions.2.1
  exact ⟨c, hc, code, carrier, relation,
    canonicalRepresentativesInjection fractionCarrier fractionEquivGraph c, injection,
    canonicalRepresentativesInjection_code code, rational_denseOrderCode code,
    rationalCarrier_rank_lt limit c omega, rationalLtGraph_rank_lt limit c omega,
    rational_no_endpoints code, M.rational_seed_pair carrier code⟩

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

structure GroundInitialMainSeedData (M : TransitiveGround.{u}) (K C : ZFSet.{u}) where
  fractionCode : ZFSet.{u}
  fraction_ground : fractionCode ∈ M.sets
  fraction_injection : InjectionCode fractionCarrier ZFSet.omega fractionCode
  coordinateInjection : ZFSet.{u}
  injection_ground : coordinateInjection ∈ M.sets
  injection_code : InjectionCode (rationalCarrier fractionCode) ZFSet.omega coordinateInjection
  dense : DenseOrderCode (rationalCarrier fractionCode) (rationalLtGraph fractionCode)
  no_endpoints : ∀ x ∈ rationalCarrier fractionCode,
    (∃ y ∈ rationalCarrier fractionCode, ZFSet.pair y x ∈ rationalLtGraph fractionCode) ∧
    (∃ y ∈ rationalCarrier fractionCode, ZFSet.pair x y ∈ rationalLtGraph fractionCode)
  lo : ZFSet.{u}
  hi : ZFSet.{u}
  lo_mem : lo ∈ rationalCarrier fractionCode
  hi_mem : hi ∈ rationalCarrier fractionCode
  gap : ZFSet.pair lo hi ∈ rationalLtGraph fractionCode
  source : GroundChronologicalMainStage M C (rationalCarrier fractionCode) (rationalLtGraph fractionCode)
  points_eq : source.stage.carrier = natSetCode 2
  actors_eq : source.stage.actors = natSetCode 1
  bottom_eq : source.stage.bottom = natSetCode 0
  top_eq : source.stage.top = natSetCode 1
  stage_code : source.stage.code = mainStageCode InitialMainAlgebra.carrier InitialMainAlgebra.order
    InitialMainAlgebra.meetGraph InitialMainAlgebra.actors InitialMainAlgebra.multiplication
    InitialMainAlgebra.inverse InitialMainAlgebra.identity InitialMainAlgebra.action
    InitialMainAlgebra.bottom InitialMainAlgebra.top
    (twoPointHeight InitialMainAlgebra.bottom InitialMainAlgebra.top ∅ lo hi)
  cutoff_zero : source.cutoff = ∅
  birth_eq : source.birth = constantFamilyGraph (natSetCode 2) ∅
  invariant : source.Invariant K C

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

theorem initialMainChronological_invariant {K C D rD c d0 d1 Labels : ZFSet.{u}}
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) (gap : ZFSet.pair d0 d1 ∈ rD)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    (labels : GroundBelow M Labels K) (labelRank : ZFSet.rank Labels < ZFSet.rank K)
    (columnRank : ZFSet.rank C < ZFSet.rank K) (coordinateRank : ZFSet.rank D < ZFSet.rank K) :
    (M.initialMainChronological pairing unions powers separation infinite hC hD hrD hc h0 h1 gap).Invariant K Labels := by
  have points := conditions.finite_seed_bounds pairing unions powers separation infinite hK 2
  have actors := conditions.finite_seed_bounds pairing unions powers separation infinite hK 1
  have zero : (∅ : ZFSet.{u}) ∈ K :=
    conditions.1.1 ZFSet.omega conditions.2.1 _ (natSetCode_mem_omega 0)
  exact ⟨points.2.2.1, actors.2.2.1, labels, points.2.2.2, actors.2.2.2,
    labelRank, zero, columnRank, coordinateRank⟩

theorem exists_groundInitialMainSeed (collection : CollectionSchema M.sets)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K) :
    Nonempty (GroundInitialMainSeedData M K
      (M.groundOmegaOne pairing unions powers separation collection infinite)) := by
  obtain ⟨c, hc, fraction, hD, hrD, f, hf, injection, dense, rankD, _rankR, endpoints,
    lo, _hlo, hi, _hhi, loMem, hiMem, gap⟩ :=
    M.exists_groundRationalSeed pairing unions powers separation infinite hK conditions
  let C := M.groundOmegaOne pairing unions powers separation collection infinite
  have spec := M.groundOmegaOne_spec pairing unions powers separation collection infinite
  have column : (∅ : ZFSet.{u}) ∈ C := (spec.2.2.1 ∅).2
    ⟨M.empty_mem ⟨C, spec.1⟩, ordinalSetProperty_empty,
      M.empty_groundEmbeddable ZFSet.omega ⟨C, spec.1⟩⟩
  have labelSize := conditions.groundOmegaOne_below pairing unions powers separation collection infinite hK
  have columnRank := ZFSet.rank_lt_of_mem
    (conditions.groundOmegaOne_mem pairing unions powers separation collection infinite hK)
  let source := M.initialMainChronological pairing unions powers separation infinite
    spec.1 hD hrD column loMem hiMem gap
  exact ⟨{
    fractionCode := c
    fraction_ground := hc
    fraction_injection := fraction
    coordinateInjection := f
    injection_ground := hf
    injection_code := injection
    dense := dense
    no_endpoints := endpoints
    lo := lo
    hi := hi
    lo_mem := loMem
    hi_mem := hiMem
    gap := gap
    source := source
    points_eq := rfl
    actors_eq := rfl
    bottom_eq := rfl
    top_eq := rfl
    stage_code := rfl
    cutoff_zero := rfl
    birth_eq := rfl
    invariant := M.initialMainChronological_invariant pairing unions powers separation infinite
      spec.1 hD hrD column loMem hiMem gap hK conditions labelSize columnRank columnRank rankD }⟩

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

theorem exists_groundInitialMainSeedSerialized
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    {K : ZFSet.{u}} (hK : K ∈ M.sets) (standard : GroundStandardInaccessible M K) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ seed : GroundInitialMainSeedData M K C,
      ∃ serial : GroundSerializedChronology M (insert (∅ : ZFSet.{u}) ∅)
          C (rationalCarrier seed.fractionCode) (rationalLtGraph seed.fractionCode),
        serial.code ∈ M.sets ∧ serial.fields.graph = seed.source.stage.initialChronologyGraph ∧
          serial.toHistory.space ∅ = seed.source.stage.carrier ∧
          serial.toHistory.order ∅ = seed.source.stage.order ∧
          serial.toHistory.meetGraph ∅ = seed.source.stage.meetGraph ∧
          serial.toHistory.birth ∅ = seed.source.birth ∧
          serial.toHistory.height ∅ = seed.source.stage.height := by
  dsimp only
  have conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨seed⟩ := M.exists_groundInitialMainSeed pairing unions powers separation infinite
    collection hK conditions
  have small : M.groundEmbeddable seed.source.stage.carrier ZFSet.omega := by
    rw [seed.points_eq]
    exact M.natSetCode_countable pairing unions powers separation infinite 2
  obtain ⟨serial, ground, graph, carrier, order, meet, birth, height⟩ :=
    seed.source.stage.exists_initialSerializedChronology pairing unions powers separation small
  have birthEq : seed.source.stage.initialBirth = seed.source.birth := by
    rw [GroundMainStage.initialBirth, seed.points_eq, seed.birth_eq]
  exact ⟨seed, serial, ground, graph, carrier, order, meet, birth.trans birthEq, height⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula SetRealization
open scoped ZFSet
universe u
namespace GroundInitialMainSeedData
variable {M : TransitiveGround.{u}} {K C : ZFSet.{u}}
variable (seed : GroundInitialMainSeedData M K C)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include infinite hK conditions

theorem initialSerializedChronology_code_rank_lt {injection : ZFSet.{u}}
    (hInjection : injection ∈ M.sets)
    (injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection) :
    ZFSet.rank (seed.source.stage.initialSerializedChronology pairing unions powers separation
      hInjection injected).code < ZFSet.rank K := by
  have limit := conditions.rank_isLimit pairing unions powers separation infinite hK
  have height := rank_functionGraph_lt limit seed.source.stage.height_code.function
    seed.invariant.points_rank (rank_product_lt limit seed.invariant.columns_rank seed.invariant.coordinates_rank)
  exact seed.source.stage.initialSerializedChronology_code_rank_lt_inaccessible
    pairing unions powers separation hInjection injected infinite hK conditions seed.invariant.points_rank height

theorem exists_rankedInitialSerialization :
    ∃ injection ∈ M.sets, ∃ injected : InjectionCode seed.source.stage.carrier ZFSet.omega injection,
      ∃ hInjection : injection ∈ M.sets,
        let serial := seed.source.stage.initialSerializedChronology pairing unions powers separation hInjection injected
        serial.code ∈ M.sets ∧ ZFSet.rank serial.code < ZFSet.rank K ∧
          serial.fields.graph = seed.source.stage.initialChronologyGraph ∧
          serial.toHistory.space ∅ = seed.source.stage.carrier ∧
          serial.toHistory.order ∅ = seed.source.stage.order ∧
          serial.toHistory.meetGraph ∅ = seed.source.stage.meetGraph ∧
          serial.toHistory.birth ∅ = seed.source.birth ∧
          serial.toHistory.height ∅ = seed.source.stage.height := by
  have small : M.groundEmbeddable seed.source.stage.carrier ZFSet.omega := by
    rw [seed.points_eq]
    exact M.natSetCode_countable pairing unions powers separation infinite 2
  obtain ⟨injection, hInjection, injected⟩ := small
  have values := seed.source.stage.initialSerializedChronology_values pairing unions powers separation
    hInjection injected (ZFSet.mem_insert _ _)
  have birth : seed.source.stage.initialBirth = seed.source.birth := by
    rw [GroundMainStage.initialBirth, seed.points_eq, seed.birth_eq]
  exact ⟨injection, hInjection, injected, hInjection,
    seed.source.stage.initialSerializedChronology_code_ground pairing unions powers separation hInjection injected,
    seed.initialSerializedChronology_code_rank_lt pairing unions powers separation infinite hK conditions hInjection injected,
    rfl, values.1, values.2.1, values.2.2.1, values.2.2.2.1.trans birth, values.2.2.2.2⟩

end GroundInitialMainSeedData
end PartitionPilot.Forcing

end OAI
