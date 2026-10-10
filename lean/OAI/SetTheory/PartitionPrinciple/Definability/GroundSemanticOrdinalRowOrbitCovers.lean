import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralDataSupport
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowTupleEvaluation
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSelectedOrbitNameFamilies
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalPartialMapCovers

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

private theorem acted_pair (g : G) (x y : Name s) :
    a.act s g (Name.orderedPair ⊤ x y) = Name.orderedPair ⊤ (a.act s g x) (a.act s g y) := by
  change Name.rename s (a.iso g) (Name.orderedPair ⊤ x y) = _
  rw [Name.rename_orderedPair, (a.iso g).map_top]
  rfl

theorem orbitPairGraph_code_eq (tuple tau : Name s)
    (jointGround : (Name.orderedPair ⊤ tuple tau).val ∈ M.sets) :
    (Name.orbitPairGraph a s tuple tau).val =
      ZFSet.prod (a.orbitCodes s (M.nameDomain s) {(Name.orderedPair ⊤ tuple tau).val})
        {s.encode ⊤} := by
  have orbitMembers (y : ZFSet.{u}) :
      y ∈ a.orbitCodes s (M.nameDomain s) {(Name.orderedPair ⊤ tuple tau).val} ↔
        ∃ g : G, y = (Name.orderedPair ⊤ (a.act s g tuple) (a.act s g tau)).val := by
    rw [a.mem_orbitCodes]
    constructor
    · rintro ⟨g, sigma, _ground, member, equal⟩
      have same : sigma = Name.orderedPair ⊤ tuple tau := Subtype.ext (ZFSet.mem_singleton.1 member)
      rw [same, acted_pair] at equal
      exact ⟨g, equal⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, Name.orderedPair ⊤ tuple tau, jointGround, ZFSet.mem_singleton.2 rfl,
        (congrArg Subtype.val (acted_pair a s g tuple tau)).symm⟩
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨sigma, p, code⟩ := Name.entries_cover (Name.orbitPairGraph a s tuple tau) member
    have entry : Name.Entry sigma (Name.orbitPairGraph a s tuple tau) p := by
      change ZFSet.pair sigma.val (s.encode p) ∈ (Name.orbitPairGraph a s tuple tau).val
      exact code ▸ member
    obtain ⟨g, rfl, rfl⟩ := (Name.entry_orbitPairGraph a s tuple tau sigma p).1 entry
    rw [code, ZFSet.pair_mem_prod]
    exact ⟨(orbitMembers _).2 ⟨g, rfl⟩, ZFSet.mem_singleton.2 rfl⟩
  · intro member
    obtain ⟨x, hx, y, hy, shape⟩ := ZFSet.mem_prod.1 member
    obtain ⟨g, rfl⟩ := (orbitMembers x).1 hx
    have topEq := ZFSet.mem_singleton.1 hy
    rw [topEq] at shape
    have entry := (Name.entry_orbitPairGraph a s tuple tau _ ⊤).2 ⟨g, rfl, rfl⟩
    change ZFSet.pair (Name.orderedPair ⊤ (a.act s g tuple) (a.act s g tau)).val
      (s.encode ⊤) ∈ (Name.orbitPairGraph a s tuple tau).val at entry
    exact shape.symm ▸ entry

theorem orbitPairGraph_ground_hs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (F : NormalSubgroupFamily G) (tuple tau : Name s)
    (tupleGround : tuple.val ∈ M.sets) (tauGround : tau.val ∈ M.sets)
    (tupleHS : HereditarilySymmetric a s F tuple) (tauHS : HereditarilySymmetric a s F tau) :
    (Name.orbitPairGraph a s tuple tau).val ∈ M.sets ∧
      (∀ g : G, a.act s g (Name.orbitPairGraph a s tuple tau) = Name.orbitPairGraph a s tuple tau) ∧
      HereditarilySymmetric a s F (Name.orbitPairGraph a s tuple tau) ∧
      ∀ (H : Set P), (⊤ : P) ∈ H → ∀ z : ZFSet.{u},
        z ∈ Name.eval H (Name.orbitPairGraph a s tuple tau) ↔
          ∃ g : G, ZFSet.pair (Name.eval H (a.act s g tuple))
            (Name.eval H (a.act s g tau)) = z := by
  have topGround : s.encode (⊤ : P) ∈ M.sets := M.transitive carrier (s.encode_mem ⊤)
  have pairGround : (Name.orderedPair ⊤ tuple tau).val ∈ M.sets := by
    rw [Name.orderedPair_code]
    exact M.orderedPairNameCode_mem pairing topGround tupleGround tauGround
  have singletonGround : ({(Name.orderedPair ⊤ tuple tau).val} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing pairGround pairGround
  have orbitGround := M.orbitCodes_mem a s t pairing unions powers separation collection
    carrier group maps {(Name.orderedPair ⊤ tuple tau).val} singletonGround
  have ground : (Name.orbitPairGraph a s tuple tau).val ∈ M.sets := by
    rw [M.orbitPairGraph_code_eq a s tuple tau pairGround]
    apply M.prod_mem pairing unions powers separation orbitGround
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing topGround topGround
  exact ⟨ground, Name.act_orbitPairGraph a s tuple tau,
    Name.orbitPairGraph_hs a s F tuple tau tupleHS tauHS,
    fun H htop z => Name.mem_eval_orbitPairGraph a s tuple tau H htop z⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowTuple_equal_relativeFix
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (delta : ZFSet.{u}) (positions : delta.toSet → {i : L // i ≠ ⊥}) (D : L)
    (covers : ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let lower := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))),
      H.GenericFor (M.codedFamily lower) → ∀ g h : G,
      Name.eval {p | H.mem p} (act.act lower g (M.internalRowTupleName s C hL delta positions)) =
        Name.eval {p | H.mem p} (act.act lower h (M.internalRowTupleName s C hL delta positions)) →
      h⁻¹ * g ∈ a.principalFix D := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act lower H generic g h equal
  rw [M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph,
    M.internalRowTupleName_action a s b C pairing unions powers separation infinite hL hC hG graph] at equal
  have coordinates := (M.internalRowTupleName_eval_eq_iff s C hL pairing unions powers separation
    infinite choice hC uncountable delta (fun i => a.nonbottom.iso g (positions i))
      (fun i => a.nonbottom.iso h (positions i)) H generic).1 equal
  intro v below
  by_cases bottom : v = ⊥
  · subst v
    exact (a.iso (h⁻¹ * g)).map_bot
  · obtain ⟨i, atPosition⟩ := covers v bottom below
    have aligned : a.iso g v = a.iso h v := by
      have value := congrArg Subtype.val (congrFun coordinates i)
      change a.iso g (positions i).val = a.iso h (positions i).val at value
      simpa only [atPosition] using value
    rw [a.mul, aligned, a.point_inv_left]

theorem liftedRowOrbit_function
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (delta : ZFSet.{u}) (positions : delta.toSet → {i : L // i ≠ ⊥}) (D : L)
    (covers : ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v)
    {Upper : Type u} [PartialOrder Upper] [OrderTop Upper]
    (upper : Presentation Upper) (e : PosetAction G Upper) (upperGround : upper.carrier ∈ M.sets) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let lower := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (restriction : Upper →o SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (inclusion : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega) ↪o Upper)
      (_projection : CompleteProjection restriction inclusion),
      upper.graph lower restriction ∈ M.sets →
      (∀ g p, inclusion (act.iso g p) = e.iso g (inclusion p)) →
      ∀ (H : ConditionFilter Upper), H.GenericFor (formulaFamily (M.nameDomain upper)) →
      ∀ (tau : Name upper), a.principalFix D ≤ e.stabilizer upper tau →
      let tuple := Name.rename upper inclusion (M.internalRowTupleName s C hL delta positions)
      ZFSet.IsFunc (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (e.act upper g tuple)))
        (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (e.act upper g tau)))
        (Name.eval {p | H.mem p} (Name.orbitPairGraph e upper tuple tau)) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act lower restriction inclusion projection restrictionGround equivariant H ordinary tau supported tuple
  have lowerGround : lower.carrier ∈ M.sets :=
    M.countablePartialFunctions_mem pairing unions powers separation infinite
      (M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC)
      (M.natSetCode_mem separation infinite 2)
  have generic := M.completeProjection_codedGeneric_of_ordinary upper lower projection
    pairing unions powers separation upperGround lowerGround restrictionGround H ordinary
  have sameTarget (g h : G)
      (equal : Name.eval {p | H.mem p} (e.act upper g tuple) =
        Name.eval {p | H.mem p} (e.act upper h tuple)) : e.act upper g tau = e.act upper h tau := by
    have lowerEqual :
        Name.eval {p | (projection.projectedFilter H).mem p}
          (act.act lower g (M.internalRowTupleName s C hL delta positions)) =
        Name.eval {p | (projection.projectedFilter H).mem p}
          (act.act lower h (M.internalRowTupleName s C hL delta positions)) := by
      change Name.eval {p | H.mem p} (e.act upper g (Name.rename upper inclusion _)) =
        Name.eval {p | H.mem p} (e.act upper h (Name.rename upper inclusion _)) at equal
      rw [act.act_rename_of_equivariant e lower upper inclusion equivariant,
        act.act_rename_of_equivariant e lower upper inclusion equivariant,
        Name.eval_rename, Name.eval_rename] at equal
      exact equal
    have relative := M.internalRowTuple_equal_relativeFix a s b C pairing unions powers separation infinite
      hL hC hG graph choice uncountable delta positions D covers
      (projection.projectedFilter H) generic g h lowerEqual
    have fixed : e.act upper (h⁻¹ * g) tau = tau := supported relative
    have moved := congrArg (e.act upper h) fixed
    rw [← e.act_mul, mul_inv_cancel_left] at moved
    exact moved
  constructor
  · intro z member
    obtain ⟨g, rfl⟩ := (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem z).1 member
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_range.2 ⟨g, rfl⟩, ZFSet.mem_range.2 ⟨g, rfl⟩⟩
  · intro x member
    obtain ⟨g, rfl⟩ := ZFSet.mem_range.1 member
    refine ⟨Name.eval {p | H.mem p} (e.act upper g tau),
      (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem _).2 ⟨g, rfl⟩, ?_⟩
    intro y entry
    obtain ⟨h, equal⟩ := (Name.mem_eval_orbitPairGraph e upper tuple tau {p | H.mem p} H.top_mem _).1 entry
    have parts := ZFSet.pair_inj.1 equal
    exact parts.2.symm.trans (congrArg (Name.eval {p | H.mem p}) (sameTarget h g parts.1))

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R L : Type u}
variable [Group G] [PartialOrder R] [PartialOrder L]
variable (c : Presentation R) (a : PosetAction G R) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (T T2 rowTop : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : c.carrier ∈ M.sets) (rowOrderGround : c.conditionOrder ∈ M.sets)
variable (rowAction : a.actionGraph c t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (nodeOrder : b.conditionOrder ∈ M.sets) (nodeAction : d.actionGraph b t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
variable (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
variable (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T →
  (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 →
  (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "Q" => M.refinementHistoryForcing c.carrier T stages packed
local notation "upper" => SetMembers.presentation Q
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
  t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
  T T2 ordinal trace
local notation "rowFunction" => M.refinementHistoryRowFunction c T stages packed
local notation "rowInclusion" => M.refinementHistoryRowInclusion c (RecursiveRefinementOrderHistory.carriers run) ordinal carrier
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hs hh ordinal trace
include hs hh ordinal trace infinite choice

theorem semanticStructuralTrace_rowProjection :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    CompleteProjection (M.refinementHistoryRowRestriction c T stages packed)
        (M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier) ∧
      (upper).graph c rowFunction ∈ M.sets ∧
      c.graph upper rowInclusion ∈ M.sets ∧
      (∀ p row A, SetMembers.raw p = ZFSet.pair (c.encode row) A → rowFunction p = row) ∧
      (∀ row, (upper).encode (rowInclusion row) = ZFSet.pair (c.encode row) ∅) ∧
      (∀ g p, rowFunction ((upperAct).iso g p) = a.iso g (rowFunction p)) ∧
      (∀ g row, rowInclusion (a.iso g row) = (upperAct).iso g (rowInclusion row)) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  have mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have projection := M.refinementHistoryRow_completeProjection c T stages packed run ordinal carrier
    pairing unions powers separation infinite choice hs hPacked hT rowTop topMem topRows mono
  have hQ := M.refinementHistoryForcing_mem pairing unions powers separation carrier hT hs hPacked omega
  have grounds := M.refinementHistoryRowGraphs_mem c T stages packed run ordinal carrier
    pairing unions powers separation hQ
  have equivariant : ∀ g p,
      rowFunction ((upperAct).iso g p) = a.iso g (rowFunction p) := by
    intro g p
    obtain ⟨A, code⟩ := M.refinementHistoryRowFunction_coordinates c T stages packed p
    exact M.refinementHistoryRowFunction_code c T stages packed ((upperAct).iso g p)
      (a.iso g (rowFunction p))
      (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A)
      (M.semanticStructuralAction_coordinates c a t b d base directed T T2 rowTop
        pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
        nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
        topMem topRows hs hh ordinal trace g p (rowFunction p) A code)
  refine ⟨projection, grounds.1, grounds.2,
    M.refinementHistoryRowFunction_code c T stages packed,
    M.refinementHistoryRowInclusion_encode c (RecursiveRefinementOrderHistory.carriers run) ordinal carrier,
    equivariant, ?_⟩
  intro g row
  exact (projection.inclusion_equivariant upperAct a equivariant g row).symm

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_orbit_function
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (delta f : ZFSet.{u}) (hDelta : delta ∈ M.sets) (hf : f ∈ M.sets)
    (function : FunctionGraphOn delta f) (positions : delta.toSet → {i : L // i ≠ ⊥})
    (values : ∀ i, function.value i = s.encode (positions i).val) (D : L)
    (bounded : ∀ i, (positions i).val ≤ D)
    (covers : ∀ v : L, v ≠ ⊥ → v ≤ D → ∃ i, (positions i).val = v) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let tuple := Name.rename upper inclusion (M.internalRowTupleName s C hL delta positions)
    ∀ (tau : Name upper), tau.val ∈ M.sets →
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tau →
      a.principalFix D ≤ upperAct.stabilizer upper tau →
      let orbit := Name.orbitPairGraph upperAct upper tuple tau
      tuple.val ∈ M.sets ∧ orbit.val ∈ M.sets ∧
        (∀ g, upperAct.act upper g orbit = orbit) ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) orbit ∧
        ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          ZFSet.IsFunc (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (upperAct.act upper g tuple)))
            (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (upperAct.act upper g tau)))
            (Name.eval {p | H.mem p} orbit) ∧
          Name.eval {p | H.mem p} orbit ∈ (M.symmetricExtension upper upperAct
            (a.principalSupportFamily ⊥ directed) H).sets ∧
          (∀ z, z ∈ Name.eval {p | H.mem p} orbit ↔ ∃ g : G,
            ZFSet.pair (Name.eval {p | H.mem p} (upperAct.act upper g tuple))
              (Name.eval {p | H.mem p} (upperAct.act upper g tau)) = z) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
  intro act c T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed run
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier (c.encode ⊤) topMem topRows
  intro upper upperAct inclusion tuple tau tauGround tauHS supported orbit
  have rowProjection := M.semanticStructuralTrace_rowProjection c act b s a ⊥ directed T T2 (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hs hh ordinal trace infinite choice
  obtain ⟨projection, restrictionGround, inclusionGround, _, _, _, equivariant⟩ := rowProjection
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hT hT2 hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    have graphEq := M.semanticStructuralAction_graph c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace
    change upperAct.actionGraph upper b = _ at graphEq
    rw [graphEq]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have sourceGround := M.internalRowTupleName_mem s C pairing unions powers separation collection
    infinite hL hC delta f hDelta hf function positions values
  have tupleGround : tuple.val ∈ M.sets := M.rename_between_mem c upper pairing unions powers separation
    collection carrier hQ inclusion inclusionGround _ sourceGround
  have sourceHS := M.internalRowTupleName_hs a s b C pairing unions powers separation infinite
    hL hC hG graph directed delta positions D bounded
  have tupleHS : HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tuple :=
    HereditarilySymmetric.rename upperAct upper inclusion equivariant sourceHS
  obtain ⟨orbitGround, fixed, orbitHS, entries⟩ := M.orbitPairGraph_ground_hs upperAct upper b
    pairing unions powers separation collection hQ hG maps (a.principalSupportFamily ⊥ directed)
    tuple tau tupleGround tauGround tupleHS tauHS
  refine ⟨tupleGround, orbitGround, fixed, orbitHS, ?_⟩
  intro H ordinary
  refine ⟨M.liftedRowOrbit_function a s b C pairing unions powers separation infinite hL hC hG graph
    choice uncountable delta positions D covers upper upperAct hQ
    (M.refinementHistoryRowRestriction c T stages packed) inclusion projection restrictionGround equivariant
    H ordinary tau supported, ?_, entries {p | H.mem p} H.top_mem⟩
  exact (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H _).2
    ⟨orbit, orbitGround, orbitHS, rfl⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_orbit_cover
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable s.nonbottom.carrier mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (W : ZFSet.{u}) (_hW : W ∈ M.sets) (validW : ∀ z ∈ W, IsName upper z),
      (∀ tau : Name upper, tau.val ∈ W → HereditarilySymmetric upperAct upper
        (a.principalSupportFamily ⊥ directed) tau) →
      ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
      ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
      let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
        (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
      rowName.val ∈ M.sets ∧
        (∀ g, upperAct.act upper g rowName = rowName) ∧
        HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) rowName ∧
      ∃ family ∈ M.sets, ∃ function : FunctionGraphOn W family,
      ∃ names : ∀ i, IsName upper (function.value i),
        (∀ g i, upperAct.act upper g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩) ∧
        (∀ i, HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed)
          ⟨function.value i, names i⟩) ∧
        ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          let sequence := Name.indexedGraphName (s := upper)
            (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) function names
          rowName.val ∈ M.sets ∧ sequence.val ∈ M.sets ∧
          HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sequence ∧
          Name.eval {p | H.mem p} rowName ∈ (M.symmetricExtension upper upperAct
            (a.principalSupportFamily ⊥ directed) H).sets ∧
          Name.eval {p | H.mem p} sequence ∈ (M.symmetricExtension upper upperAct
            (a.principalSupportFamily ⊥ directed) H).sets ∧
          ZFSet.IsFunc W (ZFSet.range (fun i : W =>
            Name.eval {p | H.mem p} ⟨function.value i, names i⟩)) (Name.eval {p | H.mem p} sequence) ∧
          ∀ i : W.toSet,
            let orbit := Name.eval {p | H.mem p} ⟨function.value i, names i⟩
            PartialFunctionCode (Name.eval {p | H.mem p} rowName) (⋃₀ ⋃₀ orbit) orbit ∧
            ∃ x ∈ Name.eval {p | H.mem p} rowName,
              ZFSet.pair x (Name.eval {p | H.mem p} ⟨i.val, validW i.val i.property⟩) ∈ orbit := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
  intro act c T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed run
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier (c.encode ⊤) topMem topRows
  intro upper upperAct inclusion rows S RowTerms W hW validW symmetricW
  have rowProjection := M.semanticStructuralTrace_rowProjection c act b s a ⊥ directed T T2 (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
    hs hh ordinal trace infinite choice
  have projection := rowProjection.1
  have restrictionGround := rowProjection.2.1
  have inclusionGround := rowProjection.2.2.1
  have equivariant := rowProjection.2.2.2.2.2.2
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs hPacked omega
  have hAssignments := (M.definable_structuralAssignments pairing unions powers separation collection).closed
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hAssignmentAction := M.structuralAssignmentActionGraph_mem pairing unions powers separation
    collection hG hL order graph supports hT hT2 hs hh
  have hGraph : upperAct.actionGraph upper b ∈ M.sets := by
    have graphEq := M.semanticStructuralAction_graph c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows
      hs hh ordinal trace
    change upperAct.actionGraph upper b = _ at graphEq
    rw [graphEq]
    exact M.rawRowAssignmentActionGraph_mem pairing unions powers separation collection hG hQ
      carrier (M.union_mem unions (M.union_mem unions hQ)) hAssignments forcingAction hAssignmentAction
  have maps := M.conditionMapFamily_mem_of_actionGraph upperAct upper b pairing unions powers separation
    collection hQ hG hGraph
  have hI := M.nonbottom_carrier_mem s separation hL
  have hS := M.rowPositionSequences_mem pairing unions powers separation hL order hI hmu
  have tupleGraphGround := M.binaryRowTupleFamily_mem pairing unions powers separation collection infinite
    hL order hI hC hmu ⊤
  have hRowTerms : RowTerms ∈ M.sets := M.rowTupleTerms_mem unions separation hS tupleGraphGround
  have rowData := M.binaryRowTupleTerms_hs a s b C pairing unions powers separation infinite
    hL hC hG graph directed hmu muOrdinal
  have validRows (z : ZFSet.{u}) (member : z ∈ RowTerms) : IsName c z := by
    obtain ⟨tau, equal, _⟩ := rowData z member
    exact equal ▸ tau.property
  have rowHS (tau : Name c) (member : tau.val ∈ RowTerms) :
      HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) tau := by
    obtain ⟨sigma, equal, symmetric⟩ := rowData tau.val member
    exact (show sigma = tau from Subtype.ext equal) ▸ symmetric
  let lifted := Name.renamedFamily upper inclusion RowTerms validRows
  let renameGraph := Name.renameFamilyGraph upper inclusion RowTerms validRows
  have hLifted : lifted ∈ M.sets := M.renamedFamily_mem c upper pairing unions powers separation
    collection carrier hQ inclusion inclusionGround RowTerms hRowTerms validRows
  have hRenameGraph : renameGraph ∈ M.sets := M.renameFamilyGraph_mem c upper pairing unions powers separation
    collection carrier hQ inclusion inclusionGround RowTerms hRowTerms validRows
  have validUpper (z : ZFSet.{u}) (member : z ∈ lifted) : IsName upper z := by
    obtain ⟨tau, _, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows z).1 member
    exact equal.symm ▸ (Name.rename upper inclusion tau).property
  have liftedHS (tau : Name upper) (member : tau.val ∈ lifted) :
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) tau := by
    obtain ⟨sigma, inRows, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows tau.val).1 member
    have same : tau = Name.rename upper inclusion sigma := Subtype.ext equal
    exact same.symm ▸ HereditarilySymmetric.rename upperAct upper inclusion equivariant (rowHS sigma inRows)
  have liftedClosed (g : G) (tau : Name upper) (member : tau.val ∈ lifted) :
      (upperAct.act upper g tau).val ∈ lifted := by
    obtain ⟨sigma, inRows, equal⟩ := (Name.mem_renamedFamily upper inclusion RowTerms validRows tau.val).1 member
    have same : tau = Name.rename upper inclusion sigma := Subtype.ext equal
    have moved := M.binaryRowTupleTerms_action a s b C pairing unions powers separation infinite
      hL hC hG graph hmu muOrdinal g sigma inRows
    apply (Name.mem_renamedFamily upper inclusion RowTerms validRows _).2
    refine ⟨act.act c g sigma, moved, ?_⟩
    rw [same, act.act_rename_of_equivariant upperAct c upper inclusion equivariant]
  let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) lifted validUpper
  have topGround := M.transitive hQ (upper.encode_mem (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)))
  have rowNameGround : rowName.val ∈ M.sets := M.familySet_mem upper ⊤ pairing unions powers separation hLifted topGround validUpper
  have rowNameFixed := Name.act_familySet upperAct lifted validUpper liftedClosed
  have rowNameHS := Name.familySet_hs upperAct (a.principalSupportFamily ⊥ directed) lifted validUpper liftedClosed liftedHS
  have supportPackage := M.exists_groundSupportTupleFamily upperAct upper b s a C directed pairing unions powers separation
    collection infinite choice hQ hG hL order hC supports maps mu hmu muOrdinal small W hW validW symmetricW
  dsimp only at supportPackage
  let supportChoice := Classical.choose supportPackage
  have supportRest := Classical.choose_spec supportPackage
  let positionChoice := Classical.choose supportRest.2
  have positionRest := Classical.choose_spec supportRest.2
  let tupleChoice := Classical.choose positionRest.2
  have tupleRest := Classical.choose_spec positionRest.2
  have hTupleChoice := tupleRest.1
  have tupleChoiceFunction := tupleRest.2.2.2.1
  have chosenData := tupleRest.2.2.2.2
  let liftedChoice := relationCompose W RowTerms lifted tupleChoice renameGraph
  have liftedChoiceGround : liftedChoice ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hW hRowTerms hLifted hTupleChoice hRenameGraph
  have liftedChoiceFunction : ZFSet.IsFunc W lifted liftedChoice := relationCompose_function_of_subset
    tupleChoiceFunction (Name.renameFamilyGraph_function upper inclusion RowTerms validRows) (fun _ h => h)
  have orbitPackage := M.exists_groundSelectedOrbitNameFamily upperAct upper b pairing unions powers separation
    collection hQ hG maps (upper.encode ⊤) W lifted liftedChoice topGround hW hLifted
    liftedChoiceGround liftedChoiceFunction
  let family := Classical.choose orbitPackage
  have orbitRest := Classical.choose_spec orbitPackage
  have hFamily := orbitRest.1
  have function := orbitRest.2.1
  have familyValues := orbitRest.2.2
  have each (i : W.toSet) : ∃ tuple : Name upper, tuple.val ∈ lifted ∧
      function.value i = (Name.orbitPairGraph upperAct upper tuple ⟨i.val, validW i.val i.property⟩).val ∧
      ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
        H.GenericFor (formulaFamily (M.nameDomain upper)) →
        ZFSet.IsFunc (ZFSet.range (fun g : G => Name.eval {p | H.mem p} (upperAct.act upper g tuple)))
          (ZFSet.range (fun g : G => Name.eval {p | H.mem p}
            (upperAct.act upper g ⟨i.val, validW i.val i.property⟩)))
          (Name.eval {p | H.mem p} (Name.orbitPairGraph upperAct upper tuple ⟨i.val, validW i.val i.property⟩)) := by
    let tau : Name upper := ⟨i.val, validW i.val i.property⟩
    obtain ⟨z, chosen, _⟩ := tupleChoiceFunction.2 i.val i.property
    have inRows := (ZFSet.pair_mem_prod.1 (tupleChoiceFunction.1 chosen)).2
    obtain ⟨D, f, _, _, _, supported, delta, hDelta, _, _, fn, positions, values, bounded, covers, exactCode⟩ :=
      chosenData tau z chosen
    let source := M.internalRowTupleName s C hL delta positions
    let tuple := Name.rename upper inclusion source
    have sourceIn : source.val ∈ RowTerms := exactCode ▸ inRows
    have tupleIn : tuple.val ∈ lifted := (Name.mem_renamedFamily upper inclusion RowTerms validRows _).2
      ⟨source, sourceIn, rfl⟩
    have renamed := (Name.pair_mem_renameFamilyGraph upper inclusion RowTerms validRows source tuple.val).2
      ⟨sourceIn, rfl⟩
    have liftedEntry : ZFSet.pair tau.val tuple.val ∈ liftedChoice :=
      (pair_mem_relationCompose _ _ _ _ _ _ _).2 ⟨i.property, tupleIn, source.val, sourceIn, exactCode ▸ chosen, renamed⟩
    have jointGround : (Name.orderedPair (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed)) tuple tau).val ∈ M.sets := by
      rw [Name.orderedPair_code]
      exact M.orderedPairNameCode_mem pairing topGround (M.transitive hLifted tupleIn) (M.transitive hW i.property)
    have code := M.orbitPairGraph_code_eq upperAct upper tuple tau jointGround
    rw [Name.orderedPair_code] at code
    have entry := (familyValues tau.val tuple.val liftedEntry _).2 code
    refine ⟨tuple, tupleIn, function.value_eq_of_entry i entry, ?_⟩
    intro H ordinary
    exact M.liftedRowOrbit_function a s b C pairing unions powers separation infinite hL hC hG graph
      choice uncountable delta positions D covers upper upperAct hQ
      (M.refinementHistoryRowRestriction c T stages packed) inclusion projection restrictionGround equivariant H ordinary tau supported
  let selectedTuple (i : W.toSet) := Classical.choose (each i)
  have selectedData (i : W.toSet) := Classical.choose_spec (each i)
  have names (i : W.toSet) : IsName upper (function.value i) :=
    (selectedData i).2.1.symm ▸ (Name.orbitPairGraph upperAct upper (selectedTuple i)
      ⟨i.val, validW i.val i.property⟩).property
  have actual (i : W.toSet) : (⟨function.value i, names i⟩ : Name upper) =
      Name.orbitPairGraph upperAct upper (selectedTuple i) ⟨i.val, validW i.val i.property⟩ :=
    Subtype.ext (selectedData i).2.1
  have fixed (g : G) (i : W.toSet) : upperAct.act upper g ⟨function.value i, names i⟩ = ⟨function.value i, names i⟩ := by
    rw [actual i]
    exact Name.act_orbitPairGraph upperAct upper _ _ g
  have children (i : W.toSet) : HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed)
      ⟨function.value i, names i⟩ := by
    rw [actual i]
    exact Name.orbitPairGraph_hs upperAct upper (a.principalSupportFamily ⊥ directed) _ _
      (liftedHS (selectedTuple i) (selectedData i).1) (symmetricW _ i.property)
  refine ⟨validRows, ?_⟩
  refine ⟨validUpper, ?_⟩
  dsimp only
  refine ⟨rowNameGround, rowNameFixed, rowNameHS,
    family, hFamily, function, names, fixed, children, ?_⟩
  intro H ordinary
  have package := M.supportedNameSequence_function_mem upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection hQ hW hFamily function names ⊤
    (a.principalSupportFamily ⊥ directed).top (fun g _ i => fixed g i) children H
  refine ⟨rowNameGround, package.1, package.2.2.1,
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H _).2
      ⟨rowName, rowNameGround, rowNameHS, rfl⟩, package.2.2.2.2, package.2.2.2.1, ?_⟩
  intro i
  let orbit := Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper)
  have fn := (selectedData i).2.2 H ordinary
  have within (g : G) : Name.eval {p | H.mem p} (upperAct.act upper g (selectedTuple i)) ∈
      Name.eval {p | H.mem p} rowName :=
    (Name.mem_eval_familySet {p | H.mem p} ⊤ H.top_mem lifted validUpper _).2
      ⟨upperAct.act upper g (selectedTuple i), liftedClosed g _ (selectedData i).1, rfl⟩
  have orbitEq : orbit = Name.eval {p | H.mem p} (Name.orbitPairGraph upperAct upper
      (selectedTuple i) ⟨i.val, validW i.val i.property⟩) := congrArg (Name.eval {p | H.mem p}) (actual i)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    have original := hz
    change z ∈ orbit at hz
    rw [orbitEq] at hz
    obtain ⟨g, rfl⟩ := (Name.mem_eval_orbitPairGraph upperAct upper _ _ {p | H.mem p} H.top_mem z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨within g, pair_second_mem_doubleUnion original⟩
  · intro x y z first second
    change ZFSet.pair x y ∈ orbit at first
    change ZFSet.pair x z ∈ orbit at second
    have functionOn : FunctionGraphOn _ _ := ⟨_, fn⟩
    exact functionOn.unique (orbitEq ▸ first) (orbitEq ▸ second)
  · refine ⟨Name.eval {p | H.mem p} (selectedTuple i), ?_, ?_⟩
    · simpa only [upperAct.act_one] using within (1 : G)
    · change ZFSet.pair (Name.eval {p | H.mem p} (selectedTuple i))
        (Name.eval {p | H.mem p} ⟨i.val, validW i.val i.property⟩) ∈ orbit
      rw [orbitEq]
      apply (Name.mem_eval_orbitPairGraph upperAct upper _ _ {p | H.mem p} H.top_mem _).2
      exact ⟨1, congrArg₂ ZFSet.pair
        (congrArg (Name.eval {p | H.mem p}) (upperAct.act_one upper (selectedTuple i)))
        (congrArg (Name.eval {p | H.mem p}) (upperAct.act_one upper ⟨i.val, validW i.val i.property⟩))⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
include order nodeMaps supports choice

theorem semanticBinaryRow_ordinal_partial_cover
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega)
    (mu : ZFSet.{u}) (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu)
    (small : M.groundEmbeddable s.nonbottom.carrier mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    ∀ (T T2 : ZFSet.{u}) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets)
      (valid1 : ∀ z ∈ T, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ T2, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (act.act c.pairEmpty g tau).val ∈ T)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (act.act c.pairEmpty g tau).val ∈ T2)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (ordinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) T T2 level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) T T2 stages history
    let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder (c.encode ⊤)
      (act.actionGraph c b) b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) T T2 ordinal trace
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
      run.carriers ordinal carrier (c.encode ⊤) topMem topRows
    let upper := SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages packed)
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed T T2 (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 children1 children2 topMem topRows hs hh ordinal trace
    let inclusion := M.refinementHistoryRowEmbedding c T stages packed run ordinal carrier
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let RowTerms := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∃ validRows : ∀ z ∈ RowTerms, IsName c z,
    ∃ validUpper : ∀ z ∈ Name.renamedFamily upper inclusion RowTerms validRows, IsName upper z,
    let rowName := Name.familySet (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
      (Name.renamedFamily upper inclusion RowTerms validRows) validUpper
    ∀ (H : ConditionFilter (SetMembers (M.refinementHistoryForcing c.carrier T stages packed))),
      H.GenericFor (formulaFamily (M.nameDomain upper)) →
      let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
      let Trow := Name.eval {p | H.mem p} rowName
      Trow ∈ N.sets ∧
      ∀ X ∈ N.sets, ∃ delta ∈ N.sets, ordinalSetProperty delta ∧
        ∃ h ∈ N.sets, FunctionGraphOn delta h ∧
          (∀ i hi, ZFSet.pair i hi ∈ h → PartialFunctionCode Trow (⋃₀ ⋃₀ hi) hi) ∧
          ∀ x ∈ X, ∃ i ∈ delta, ∃ hi, ZFSet.pair i hi ∈ h ∧
            ∃ u ∈ Trow, ZFSet.pair u x ∈ hi := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega ⟨s.carrier, hL⟩
  intro act c T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
    coordinates two carrier forcingOrder forcingAction omega topMem topRows packed run
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T stages packed
    run.carriers ordinal carrier (c.encode ⊤) topMem topRows
  intro upper upperAct inclusion rows S RowTerms
  have hPacked := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![b.carrier, s.carrier, s.conditionOrder, supportBasisCode s b a.principalFix, T, T2, stages, history]
    (Fin.cases hG (Fin.cases hL (Fin.cases order (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : upper.carrier ∈ M.sets := M.refinementHistoryForcing_mem pairing unions powers separation
    carrier hT hs hPacked omega
  have cover := M.semanticBinaryRow_orbit_cover a s b C pairing unions powers separation collection
    infinite choice hL order hC hG graph nodeMaps supports directed uncountable mu hmu muOrdinal small
    T T2 hT hT2 valid1 valid2 closed1 closed2 children1 children2 stages history hs hh ordinal trace
  dsimp only at cover
  have emptyGround := M.empty_mem ⟨mu, hmu⟩
  have base := cover ∅ emptyGround (fun z hz => False.elim (ZFSet.notMem_empty z hz))
    (fun tau member => False.elim (ZFSet.notMem_empty tau.val member))
  let validRows := Classical.choose base
  have baseRows := Classical.choose_spec base
  let validUpper := Classical.choose baseRows
  have baseData := Classical.choose_spec baseRows
  refine ⟨validRows, ?_⟩
  refine ⟨validUpper, ?_⟩
  dsimp only
  intro H ordinary
  let N := M.symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H
  let Trow := Name.eval {p | H.mem p} (Name.familySet
    (⊤ : SetMembers (M.refinementHistoryForcing c.carrier T stages packed))
    (Name.renamedFamily upper inclusion RowTerms validRows) validUpper)
  have groundSubset := M.ground_subset_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection hQ H
  refine ⟨(M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H _).2
    ⟨_, baseData.1, baseData.2.2.1, rfl⟩, ?_⟩
  intro X hX
  obtain ⟨tau, tauGround, tauHS, tauValue⟩ :=
    (M.mem_symmetricExtension upper upperAct (a.principalSupportFamily ⊥ directed) H X).1 hX
  have singletonGround : ({tau.val} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing tauGround tauGround
  have singletonValid (z : ZFSet.{u}) (hz : z ∈ ({tau.val} : ZFSet.{u})) : IsName upper z :=
    (ZFSet.mem_singleton.1 hz).symm ▸ tau.property
  have singletonHS (sigma : Name upper) (member : sigma.val ∈ ({tau.val} : ZFSet.{u})) :
      HereditarilySymmetric upperAct upper (a.principalSupportFamily ⊥ directed) sigma :=
    (show sigma = tau from Subtype.ext (ZFSet.mem_singleton.1 member)).symm ▸ tauHS
  let W := Name.childFamilyCodes upper {tau.val}
  have hW : W ∈ M.sets := M.childFamilyCodes_mem upper pairing unions powers separation hQ _ singletonGround
  have validW := Name.childFamilyCodes_valid upper {tau.val} singletonValid
  have symmetricW := Name.childFamilyCodes_hs upper upperAct (a.principalSupportFamily ⊥ directed)
    {tau.val} singletonValid singletonHS
  have selected := cover W hW validW symmetricW
  have selectedRows := Classical.choose_spec selected
  have selectedData := Classical.choose_spec selectedRows
  let family := Classical.choose selectedData.2.2.2
  have familyData := Classical.choose_spec selectedData.2.2.2
  let function := Classical.choose familyData.2
  have functionData := Classical.choose_spec familyData.2
  let names := Classical.choose functionData
  have nameData := Classical.choose_spec functionData
  have original := nameData.2.2 H ordinary
  refine M.exists_ordinalPartialMapCover upper upperAct (a.principalSupportFamily ⊥ directed)
    pairing unions powers separation collection choice hQ hW familyData.1
    function names nameData.1 nameData.2.1 H Trow X
    (fun i => (original.2.2.2.2.2.2 i).1) ?_
  intro x member
  have originalMember : x ∈ Name.eval {p | H.mem p} tau :=
    Eq.mpr (congrArg (fun A => x ∈ A) tauValue) member
  have childWitness : ∃ sigma : Name upper, sigma.val ∈ W ∧
      Name.eval {p | H.mem p} sigma = x :=
    Name.eval_member_childFamilyCodes upper {tau.val} singletonValid
      {p | H.mem p} tau (ZFSet.mem_singleton.2 rfl) x originalMember
  let sigma := Classical.choose childWitness
  have sigmaData := Classical.choose_spec childWitness
  let i : W.toSet := ⟨sigma.val, sigmaData.1⟩
  have rangeWitness : ∃ u ∈ Trow, ZFSet.pair u (Name.eval {p | H.mem p} sigma) ∈
      Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper) :=
    (original.2.2.2.2.2.2 i).2
  let u := Classical.choose rangeWitness
  have uData := Classical.choose_spec rangeWitness
  refine ⟨i, u, uData.1, ?_⟩
  exact Eq.mp (congrArg (fun v => ZFSet.pair u v ∈
    Name.eval {p | H.mem p} (⟨function.value i, names i⟩ : Name upper)) sigmaData.2) uData.2

end PartitionPilot.Forcing.TransitiveGround

end OAI
