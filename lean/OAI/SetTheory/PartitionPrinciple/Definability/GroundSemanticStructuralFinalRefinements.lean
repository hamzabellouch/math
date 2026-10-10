import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralRefinementNormalization
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOrdinaryMembershipAntichainFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRepresentativeAntichainBounds
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAssignmentRepresentativeClosure

namespace OAI


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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_antichains_below
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    ∀ D ∈ M.sets,
      OrderAntichainCode (M.refinementHistoryForcing c.carrier T K packed)
        (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) D → GroundBelow M D K := by
  dsimp only
  intro D hD antichain
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let I := refinementDataHistoryIndices K packed
  let Q := M.refinementHistoryForcing c.carrier T K packed
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hI : I ∈ M.sets := M.refinementDataHistoryIndices_mem pairing unions powers separation hK hPacked
  have shape : Q ⊆ M.stageOneCandidateBound c.carrier I T :=
    fun _ member => ((M.mem_refinementHistoryForcing c.carrier T K packed _).1 member).1
  obtain ⟨X, hX, _, smallX, representatives⟩ := M.exists_assignmentRepresentativeClosure
    pairing unions powers separation collection infinite choice carrier hI hT hD hK conditions
    smallRows smallT (fun _ member => shape (antichain.1 member))
  apply M.representative_antichain_below pairing unions powers separation carrier hX hT hK hD omega
    conditions.1 conditions.2.2.2 smallRows smallX smallT shape antichain ?_ representatives
  intro row A C first second agreement
  obtain ⟨member, belowFirst, belowSecond⟩ := M.semanticStructuralTrace_binary_union_extension
    c a t b d base directed T T2 rowTop pairing unions powers separation collection
    carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega
    valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh conditions.1 trace
    infinite choice row A C first second agreement
  exact ⟨ZFSet.pair row (A ∪ C), member, belowFirst, belowSecond⟩

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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_predense_prefix
    {stages history : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (ordinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
    (alpha : ZFSet.{u}) (hAlpha : alpha ∈ M.sets)
    (cutOrdinal : ordinalSetProperty alpha) (subset : alpha ⊆ stages)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 stages history
    let U := M.refinementHistoryForcing c.carrier T stages packed
    let L := M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
    ∀ A : ZFSet.{u}, A ⊆ L →
      (∀ q ∈ U, ∃ p ∈ A, ∃ r ∈ U,
        ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed ∧
        ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed) →
      ∀ q ∈ L, ∃ p ∈ A, ∃ r ∈ L,
        ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha
          (graphRestriction alpha packed) ∧
        ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T alpha
          (graphRestriction alpha packed) := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 stages history
  let U := M.refinementHistoryForcing c.carrier T stages packed
  let L := M.refinementHistoryForcing c.carrier T alpha (graphRestriction alpha packed)
  let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix)
    T T2 ordinal trace
  let witnesses := M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace
  let mono := M.structuralHistory_rawTests_mono t b d base directed T T2 stages history
    pairing unions powers separation collection group nodes supports hh hT witnesses
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem
    pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace alpha hAlpha cutOrdinal subset infinite choice
  have unchanged : ∀ q : SetMembers L,
      (SetMembers.presentation U).encode
        (run.inclusion ordinal cutOrdinal subset pairing unions powers separation infinite choice
          hs hPacked hT hAlpha carrier rowTop topMem topRows mono c.conditionOrder_code q) =
        (SetMembers.presentation L).encode q := by
    intro q
    exact run.inclusionFunction_raw ordinal cutOrdinal subset pairing unions powers separation
      infinite choice hs hPacked hT hAlpha carrier rowTop topMem topRows mono q
  dsimp only
  intro A within predense
  have upperOrder : (SetMembers.presentation U).conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T stages packed :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T stages packed
  have lowerOrder : (SetMembers.presentation L).conditionOrder =
      M.refinementHistoryOrder c.carrier c.conditionOrder T alpha (graphRestriction alpha packed) :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T alpha (graphRestriction alpha packed)
  have upper : ∀ q ∈ (SetMembers.presentation U).carrier, ∃ p ∈ A,
      ∃ r ∈ (SetMembers.presentation U).carrier,
        ZFSet.pair r q ∈ (SetMembers.presentation U).conditionOrder ∧
        ZFSet.pair r p ∈ (SetMembers.presentation U).conditionOrder := by
    rw [upperOrder]
    exact predense
  have result := projection.raw_predense_restriction
    (SetMembers.presentation U) (SetMembers.presentation L) unchanged within upper
  rw [lowerOrder] at result
  exact result

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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_membershipAntichains_prefix
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (conditions : GroundInaccessibleConditions M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    let Q := M.refinementHistoryForcing c.carrier T K packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    let s := SetMembers.presentation Q
    ∀ J ∈ M.sets, GroundBelow M J K → (∀ sigma ∈ J, IsName s sigma) →
      ∀ tau : (M.nameDomain s).names,
        ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
          (∀ sigma A, ZFSet.pair sigma A ∈ f →
            RelativeMaximalAntichainCode Q order
              (M.ordinaryMembershipDecisions Q order sigma tau.val.val) A ∧
            ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
              ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) ∧
          let U := (relationImage J (M.groundPower Q) f).sUnion
          (U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q) ∧
          ∃ beta ∈ K,
            (∀ row B, ZFSet.pair row B ∈ U →
              assignmentCut (refinementDataHistoryLevels K packed T) beta B = B ∧
              ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)) ∧
            ∀ sigma A, ZFSet.pair sigma A ∈ f →
              let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
              let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
                (graphRestriction beta packed)
              A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
                ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let Q := M.refinementHistoryForcing c.carrier T K packed
  let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let s := SetMembers.presentation Q
  have hPacked : packed ∈ M.sets := M.structuralRefinementHistory_mem pairing unions powers separation collection
    ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
    (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
      (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
  have hQ : Q ∈ M.sets := M.refinementHistoryForcing_mem
    pairing unions powers separation carrier hT hK hPacked omega
  have orderEq : s.conditionOrder = order :=
    M.refinementHistoryDecodedOrder_eq c.conditionOrder_code T K packed
  have hOrder : s.conditionOrder ∈ M.sets := orderEq.symm ▸
    M.refinementHistoryOrder_mem pairing unions powers separation carrier rowOrderGround hT hK hPacked omega
  have chain := M.semanticStructuralTrace_antichains_below c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions trace infinite choice smallRows smallT
  have typedChain : ∀ A ∈ M.sets, OrderAntichainCode s.carrier s.conditionOrder A → GroundBelow M A K := by
    rw [orderEq]
    exact chain
  dsimp only
  intro J hJ smallJ valid tau
  have family := M.exists_ordinaryMembershipAntichainFamily s pairing unions powers separation
    collection choice hQ hOrder hJ valid tau hK conditions smallJ typedChain
  rw [orderEq] at family
  obtain ⟨f, hf, function, selected, whole⟩ := family
  let U := (relationImage J (M.groundPower Q) f).sUnion
  obtain ⟨beta, hBeta, placed⟩ := M.structuralForcingTrace_small_family_prefix
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection choice carrier group nodes nodeOrder supports hT hT2
    hK hh conditions trace U whole.1 whole.2.1 whole.2.2
  refine ⟨f, hf, function, selected, whole, beta, hBeta, placed, ?_⟩
  intro sigma A entry
  have values := ZFSet.pair_mem_prod.1 (function.1 entry)
  have insideUnion : A ⊆ U := fun q hq => ZFSet.mem_sUnion.2
    ⟨A, (mem_relationImage J (M.groundPower Q) f A).2
      ⟨values.2, sigma, values.1, entry⟩, hq⟩
  have lower : A ⊆ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) := by
    intro q hq
    have inU := insideUnion hq
    have inQ := whole.2.2 inU
    have candidate := ((M.mem_refinementHistoryForcing c.carrier T K packed q).1 inQ).1
    obtain ⟨row, _, B, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound c.carrier
      (refinementDataHistoryIndices K packed) T q).1 candidate
    exact (placed row B inU).2
  refine ⟨lower, ?_⟩
  exact M.semanticStructuralTrace_predense_prefix c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions.1 trace beta (M.transitive hK hBeta)
    (ordinalSetProperty_member conditions.1 hBeta) (conditions.1.1 beta hBeta) infinite choice
    A lower (selected sigma A entry).2

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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

theorem semanticStructuralTrace_finitePowerAntichains_prefix
    {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
    (standard : GroundStandardInaccessible M K)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
        t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 level prior) K history)
    (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K) (n : Nat) :
    let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
      (supportBasisCode b t d.principalFix) T T2 K history
    let Q := M.refinementHistoryForcing c.carrier T K packed
    let order := M.refinementHistoryOrder c.carrier c.conditionOrder T K packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    let s := SetMembers.presentation Q
    let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
    J ∈ M.sets ∧ GroundBelow M J K ∧
      (∀ alpha : ZFSet.{u}, ordinalSetProperty alpha → alpha ⊆ K →
        ∀ z ∈ J, IsName (SetMembers.presentation (M.refinementHistoryForcing
          c.carrier T alpha (graphRestriction alpha packed))) z) ∧
      ∀ tau : (M.nameDomain s).names,
        ∃ f ∈ M.sets, ZFSet.IsFunc J (M.groundPower Q) f ∧
          (∀ sigma A, ZFSet.pair sigma A ∈ f →
            RelativeMaximalAntichainCode Q order
              (M.ordinaryMembershipDecisions Q order sigma tau.val.val) A ∧
            ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
              ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) ∧
          let U := (relationImage J (M.groundPower Q) f).sUnion
          (U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q) ∧
          ∃ beta ∈ K,
            (∀ row B, ZFSet.pair row B ∈ U →
              assignmentCut (refinementDataHistoryLevels K packed T) beta B = B ∧
              ZFSet.pair row B ∈ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)) ∧
            ∀ sigma A, ZFSet.pair sigma A ∈ f →
              let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
              let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
                (graphRestriction beta packed)
              A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
                ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder := by
  let packed := M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 K history
  let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
  let run := M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 standard.1.1 trace
  have terms := M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
    (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
    carrier hT valid1 topMem standard.1.1 trace n
  have oneGround := M.orderedPair_mem pairing (M.transitive carrier topMem)
    (M.empty_mem ⟨c.carrier, carrier⟩)
  have smallJ := M.iteratedPairNameFamily_below pairing unions powers separation infinite
    choice oneGround hT hK standard smallT n
  have upperValid := terms.2 K standard.1.1 (fun _ h => h)
  rw [run.carriers.data.function.restriction_eq] at upperValid
  have family := M.semanticStructuralTrace_membershipAntichains_prefix c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction
    group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh
    (standard.to_conditions pairing unions powers separation hK) trace infinite choice smallRows smallT
    J terms.1 smallJ upperValid
  exact ⟨terms.1, smallJ, terms.2, family⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_commonPowerAntichains :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ count (degrees : Fin count → Nat)
      (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
      ∃ beta, ∃ _ : beta ∈ K, ∃ f : Fin count → ZFSet.{u}, ∀ i,
        let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
        f i ∈ M.sets ∧ ZFSet.IsFunc J (M.groundPower Q) (f i) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          RelativeMaximalAntichainCode Q
            (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
            (M.ordinaryMembershipDecisions Q
              (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
              sigma (tau i).val.val) A ∧
          ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
            ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
            ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
        (∀ sigma A, ZFSet.pair sigma A ∈ f i →
          let lower := M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed)
          let lowerOrder := M.refinementHistoryOrder c.carrier c.conditionOrder T beta
            (graphRestriction beta packed)
          A ⊆ lower ∧ ∀ q ∈ lower, ∃ p ∈ A, ∃ r ∈ lower,
            ZFSet.pair r q ∈ lowerOrder ∧ ZFSet.pair r p ∈ lowerOrder) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro count degrees tau
  let J : Fin count → ZFSet.{u} := fun i =>
    iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  have each : ∀ i : Fin count, ∃ f ∈ M.sets,
      ZFSet.IsFunc (J i) (M.groundPower Q) f ∧
      (∀ sigma A, ZFSet.pair sigma A ∈ f →
        RelativeMaximalAntichainCode Q
          (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
          (M.ordinaryMembershipDecisions Q
            (M.refinementHistoryOrder c.carrier c.conditionOrder T K packed)
            sigma (tau i).val.val) A ∧
        ∀ q ∈ Q, ∃ p ∈ A, ∃ r ∈ Q,
          ZFSet.pair r q ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed ∧
          ZFSet.pair r p ∈ M.refinementHistoryOrder c.carrier c.conditionOrder T K packed) ∧
      let U := (relationImage (J i) (M.groundPower Q) f).sUnion
      U ∈ M.sets ∧ GroundBelow M U K ∧ U ⊆ Q := by
    intro i
    obtain ⟨_, _, _, family⟩ := M.semanticStructuralTrace_finitePowerAntichains_prefix
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT (degrees i)
    obtain ⟨f, hf, function, selected, whole, _⟩ := family (tau i)
    exact ⟨f, hf, function, selected, whole⟩
  choose f hf function selected whole using each
  let U : Fin count → ZFSet.{u} := fun i => (relationImage (J i) (M.groundPower Q) (f i)).sUnion
  let conditions := standard.to_conditions pairing unions powers separation hK
  obtain ⟨D, hD, smallD, members⟩ := conditions.finite_family_union
    pairing unions powers separation infinite choice hK count U
    (fun i => ⟨(whole i).1, (whole i).2.1⟩)
  have inside : D ⊆ Q := by
    intro q hq
    obtain ⟨i, member⟩ := (members q).1 hq
    exact (whole i).2.2 member
  obtain ⟨beta, hBeta, placed⟩ := M.structuralForcingTrace_small_family_prefix
    c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2
    pairing unions powers separation collection choice carrier group nodes nodeOrder supports hT hT2
    hK hh conditions trace D hD smallD inside
  refine ⟨beta, hBeta, f, ?_⟩
  intro i
  refine ⟨hf i, function i, selected i, ?_⟩
  intro sigma A entry
  have values := ZFSet.pair_mem_prod.1 ((function i).1 entry)
  have insideUnion : A ⊆ D := by
    intro q hq
    apply (members q).2
    refine ⟨i, ZFSet.mem_sUnion.2 ?_⟩
    exact ⟨A, (mem_relationImage (J i) (M.groundPower Q) (f i) A).2
      ⟨values.2, sigma, values.1, entry⟩, hq⟩
  have lower : A ⊆ M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed) := by
    intro q hq
    have inD := insideUnion hq
    have inQ := inside inD
    have candidate := ((M.mem_refinementHistoryForcing c.carrier T K packed q).1 inQ).1
    obtain ⟨row, _, B, _, _, _, rfl⟩ := (M.mem_stageOneCandidateBound c.carrier
      (refinementDataHistoryIndices K packed) T q).1 candidate
    exact (placed row B inD).2
  refine ⟨lower, ?_⟩
  exact M.semanticStructuralTrace_predense_prefix c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hK hh conditions.1 trace beta (M.transitive hK hBeta)
    (ordinalSetProperty_member conditions.1 hBeta) (conditions.1.1 beta hBeta) infinite choice
    A lower (selected i sigma A entry).2

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_commonEarlierPowerNames :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ count (degrees : Fin count → Nat)
      (tau : Fin count → (M.nameDomain (SetMembers.presentation Q)).names),
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ i,
      let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := (M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation carrier hT valid1 topMem (And.left (And.left standard)) trace (degrees i)).2 beta cutOrdinal subset
      let N := Name.crossStageMembershipName (SetMembers.presentation Q) lower inc J valid (tau i).val
      N.val ∈ M.sets ∧
      (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
        C ≤ (upperAct).stabilizer (SetMembers.presentation Q) (tau i).val →
        NiceNameCode lowerAct lower J C N.val ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed) N) ∧
      ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (formulaFamily (M.nameDomain (SetMembers.presentation Q))) →
        (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
        Name.eval {p | (projection.projectedFilter H).mem p} N =
          Name.eval {p | H.mem p} (tau i).val ∩
            Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) ∧
        (Name.eval {p | H.mem p} (tau i).val ⊆
          Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) →
          Name.eval {p | (projection.projectedFilter H).mem p} N = Name.eval {p | H.mem p} (tau i).val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro count degrees tau
  obtain ⟨beta, hBeta, f, family⟩ := M.semanticStructuralTrace_commonPowerAntichains
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT count degrees tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  refine ⟨beta, hBeta, ?_⟩
  dsimp only
  intro i
  have evaluation := M.semanticStructuralPrefixMembershipName_eval c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice (degrees i) (tau i) (f i) (family i).2.1
    (fun sigma A entry => ⟨((family i).2.2.1 sigma A entry).1.1, (family i).2.2.2 sigma A entry⟩)
  refine ⟨evaluation.1, ?_, ?_⟩
  · intro C member supported
    obtain ⟨_, _, nice, symmetric⟩ := M.semanticStructuralCrossStagePower_hs
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice (degrees i) C member (tau i).val supported
    exact ⟨nice, symmetric⟩
  · intro H upperGeneric lowerGeneric
    have equal := evaluation.2 H upperGeneric lowerGeneric
    refine ⟨equal, ?_⟩
    intro valueSubset
    rw [equal]
    apply ZFSet.ext
    intro x
    exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
      fun member => ZFSet.mem_inter.2 ⟨member, valueSubset member⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

theorem semanticStructuralTrace_earlierPowerName (n : Nat) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ tau : (M.nameDomain (SetMembers.presentation Q)).names,
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let J := iteratedPairNameFamily (ZFSet.pair rowTop ∅) T n
      let valid := (M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation carrier hT valid1 topMem (And.left (And.left standard)) trace n).2 beta cutOrdinal subset
      let N := Name.crossStageMembershipName (SetMembers.presentation Q) lower inc J valid tau.val
      N.val ∈ M.sets ∧
      (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
        C ≤ (upperAct).stabilizer (SetMembers.presentation Q) tau.val →
        NiceNameCode lowerAct lower J C N.val ∧
        HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed) N) ∧
      ∀ H : ConditionFilter (SetMembers Q),
        H.GenericFor (formulaFamily (M.nameDomain (SetMembers.presentation Q))) →
        (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
        Name.eval {p | (projection.projectedFilter H).mem p} N =
          Name.eval {p | H.mem p} tau.val ∩
            Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) ∧
        (Name.eval {p | H.mem p} tau.val ⊆
          Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ J valid) →
          Name.eval {p | (projection.projectedFilter H).mem p} N = Name.eval {p | H.mem p} tau.val) := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro tau
  obtain ⟨_, _, _, family⟩ := M.semanticStructuralTrace_finitePowerAntichains_prefix
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT n
  obtain ⟨f, _, function, selected, _, beta, hBeta, _, lowerSelected⟩ := family tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have evaluation := M.semanticStructuralPrefixMembershipName_eval c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice n tau f function
    (fun sigma A entry => ⟨(selected sigma A entry).1.1, lowerSelected sigma A entry⟩)
  refine ⟨beta, hBeta, evaluation.1, ?_, ?_⟩
  · intro C member supported
    obtain ⟨_, _, nice, symmetric⟩ := M.semanticStructuralCrossStagePower_hs
      c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice n C member tau.val supported
    exact ⟨nice, symmetric⟩
  · intro H upperGeneric lowerGeneric
    have equal := evaluation.2 H upperGeneric lowerGeneric
    refine ⟨equal, ?_⟩
    intro valueSubset
    rw [equal]
    apply ZFSet.ext
    intro x
    exact ⟨fun member => (ZFSet.mem_inter.1 member).1,
      fun member => ZFSet.mem_inter.2 ⟨member, valueSubset member⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_commonRefinementNames (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ T validT))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  intro tau
  let degrees : Fin 3 → Nat := ![0, 1, 1]
  obtain ⟨beta, hBeta, representations⟩ := M.semanticStructuralTrace_commonEarlierPowerNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT 3 degrees tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let upper := SetMembers.presentation Q
  let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
  let validT := (termData 0).2 beta cutOrdinal subset
  let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
  let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
  let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
    beta hAlpha cutOrdinal subset infinite choice
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, unchanged⟩ :=
    M.semanticStructuralPrefixRefinementNormalization c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset infinite choice
      small degrees tau
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid i
  have topCode : lower.encode ⊤ = ZFSet.pair rowTop ∅ :=
    M.refinementHistoryDecodedTop_eq c.conditionOrder_code T beta (graphRestriction beta packed)
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  have bounds : ∀ j : Fin 3, Name.eval {p | H.mem p} (tau j).val ⊆
      Name.eval {p | (projection.projectedFilter H).mem p} (Name.familySet ⊤ (J j) (valid j)) := by
    exact Name.refinementValidity_familySet_power_bounds
      {p | (projection.projectedFilter H).mem p} ⊤ (projection.projectedFilter H).top_mem
      (ZFSet.pair rowTop ∅) T topCode.symm validT valid
      (fun j => Name.eval {p | H.mem p} (tau j).val) originalValid
  have oldEqual (j : Fin 3) :
      Name.eval {p | (projection.projectedFilter H).mem p} (env j.castSucc).val =
        Name.eval {p | H.mem p} (tau j).val := by
    rw [names j]
    exact ((representations j).2.2 H upperGeneric lowerCoded).2 (bounds j)
  have oldValid : RefinementValidityCode
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 3).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 0).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 1).val)
      (Name.eval {p | (projection.projectedFilter H).mem p} (env 2).val) := by
    have zero := oldEqual 0
    have one := oldEqual 1
    have two := oldEqual 2
    change Name.eval _ (env 0).val = _ at zero
    change Name.eval _ (env 1).val = _ at one
    change Name.eval _ (env 2).val = _ at two
    rw [last, zero, one, two]
    exact originalValid
  exact (unchanged (projection.projectedFilter H) lowerGeneric oldValid i).trans (oldEqual i)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula Compression.RecursiveMaps
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
variable (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T → (a.act c.pairEmpty g tau).val ∈ T)
variable (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ T2 → (a.act c.pairEmpty g tau).val ∈ T2)
variable (symmetric1 : ∀ tau : Name c.pairEmpty, tau.val ∈ T →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (symmetric2 : ∀ tau : Name c.pairEmpty, tau.val ∈ T2 →
  HereditarilySymmetric a c.pairEmpty (d.principalSupportFamily base directed) tau)
variable (topMem : rowTop ∈ c.carrier)
variable (topRows : ∀ row ∈ c.carrier, ZFSet.pair row rowTop ∈ c.conditionOrder)
include pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction
  nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows

variable {K history : ZFSet.{u}} (hK : K ∈ M.sets) (hh : history ∈ M.sets)
variable (standard : GroundStandardInaccessible M K)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level prior) K history)
variable (infinite : Realize M.sets infinity Fin.elim0) (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable (smallRows : GroundBelow M c.carrier K) (smallT : GroundBelow M T K)
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 K history
local notation "Q" => M.refinementHistoryForcing c.carrier T K packed
local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 (And.left (And.left standard)) trace
local notation "upperAct" => M.semanticStructuralAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "witnesses" => M.structuralForcingTrace_witnesses c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
local notation "mono" => M.structuralHistory_rawTests_mono t b d base directed T T2 K history
  pairing unions powers separation collection group nodes supports hh hT witnesses
local notation "hPacked" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, K, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hK (Fin.cases hh (fun j => Fin.elim0 j)))))))))
include hK hh standard trace infinite choice smallRows smallT

local notation "termData" => M.structuralTrace_finitePowerTerms c c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 pairing unions powers separation
  carrier hT valid1 topMem (And.left (And.left standard)) trace

theorem semanticStructuralTrace_finalRefinementNames (small : M.sets.Countable) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
      (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
    let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
      (And.left (And.left standard)) carrier T valid1
    ∀ tau : Fin 3 → (M.nameDomain (SetMembers.presentation Q)).names,
      ∃ beta, ∃ hBeta : beta ∈ K,
      let hAlpha := M.transitive hK hBeta
      let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
      let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
      letI := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
        ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
      let upper := SetMembers.presentation Q
      let lower := SetMembers.presentation (M.refinementHistoryForcing c.carrier T beta (graphRestriction beta packed))
      let inc := RecursiveRefinementOrderHistory.inclusionFunction run (And.left (And.left standard)) cutOrdinal subset
        pairing unions powers separation infinite choice hK hPacked hT hAlpha carrier rowTop topMem topRows mono
      let projection := M.semanticStructuralTrace_completeProjection c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace
        beta hAlpha cutOrdinal subset infinite choice
      let lowerAct := M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2 topMem topRows hh trace hAlpha cutOrdinal subset
      let degrees : Fin 3 → Nat := ![0, 1, 1]
      let J := fun i => iteratedPairNameFamily (ZFSet.pair rowTop ∅) T (degrees i)
      let valid := fun i => (termData (degrees i)).2 beta cutOrdinal subset
      let validT := (termData 0).2 beta cutOrdinal subset
      ∃ env : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (env i.castSucc).val =
          Name.crossStageMembershipName upper lower inc (J i) (valid i) (tau i).val) ∧
        (env 3).val = Name.familySet ⊤ T validT ∧
      ∃ normalized : Assignment (M.nameDomain lower) 4,
        (∀ i : Fin 3, (normalized i.castSucc).val =
          Name.refinementConditionNames (M.nameDomain lower) env J valid i) ∧
        normalized 3 = env 3 ∧
        Forces (M.nameDomain lower) BoundedFormula.refinementValidityFormula.toFormula normalized ⊤ ∧
        (∀ C : Subgroup G, (d.principalSupportFamily base directed).mem C →
          (∀ i, C ≤ (upperAct).stabilizer upper (tau i).val) → ∀ i : Fin 3,
          NiceNameCode lowerAct lower (J i) C (normalized i.castSucc).val.val ∧
          HereditarilySymmetric lowerAct lower (d.principalSupportFamily base directed)
            (normalized i.castSucc).val) ∧
        ∀ H : ConditionFilter (SetMembers Q),
          H.GenericFor (formulaFamily (M.nameDomain upper)) →
          (projection.projectedFilter H).GenericFor (M.codedFamily lower) →
          (projection.projectedFilter H).GenericFor (formulaFamily (M.nameDomain lower)) →
          RefinementValidityCode
            (Name.eval {p | H.mem p} (Name.familySet ⊤ T validUpper))
            (Name.eval {p | H.mem p} (tau 0).val) (Name.eval {p | H.mem p} (tau 1).val)
            (Name.eval {p | H.mem p} (tau 2).val) →
          ∀ i : Fin 3, Name.eval {p | (projection.projectedFilter H).mem p} (normalized i.castSucc).val =
            Name.eval {p | H.mem p} (tau i).val := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T K packed
  let := M.refinementHistoryOrderTop c.conditionOrder_code T K packed
    (run).carriers (And.left (And.left standard)) carrier rowTop topMem topRows
  let validUpper := M.refinementHistoryRowNameFamily_valid c (run).carriers
    (And.left (And.left standard)) carrier T valid1
  dsimp only
  intro tau
  obtain ⟨beta, hBeta, result⟩ := M.semanticStructuralTrace_commonRefinementNames
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh standard trace infinite choice smallRows smallT small tau
  let hAlpha := M.transitive hK hBeta
  let cutOrdinal := ordinalSetProperty_member (And.left (And.left standard)) hBeta
  let subset : beta ⊆ K := (And.left (And.left standard)).1 beta hBeta
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T beta (graphRestriction beta packed)
  let := M.refinementHistoryOrderTop c.conditionOrder_code T beta (graphRestriction beta packed)
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  dsimp only at result
  obtain ⟨env, names, last, normalized, entries, normalizedLast, forced, supported, preserved⟩ := result
  refine ⟨beta, hBeta, env, names, last, normalized, entries, normalizedLast, forced, supported, ?_⟩
  intro H upperGeneric lowerCoded lowerGeneric originalValid
  apply preserved H upperGeneric lowerCoded lowerGeneric
  have sameUniverse := M.semanticStructuralPowerFamily_eval_prefix
    c a t b d base directed T T2 rowTop pairing unions powers separation collection carrier rowOrderGround
    rowAction group nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hK hh (And.left (And.left standard)) trace hAlpha cutOrdinal subset
    infinite choice 0 H
  simp only [iteratedPairNameFamily_zero] at sameUniverse
  rw [← sameUniverse]
  exact originalValid

end PartitionPilot.Forcing.TransitiveGround

end OAI
