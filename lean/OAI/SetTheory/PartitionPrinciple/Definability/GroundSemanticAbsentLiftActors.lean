import OAI.SetTheory.PartitionPrinciple.Forcing.GroundAbsentLiftClassTransport

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

variable {stages history alpha : ZFSet.{u}} (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
variable (ordinal : ordinalSetProperty stages)
variable (trace : OrdinalRecursionTrace (fun level prior stage => stage =
  M.structuralForcingStage c.carrier c.conditionOrder rowTop (a.actionGraph c t)
    t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 level prior) stages history)
variable (member : alpha ∈ stages)
local notation "hAlpha" => M.transitive hs member
local notation "cutOrdinal" => ordinalSetProperty_member ordinal member
local notation "subset" => (And.left ordinal) alpha member
local notation "packed" => M.structuralRefinementHistory t.carrier b.carrier b.conditionOrder
  (supportBasisCode b t d.principalFix) T T2 stages history
local notation "lowerPacked" => graphRestriction alpha packed
local notation "Q" => M.refinementHistoryForcing c.carrier T alpha lowerPacked
include hs hh ordinal trace member

local notation "run" => M.structuralForcingTrace_recursiveOrder c.carrier c.conditionOrder rowTop
  (a.actionGraph c t) t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
  (supportBasisCode b t d.principalFix) T T2 ordinal trace
local notation "act" => M.semanticStructuralPrefixAction c a t b d base directed T T2 rowTop
  pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
  nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
  topMem topRows hh trace hAlpha cutOrdinal subset

local notation "next" => graphRestriction (insert alpha alpha) packed
local notation "upper" => M.refinementHistoryForcing c.carrier T (insert alpha alpha) next
local notation "levels" => refinementDataHistoryLevels (insert alpha alpha) next T
local notation "packedGround" => M.structuralRefinementHistory_mem pairing unions powers separation collection
  ![t.carrier, b.carrier, b.conditionOrder, supportBasisCode b t d.principalFix, T, T2, stages, history]
  (Fin.cases group (Fin.cases nodes (Fin.cases nodeOrder (Fin.cases supports
    (Fin.cases hT (Fin.cases hT2 (Fin.cases hs (Fin.cases hh (fun j => Fin.elim0 j)))))))))
local notation "lowerGround" => M.refinementHistoryForcing_mem pairing unions powers separation
  carrier hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega
local notation "orderGround" => M.refinementHistoryOrder_mem pairing unions powers separation
  carrier rowOrderGround hT hAlpha (M.graphRestriction_mem unions separation hAlpha packedGround) omega

theorem semanticStructuralSuccessor_represented_absentLift_actor
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable)
    {row A : ZFSet.{u}} (condition : ZFSet.pair row A ∈ upper) :
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
    letI := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
      ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
    let lower := SetMembers.presentation Q
    let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
      cutOrdinal carrier T valid1
    let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
      pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
      nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
      topMem topRows hs hh ordinal trace member
    let lowerOrder : lower.conditionOrder ∈ M.sets := by
      rw [M.refinementHistoryDecodedOrder_eq]
      exact orderGround
    let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
    let vis := M.stageOneVisibilityName lower valid act b d base directed system.first

    ∀ (meet : L → L → L),
      (∀ (H : ConditionFilter (SetMembers Q)), H.GenericFor (M.codedFamily lower) →
        H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v z : L) (x y : (M.nameDomain lower).names),
          d.principalFix v ≤ (act).stabilizer lower x.val →
          d.principalFix z ≤ (act).stabilizer lower y.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) x.val →
          HereditarilySymmetric act lower (d.principalSupportFamily base directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric act lower (d.principalSupportFamily base directed) tau.val ∧
            d.principalFix (meet v z) ≤ (act).stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∀ (C E D K : L) (U Rf Rc u : (M.nameDomain lower).names) (F : ZFSet.{u}),
      let idx := refinementIndexCode alpha (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
      idx ∈ M.niceRefinementIndices act lower b d alpha T T2 valid →
      u.val.val ∈ T → C ≤ D →
      d.principalFix D ≤ (act).stabilizer lower u.val →
      ∀ g : G, g ∈ d.principalFix C → d.iso g D ≤ K →
      ∀ pCut r q : SetMembers Q,
      lower.encode pCut = ZFSet.pair row (assignmentCut levels alpha A) → r ≤ pCut → q ≤ r → q ≤ (act).iso g r →
      Name.ForcesMem r u.val U.val →
      (∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v) →
      (∀ v : L, E ≤ v → b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) →
      M.DecidesVisibilityProfile act lower b d.principalFix T F (cls Rc u).val r →
      (∀ p, p ≤ r → ¬ Name.ForcesMem p (cls Rf u).val (vis C).val) →
      (∀ v z : (M.nameDomain lower).names, v.val.val ∈ T → z.val.val ∈ T →
        stageOneAssignment idx v.val.val z.val.val ∈ A →
        (∀ p, p ≤ r → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc v).val) ∧
        ∃ profile, M.DecidesVisibilityProfile act lower b d.principalFix T profile (cls Rf z).val r ∧
          (b.encode C ∉ profile → b.encode K ∉ profile)) →
      ∃ w : (M.nameDomain lower).names, w.val = (act).act lower g u.val ∧
      w.val.val ∈ T ∧ Name.ForcesMem q w.val U.val ∧
      M.representedDomainConditions lower upper levels alpha T valid idx U Rc u ∈ M.sets ∧
      ∃ lowerRow lowerA : ZFSet.{u}, lower.encode q = ZFSet.pair lowerRow lowerA ∧
        let spliced := assignmentSplice levels alpha lowerA A
        let inserted := insert (stageOneAssignment idx u.val.val w.val.val) spliced
        ZFSet.pair lowerRow inserted ∈ upper ∧
        ZFSet.pair (ZFSet.pair lowerRow inserted) (ZFSet.pair row A) ∈
          M.refinementHistoryOrder c.carrier c.conditionOrder T (insert alpha alpha) next ∧
        A ⊆ inserted ∧ stageOneAssignment idx u.val.val w.val.val ∈ inserted ∧
        ZFSet.pair lowerRow (assignmentCut levels alpha inserted) = lower.encode q ∧
        Name.ForcesEq q (cls Rc u).val (cls Rc u).val ∧
        ZFSet.pair lowerRow inserted ∈ M.representedDomainConditions lower upper levels alpha T valid
           idx U Rc u := by
  let := M.refinementHistoryPartialOrder c.conditionOrder_code T alpha lowerPacked
  let := M.refinementHistoryOrderTop c.conditionOrder_code T alpha lowerPacked
    ((run).carriers.restrict cutOrdinal subset) cutOrdinal carrier rowTop topMem topRows
  let lower := SetMembers.presentation Q
  let valid := M.refinementHistoryRowNameFamily_valid c ((run).carriers.restrict cutOrdinal subset)
    cutOrdinal carrier T valid1
  let system := M.semanticStructuralPrefix_refinementSystem c a t b d base directed T T2 rowTop
    pairing unions powers separation collection carrier rowOrderGround rowAction group nodes nodeOrder
    nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2 symmetric1 symmetric2
    topMem topRows hs hh ordinal trace member
  have lowerOrder : lower.conditionOrder ∈ M.sets := by
    rw [M.refinementHistoryDecodedOrder_eq]
    exact orderGround
  let cls := M.stageOneClassName lower pairing unions powers separation collection lowerGround lowerOrder hT valid
  let vis := M.stageOneVisibilityName lower valid act b d base directed system.first
  dsimp only
  intro meet descent C E D K U Rf Rc u F idx hu above supportU g fixed cap
    pCut r q cutCode rp qr qgr activeU capPositive capNegative decisions absent oldProfiles
  let w : (M.nameDomain lower).names := ⟨(act).act lower g u.val,
    M.act_mem lower act t pairing unions powers separation collection lowerGround
      system.inputs.condition_maps g u.val u.property⟩
  obtain ⟨hw, activeW, _literalClass, _capSupport, capVisible, nonvisible⟩ :=
    M.refinementAbsentLift_class_transport lower pairing unions powers separation collection
      lowerGround lowerOrder hT valid act t system.inputs.condition_maps b d base directed
      system.inputs.terms_closed system.first alpha system.indices small C E D K U Rf Rc u idx hu
      above supportU g fixed cap r q qgr activeU absent
  have profileMono (profile : ZFSet.{u}) (z : Name lower)
      (selected : M.DecidesVisibilityProfile act lower b d.principalFix T profile z r) :
      M.DecidesVisibilityProfile act lower b d.principalFix T profile z q := by
    intro v
    exact ⟨fun yes => Name.forcesMem_mono ((selected v).1 yes) qr,
      fun no p pq => (selected v).2 no p (pq.trans qr)⟩
  have atQ := M.semanticStructuralSuccessor_represented_absentLift c a t b d base directed
    T T2 rowTop pairing unions powers separation collection carrier rowOrderGround rowAction group
    nodes nodeOrder nodeAction nodeMaps supports hT hT2 omega valid1 valid2 closed1 closed2
    symmetric1 symmetric2 topMem topRows hs hh ordinal trace member infinite choice small condition
    meet descent C E K U Rf Rc u w F idx hu hw pCut q cutCode (qr.trans rp)
    (Name.forcesMem_mono activeU qr) activeW capPositive capNegative
    (profileMono F (cls Rc u).val decisions) capVisible nonvisible
    (by
      intro v z hv hz old
      obtain ⟨different, profile, selected, survivor⟩ := oldProfiles v z hv hz old
      exact ⟨fun p pq => different p (pq.trans qr), profile,
        profileMono profile (cls Rf z).val selected, survivor⟩)
  exact ⟨w, rfl, hw, activeW, atQ⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
