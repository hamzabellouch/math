import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageInvariant

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def LinkedMainInvariantCode (M : TransitiveGround.{u})
    (K Labels C D P G cutoff serial : ZFSet.{u}) : Prop :=
  GroundBelow M P K ∧ GroundBelow M G K ∧ GroundBelow M Labels K ∧
    ZFSet.rank P < ZFSet.rank K ∧ ZFSet.rank G < ZFSet.rank K ∧
    ZFSet.rank Labels < ZFSet.rank K ∧ cutoff ∈ K ∧
    ZFSet.rank C < ZFSet.rank K ∧ ZFSet.rank D < ZFSet.rank K ∧
    ZFSet.rank serial < ZFSet.rank K

namespace SetFormula

def linkedMainInvariantFormula {n} (K Labels C D P G cutoff serial : Fin n) : SetFormula n :=
  .conj (groundBelowFormula P K) (.conj (groundBelowFormula G K)
    (.conj (groundBelowFormula Labels K) (.conj (cumulativeRankLtFormula P K)
      (.conj (cumulativeRankLtFormula G K) (.conj (cumulativeRankLtFormula Labels K)
        (.conj (.mem cutoff K) (.conj (cumulativeRankLtFormula C K)
          (.conj (cumulativeRankLtFormula D K) (cumulativeRankLtFormula serial K)))))))))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_linkedMainInvariantFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) {n}
    (K Labels C D P G cutoff serial : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainInvariantFormula K Labels C D P G cutoff serial) env ↔
      LinkedMainInvariantCode M (env K) (env Labels) (env C) (env D)
        (env P) (env G) (env cutoff) (env serial) := by
  change (Realize M.sets (groundBelowFormula P K) env ∧
    Realize M.sets (groundBelowFormula G K) env ∧
    Realize M.sets (groundBelowFormula Labels K) env ∧
    Realize M.sets (cumulativeRankLtFormula P K) env ∧
    Realize M.sets (cumulativeRankLtFormula G K) env ∧
    Realize M.sets (cumulativeRankLtFormula Labels K) env ∧ env cutoff ∈ env K ∧
    Realize M.sets (cumulativeRankLtFormula C K) env ∧
    Realize M.sets (cumulativeRankLtFormula D K) env ∧
    Realize M.sets (cumulativeRankLtFormula serial K) env) ↔ _
  rw [M.realize_groundBelowFormula P K env members,
    M.realize_groundBelowFormula G K env members,
    M.realize_groundBelowFormula Labels K env members,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection P K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection G K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection Labels K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection C K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection D K env members ordinal,
    M.realize_cumulativeRankLtFormula pairing unions powers separation collection serial K env members ordinal]
  rfl

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
