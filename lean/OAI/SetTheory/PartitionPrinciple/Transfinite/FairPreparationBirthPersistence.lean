import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFairPreparationMonotonicity

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

theorem fairPreparation_birthPersistence
    {Q E0 stages U enumSelector prepSelector gridGraph : ZFSet.{u}}
    (function : ZFSet.IsFunc Q E0 enumSelector)
    (clocks conditions births events enumerations : Nat → ZFSet.{u})
    (chosen : ∀ k, ZFSet.pair (conditions k) (enumerations k) ∈ enumSelector)
    (initialClock : clocks 0 = ∅)
    (initialBirths : births 0 = {ZFSet.pair ∅ (enumerations 0)})
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector gridGraph
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1)))))) :
    ∀ k, clocks k = natSetCode k ∧ births k = finiteStageHistory enumerations (k + 1) ∧
      (∀ i y, ZFSet.pair (natSetCode i) y ∈ births k ↔ i ≤ k ∧ y = enumerations i) ∧
      ∀ y, ZFSet.pair (natSetCode (Nat.unpair k).1) y ∈ births k ↔
        y = enumerations (Nat.unpair k).1 := by
  have successor (k : Nat) : clocks (k + 1) = insert (clocks k) (clocks k) ∧
      births (k + 1) = insert (ZFSet.pair (clocks (k + 1)) (enumerations (k + 1))) (births k) := by
    obtain ⟨n, p, b, last, m, q, nextBirths, event, source, target, next,
      i, _hi, j, _hj, e, _he, newE, _hNew, _grid, _old, selected, append, _branch⟩ := steps k
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
    obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
    obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
    have hp := (ZFSet.pair_mem_prod.1 (function.1 (chosen (k + 1)))).1
    obtain ⟨_, _, unique⟩ := function.2 _ hp
    have same := (unique newE selected).trans (unique _ (chosen (k + 1))).symm
    exact ⟨next, same ▸ append⟩
  have exactHistory : ∀ k, clocks k = natSetCode k ∧ births k = finiteStageHistory enumerations (k + 1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨initialClock, ?_⟩
      exact initialBirths
    | succ k ih =>
      have next := successor k
      have clock : clocks (k + 1) = natSetCode (k + 1) := by
        rw [next.1, ih.1, natSetCode_succ]
      exact ⟨clock, by rw [next.2, clock, ih.2]; rfl⟩
  intro k
  have facts := exactHistory k
  have lookup (i : Nat) (y : ZFSet.{u}) :
      ZFSet.pair (natSetCode i) y ∈ births k ↔ i ≤ k ∧ y = enumerations i := by
    rw [facts.2, pair_mem_finiteStageHistory, Nat.lt_succ_iff]
  exact ⟨facts.1, facts.2, lookup, fun y => (lookup _ y).trans
    ⟨And.right, fun equal => ⟨Nat.unpair_left_le k, equal⟩⟩⟩

end PartitionPilot.Forcing

end

end OAI
