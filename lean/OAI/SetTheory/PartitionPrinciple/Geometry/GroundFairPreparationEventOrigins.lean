import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticFairPreparationRecordedLimits

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
universe u
variable (M : TransitiveGround.{u})

theorem fairPreparationStep_event_origin
    {omega E0 stages U enumSelector prepSelector grid packed Q order nodes T : ZFSet.{u}}
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q order nodes T)
    (clock p births last nextClock q nextBirths event : ZFSet.{u})
    (step : FairPreparationStepCode omega E0 stages U enumSelector prepSelector grid
      (ZFSet.pair clock (ZFSet.pair p (ZFSet.pair births last)))
      (ZFSet.pair nextClock (ZFSet.pair q (ZFSet.pair nextBirths event)))) :
    event = ∅ ∨ ∃ alpha ∈ stages, ∃ y ∈ U,
      (∃ payload, y = ZFSet.pair q payload) ∧
      ZFSet.pair (ZFSet.pair alpha p) y ∈
        M.varyingPreparationRelation stages packed Q order nodes T ∧
      event = ZFSet.pair alpha y := by
  obtain ⟨n, p', b, last', m, q', nextBirths', event', source, target, _next,
    i, _hi, j, _hj, e, _he, newE, _hNew, _grid, _old, _selected, _append, branch⟩ := step
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 source
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  obtain ⟨rfl, tail⟩ := ZFSet.pair_inj.1 target
  obtain ⟨rfl, inner⟩ := ZFSet.pair_inj.1 tail
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
  rcases branch with idle | active
  · exact Or.inl idle.2.2
  · obtain ⟨alpha, hAlpha, y, hy, shape, _entry, edge, equal⟩ := active
    exact Or.inr ⟨alpha, hAlpha, y, hy, shape, selected edge, equal⟩

theorem fairPreparationEvents_origins
    {Q stages U E0 enumSelector prepSelector grid packed order nodes T orbit : ZFSet.{u}}
    (function : ZFSet.IsFunc ZFSet.omega
      (M.fairPreparationStates Q stages U E0 enumSelector) orbit)
    (selected : prepSelector ⊆ M.varyingPreparationRelation stages packed Q order nodes T)
    (clocks conditions births events : Nat → ZFSet.{u})
    (initialEvent : events 0 = ∅)
    (entries : ∀ k, ZFSet.pair (natSetCode k)
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k)
        (ZFSet.pair (births k) (events k)))) ∈ orbit)
    (steps : ∀ k, FairPreparationStepCode ZFSet.omega E0 stages U
      enumSelector prepSelector grid
      (ZFSet.pair (clocks k) (ZFSet.pair (conditions k) (ZFSet.pair (births k) (events k))))
      (ZFSet.pair (clocks (k + 1))
        (ZFSet.pair (conditions (k + 1)) (ZFSet.pair (births (k + 1)) (events (k + 1))))))
    (i event : ZFSet.{u})
    (edge : ZFSet.pair i event ∈ familyCodeGraph natSetCode events) :
    event = ∅ ∨ ∃ k : Nat, ∃ alpha ∈ stages, ∃ y ∈ U,
      i = natSetCode (k + 1) ∧ conditions k ∈ Q ∧ conditions (k + 1) ∈ Q ∧
      (∃ payload, y = ZFSet.pair (conditions (k + 1)) payload) ∧
      ZFSet.pair (ZFSet.pair alpha (conditions k)) y ∈
        M.varyingPreparationRelation stages packed Q order nodes T ∧
      event = ZFSet.pair alpha y ∧
      ZFSet.pair (natSetCode k)
        (ZFSet.pair (clocks k) (ZFSet.pair (conditions k)
          (ZFSet.pair (births k) (events k)))) ∈ orbit ∧
      ZFSet.pair (natSetCode (k + 1))
        (ZFSet.pair (clocks (k + 1)) (ZFSet.pair (conditions (k + 1))
          (ZFSet.pair (births (k + 1)) (events (k + 1))))) ∈ orbit := by
  have condition_mem (k : Nat) : conditions k ∈ Q := by
    have state := (ZFSet.pair_mem_prod.1 (function.1 (entries k))).2
    have bound := ((M.mem_fairPreparationStates Q stages U E0 enumSelector _).1 state).1
    exact (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 bound).2).1
  obtain ⟨n, equal⟩ := (mem_familyCodeGraph natSetCode events _).1 edge
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
  cases n with
  | zero => exact Or.inl initialEvent
  | succ k =>
    rcases M.fairPreparationStep_event_origin selected
      (clocks k) (conditions k) (births k) (events k)
      (clocks (k + 1)) (conditions (k + 1)) (births (k + 1)) (events (k + 1))
      (steps k) with idle | active
    · exact Or.inl idle
    · obtain ⟨alpha, hAlpha, y, hy, shape, relation, eventEq⟩ := active
      exact Or.inr ⟨k, alpha, hAlpha, y, hy, rfl, condition_mem k, condition_mem (k + 1),
        shape, relation, eventEq, entries k, entries (k + 1)⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
