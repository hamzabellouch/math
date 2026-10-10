import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionHeightSteps

namespace OAI

section

namespace PartitionPilot.Forcing.GroundCompressionState
open SetFormula
universe u
variable {M : TransitiveGround.{u}}
variable {P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters : ZFSet.{u}}
variable {seed : FixedCompressionSeed P0 r0 μ0 A0 τ I Sources Reps G m inv one T Filters}
variable (state : GroundCompressionState M seed)

theorem exists_column_bounded_height_step
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (constant : RecursiveTemplateConstancy P0 r0 μ0 state.data)
    {C D rD c original old : ZFSet.{u}}
    (hP0 : P0 ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hrD : rD ∈ M.sets) (hc : c ∈ M.sets)
    (hOriginal : original ∈ M.sets) (hOld : old ∈ M.sets)
    (originalCode : StrictLexHeightCode P0 C D r0 original rD)
    (oldCode : StrictLexHeightCode state.data.D C D state.data.rD old rD)
    (columns : ordinalSetProperty C) (target : DenseOrderCode D rD)
    (above : ∀ lo ∈ D, ∃ hi ∈ D, ZFSet.pair lo hi ∈ rD)
    (coordinateInjection : InjectionCode D ZFSet.omega c)
    (originalSmall : M.groundEmbeddable (relationImage P0 (ZFSet.prod C D) original) ZFSet.omega)
    (extension : original ⊆ old)
    (bounded : ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ old → a ∈ heightColumns P0 C D original) :
    ∃ height ∈ M.sets,
      StrictLexHeightCode state.data.currentCarrier C D state.data.currentOrder height rD ∧
      old ⊆ height ∧ original ⊆ height ∧
      ∀ x a q, ZFSet.pair x (ZFSet.pair a q) ∈ height → a ∈ heightColumns P0 C D original := by
  have oldSmall := (M.countable_height_range_of_old_columns pairing unions powers separation infinite choice
    hP0 state.ground.carrier hC hD hOriginal hOld originalSmall ⟨c, hc, coordinateInjection⟩ bounded).2
  obtain ⟨height, hHeight, code, restrict, _, _, columnBound, _⟩ := state.exists_height_step
    pairing unions powers separation collection infinite choice constant hC hD hrD hc hOriginal hOld
    originalCode oldCode columns target above coordinateInjection originalSmall oldSmall
  have inclusion : old ⊆ height := by
    intro z hz
    obtain ⟨x, hx, y, _, rfl⟩ := ZFSet.mem_prod.1 (oldCode.function.1 hz)
    exact (restrict x hx y).2 hz
  refine ⟨height, hHeight, code, inclusion, fun _ hx => inclusion (extension hx), ?_⟩
  intro x a q entry
  exact heightColumns_subset_of_bound bounded (columnBound x a q entry)

end PartitionPilot.Forcing.GroundCompressionState

end

end OAI
