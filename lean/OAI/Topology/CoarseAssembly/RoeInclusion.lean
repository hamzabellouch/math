import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.InclusionModule
import OAI.Topology.CoarseAssembly.RoeTransfer

namespace OAI

/-! # The reduced Roe map for an actual injective nonexpanding inclusion

Extension by zero preserves each matrix entry on the image, and all other
entries vanish. Thus propagation and local compactness are proved directly
before extending to the norm closure.
-/

noncomputable section

namespace CoarseAssembly.DiscreteRoe

universe sourceUniverse targetUniverse coefficientUniverse

attribute [local instance] OAI.CoarseAssembly.DiscreteRoe.inclusionExponentFact

variable {X : Type sourceUniverse} {Y : Type targetUniverse} {H : Type coefficientUniverse}
  [sourceDecidable : DecidableEq X] [targetDecidable : DecidableEq Y]
  [coefficientNormed : NormedAddCommGroup H] [coefficientInner : InnerProductSpace ℂ H]
  [coefficientComplete : CompleteSpace H]

theorem inclusion_adjoint_apply (e : X ↪ Y) (v : Module Y H) (x : X) :
    (inclusionIsometry (H := H) e).toContinuousLinearMap.adjoint v x = v (e x) := by
  have hi : (inclusionIsometry (H := H) e).toContinuousLinearMap.comp (insert x) =
      insert (e x) := by
    apply ContinuousLinearMap.ext
    intro h
    exact inclusionIsometry_single e x h
  have ha := congrArg ContinuousLinearMap.adjoint hi
  simp only [ContinuousLinearMap.adjoint_comp, insert_adjoint] at ha
  exact DFunLike.congr_fun ha v

theorem inclusion_entry (e : X ↪ Y) (T : Operator X H) (x y : X) :
    entry (operatorConjugation (inclusionIsometry e) T) (e x) (e y) = entry T x y := by
  ext h
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply]
  rw [← inclusionIsometry_single e y h, adjoint_apply_isometry]
  exact inclusionVector_apply e _ x

omit [DecidableEq X] in
theorem inclusion_entry_row_zero (e : X ↪ Y) (T : Operator X H) (x y : Y)
    (hx : x ∉ Set.range e) :
    entry (operatorConjugation (inclusionIsometry e) T) x y = 0 := by
  ext h
  exact inclusionVector_zero e _ x hx

theorem inclusion_entry_col_zero (e : X ↪ Y) (T : Operator X H) (x y : Y)
    (hy : y ∉ Set.range e) :
    entry (operatorConjugation (inclusionIsometry e) T) x y = 0 := by
  ext h
  have hz : (inclusionIsometry (H := H) e).toContinuousLinearMap.adjoint
      (lp.single 2 y h) = 0 := by
    apply lp.ext
    funext z
    rw [inclusion_adjoint_apply]
    exact lp.single_apply_ne (E := fun _ : Y => H) 2 y h (fun heq => hy ⟨z, heq⟩)
  simp only [entry_apply, operatorConjugation, ContinuousLinearMap.comp_apply, hz, map_zero,
    lp.coeFn_zero, Pi.zero_apply, zero_apply]

theorem inclusion_compactEntries (e : X ↪ Y) {T : Operator X H}
    (hT : CompactEntries T) : CompactEntries (operatorConjugation (inclusionIsometry e) T) := by
  intro x y
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hy
      rw [inclusion_entry]
      exact hT a b
    · rw [inclusion_entry_col_zero e T _ _ hy]
      exact isCompactOperator_zero
  · rw [inclusion_entry_row_zero e T _ _ hx]
    exact isCompactOperator_zero

variable [sourceMetric : PseudoMetricSpace X] [targetMetric : PseudoMetricSpace Y]

theorem inclusion_propagation (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) {T : Operator X H} {r : ℝ}
    (hT : PropagationLE r T) : PropagationLE r (operatorConjugation (inclusionIsometry e) T) := by
  intro x y hxy
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    by_cases hy : y ∈ Set.range e
    · obtain ⟨b, rfl⟩ := hy
      rw [inclusion_entry]
      exact hT a b (hxy.trans_le (he a b))
    · exact inclusion_entry_col_zero e T _ _ hy
  · exact inclusion_entry_row_zero e T _ _ hx

theorem inclusion_generator (e : X ↪ Y)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y) {T : Operator X H}
    (hT : Generator T) : Generator (operatorConjugation (inclusionIsometry e) T) := by
  obtain ⟨⟨r, hr, hprop⟩, hc, hcs⟩ := hT
  refine ⟨⟨r, hr, inclusion_propagation e he hprop⟩, inclusion_compactEntries e hc, ?_⟩
  rw [← operatorConjugation_star (inclusionIsometry e) T]
  exact inclusion_compactEntries e hcs

theorem inclusion_mapsToRoe
    {Domain : Type sourceUniverse} {Range : Type targetUniverse}
    {Coefficient : Type coefficientUniverse}
    [domainDecidable : DecidableEq Domain] [rangeDecidable : DecidableEq Range]
    [normedCoefficient : NormedAddCommGroup Coefficient]
    [innerCoefficient : InnerProductSpace ℂ Coefficient]
    [completeCoefficient : CompleteSpace Coefficient]
    [domainMetric : PseudoMetricSpace Domain] [rangeMetric : PseudoMetricSpace Range]
    (e : Domain ↪ Range) (he : ∀ x y, dist (e x) (e y) ≤ dist x y) :
    MapsToRoe.{sourceUniverse, targetUniverse, coefficientUniverse}
      (D := Domain) (X := Range) (H := Coefficient)
      (inclusionIsometry.{sourceUniverse, targetUniverse, coefficientUniverse}
        (H := Coefficient) e) :=
  let isometry := @inclusionIsometry.{sourceUniverse, targetUniverse, coefficientUniverse}
    Domain Range Coefficient normedCoefficient innerCoefficient.toNormedSpace e
  let conjugation := @operatorConjugationHom.{max sourceUniverse coefficientUniverse,
      max targetUniverse coefficientUniverse}
    (Module Domain Coefficient) (Module Range Coefficient)
    (lp.normedAddCommGroup (E := fun _ : Domain => Coefficient) (p := 2)
      (hp := inclusionExponentFact))
    (lp.instInnerProductSpace (𝕜 := ℂ) (G := fun _ : Domain => Coefficient))
    (lp.completeSpace (E := fun _ : Domain => Coefficient) (p := 2))
    (lp.normedAddCommGroup (E := fun _ : Range => Coefficient) (p := 2)
      (hp := inclusionExponentFact))
    (lp.instInnerProductSpace (𝕜 := ℂ) (G := fun _ : Range => Coefficient))
    (lp.completeSpace (E := fun _ : Range => Coefficient) (p := 2)) isometry
  fun operator operator_mem =>
    @map_mem.{sourceUniverse, targetUniverse, coefficientUniverse}
      Domain Range Coefficient normedCoefficient innerCoefficient
      domainDecidable rangeDecidable completeCoefficient domainMetric rangeMetric conjugation
      (@conjugation_continuous.{sourceUniverse, targetUniverse, coefficientUniverse}
        Domain Range Coefficient normedCoefficient innerCoefficient completeCoefficient isometry)
      (fun generator is_generator =>
        @generator_mem.{targetUniverse, coefficientUniverse}
          Range Coefficient normedCoefficient innerCoefficient rangeDecidable
          completeCoefficient rangeMetric (conjugation generator)
          (@inclusion_generator.{sourceUniverse, targetUniverse, coefficientUniverse}
            Domain Range Coefficient domainDecidable rangeDecidable normedCoefficient
            innerCoefficient completeCoefficient domainMetric rangeMetric e he
            generator is_generator))
      operator operator_mem

end CoarseAssembly.DiscreteRoe

end

end OAI
