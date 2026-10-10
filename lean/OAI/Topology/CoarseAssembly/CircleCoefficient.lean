import OAI.Topology.CoarseAssembly.NegativeCircleCycle
import OAI.Topology.CoarseAssembly.CircleInputReduction

namespace OAI

/-! # An unconditional circle class of coordinate index one -/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

variable {X : Type} [TopologicalSpace X] [CompactSpace X]

def compactFunctionForget : C₀(X, ℂ) →⋆ₙₐ[ℂ] C(X, ℂ) where
  toFun f := f.toContinuousMap
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem compactFunctionForget_lift :
    (compactFunctionForget (X := X)).comp compactFunctionLift = NonUnitalStarAlgHom.id ℂ C(X, ℂ) := by
  ext f x
  rfl

def negativeCircleClass : LocallyFiniteK1 Circle :=
  cycleClass C₀(Circle, ℂ) (negativeCircleCycle.precomp compactFunctionForget)

theorem negativeCircleClass_coordinate_index :
    compactIndexPairing (ContinuousMap.id Circle) negativeCircleClass = 1 := by
  rw [negativeCircleClass, compactIndexPairing_cycleClass, OddCycle.precomp_comp,
    compactFunctionForget_lift, OddCycle.precomp_id]
  exact negativeCircleCycle_coordinate_index

end CoarseAssembly.Analytic

namespace CoarseAssembly

open Analytic

def circleFundamental : LocallyFiniteK1 WindingCircle :=
  pushforward (compactMap ((AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm : C(Circle, WindingCircle)))
    negativeCircleClass

theorem circleFundamental_coordinate_index :
    compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) circleFundamental = 1 := by
  let e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have he : (circleUnitary (ContinuousMap.id WindingCircle)).comp (e.symm : C(Circle, WindingCircle)) =
      ContinuousMap.id Circle := by
    apply ContinuousMap.ext
    intro z
    change AddCircle.toCircle (e.symm z) = z
    rw [← AddCircle.homeomorphCircle_apply one_ne_zero]
    exact e.apply_symm_apply z
  change compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle))
    (pushforward (compactMap (e.symm : C(Circle, WindingCircle))) negativeCircleClass) = 1
  have h := DFunLike.congr_fun
    (compactIndexPairing_natural (circleUnitary (ContinuousMap.id WindingCircle)) (e.symm : C(Circle, WindingCircle)))
    negativeCircleClass
  rw [he] at h
  exact h.trans negativeCircleClass_coordinate_index

/-- The complete published circle-index input, now a theorem. -/
def provedCircleInput : PublishedCircleInput :=
  circleInputOfIndexOne circleFundamental circleFundamental_coordinate_index

open Congruence Rips

local instance coefficientReductionMetric : MetricSpace VertexUnion :=
  vertexUnionMetric elementaryMoves chosenHolonomyUnit

/-- Main theorem with the circle and compact-filling inputs discharged. -/
theorem bounded_geometry_counterexample_from_additivity_index_gap
    (hadd : CountableAdditivityInput CircleFamily) (hfill : CountableAdditivityInput FilledDisc)
    (index : PublishedBoundaryAssemblyInput) (hgap : PublishedKazhdanInput) :
    ProperSpace VertexUnion ∧ UniformFiniteBalls VertexUnion ∧
      (∀ x y : VertexUnion, x ≠ y → 1 ≤ dist x y) ∧
      ∃ α : KX1 VertexUnion,
        (∀ n : ℤ, n ≠ 0 → n • α ≠ 0) ∧ index.total.assembly α = 0 ∧
        (1 : ℚ) ⊗ₜ[ℤ] α ≠ 0 ∧
        ¬ Function.Injective index.total.assembly ∧
        ¬ Function.Injective (index.total.assembly.toIntLinearMap.lTensor ℚ) :=
  bounded_geometry_counterexample_from_circle_index_gap provedCircleInput hadd hfill index hgap

end CoarseAssembly

end

end OAI
