import OAI.Topology.CoarseAssembly.ExplicitCircleFamily
import OAI.Topology.CoarseAssembly.CompactFamilyHomotopy
import OAI.Topology.CoarseAssembly.FamilyFilling

namespace OAI

/-! # Filling the explicit circle family without countable-additivity inputs -/

noncomputable section

namespace CoarseAssembly

open Rips Analytic
open scoped ZeroAtInfty

theorem windingCircleCycle_representation_const (z : ℂ) :
    windingCircleCycle.representation (ContinuousMap.const WindingCircle z) =
      z • (1 : End circleSequenceSpace) := by
  change circleRepresentation (ContinuousMap.const Circle z) = _
  have he : (ContinuousMap.const Circle z : C(Circle, ℂ)) = z • 1 := by
    ext x
    simp
  rw [he, map_smul, map_one]

variable {Y : ℕ → Type} [∀ j, TopologicalSpace (Y j)] [∀ j, T2Space (Y j)]

theorem circleFamily_constant_degenerate (y : ∀ j, Y j) :
    (circleSigmaCycle.precomp (pullback
      (compactFamilyMap (fun j => ContinuousMap.const WindingCircle (y j))))).Degenerate := by
  dsimp only [OddCycle.Degenerate, OddCycle.precomp, circleSigmaCycle, sigmaCycle]
  constructor
  · intro f
    apply ContinuousLinearMap.ext
    intro x
    apply lp.ext
    funext j
    have he : sigmaFunctionRestriction CircleFamily j
        (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f) =
        ContinuousMap.const WindingCircle (f ⟨j, y j⟩) := by
      ext z
      rfl
    change windingCircleCycle.operator
        (windingCircleCycle.representation (sigmaFunctionRestriction CircleFamily j
          (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f)) (x j)) -
        windingCircleCycle.representation (sigmaFunctionRestriction CircleFamily j
          (pullback (compactFamilyMap (fun k => ContinuousMap.const WindingCircle (y k))) f))
          (windingCircleCycle.operator (x j)) = 0
    rw [he, windingCircleCycle_representation_const]
    change windingCircleCycle.operator ((f ⟨j, y j⟩) • (x j)) -
      (f ⟨j, y j⟩) • windingCircleCycle.operator (x j) = 0
    rw [map_smul, sub_self]
  constructor
  · intro f
    have hs := sigmaCycleOperator_sq CircleFamily (fun _ => windingCircleCycle) 1 (by norm_num)
      (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_sq)
    rw [hs, sub_self, zero_mul]
  · intro f
    have hs := sigmaCycleOperator_selfAdjoint CircleFamily (fun _ => windingCircleCycle) 1
      (by norm_num) (fun _ => windingCircleCycle_norm) (fun _ => negativeCircleOperator_selfAdjoint)
    rw [hs.star_eq, sub_self, zero_mul]

theorem explicitCircleFamily_constant_zero (y : ∀ j, Y j) :
    pushforward (compactFamilyMap (fun j => ContinuousMap.const WindingCircle (y j)))
      explicitCircleFamily = 0 := by
  change precomp _ (cycleClass C₀(Sigma CircleFamily, ℂ) circleSigmaCycle) = 0
  rw [precomp_cycleClass]
  exact degenerate_zero _ (circleFamily_constant_degenerate y)

theorem explicitCircleFamily_filled_zero (o : ∀ j, Disc j)
    (p : ∀ j, (discGraph j).Walk (o j) (o j)) :
    pushforward (compactFamilyMap (filledBoundaryLoops o p)) explicitCircleFamily = 0 := by
  have h (j : ℕ) : (filledBoundaryLoops o p j).Homotopy
      (ContinuousMap.const WindingCircle (filledDiscCenter j)) := by
    have hc : (filledDiscContraction j).center = filledDiscCenter j := rfl
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp, hc] using
      (filledDiscContraction j).homotopy.compContinuousMap (filledBoundaryLoops o p j)
  rw [compactFamily_homotopy_invariance _ _ h]
  exact explicitCircleFamily_constant_zero _

theorem explicitBaseBoundaryFamily_zero (o : ∀ j, Disc j)
    (p : ∀ j, (discGraph j).Walk (o j) (o j)) :
    letI := separatedMetric o
    pushforward (ripsFamilyMap o 1 (baseBoundaryLoops o p)) explicitCircleFamily = 0 := by
  let := separatedMetric o
  rw [boundaryFamily_factors o p, pushforward_comp, AddMonoidHom.comp_apply,
    explicitCircleFamily_filled_zero o p, map_zero]

end CoarseAssembly

end

end OAI
