import OAI.Topology.CoarseAssembly.RoeInclusion
import OAI.Topology.CoarseAssembly.RipsMapCalculus

namespace OAI

/-! # Composition of the actual geometric and spatial inclusion maps -/

noncomputable section

namespace CoarseAssembly

variable {X Y Z H : Type} [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem inclusionIsometry_comp (e : X ↪ Y) (f : Y ↪ Z) :
    (inclusionIsometry (H := H) f).comp (inclusionIsometry (H := H) e) =
      inclusionIsometry (H := H) (e.trans f) := by
  have hc : ((inclusionIsometry (H := H) f).comp (inclusionIsometry (H := H) e)).toContinuousLinearMap =
      (inclusionIsometry (H := H) (e.trans f)).toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
    intro x
    apply ContinuousLinearMap.ext
    intro h
    change inclusionIsometry f (inclusionIsometry e (lp.single 2 x h)) =
      inclusionIsometry (e.trans f) (lp.single 2 x h)
    rw [inclusionIsometry_single, inclusionIsometry_single, inclusionIsometry_single]
    rfl
  apply DFunLike.ext
  intro v
  exact DFunLike.congr_fun hc v

namespace DiscreteRoe

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

local instance roeAddX : AddCommMonoid (algebra (X := X) (H := H)) := inferInstance
local instance roeAddY : AddCommMonoid (algebra (X := Y) (H := H)) := inferInstance
local instance roeAddZ : AddCommMonoid (algebra (X := Z) (H := H)) := inferInstance

theorem inclusionHom_comp (e : X ↪ Y) (f : Y ↪ Z)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) :
    NonUnitalStarAlgHom.comp (R := ℂ)
      (A := algebra (X := X) (H := H)) (B := algebra (X := Y) (H := H))
      (C := algebra (X := Z) (H := H))
      (inclusionHom (X := Y) (Y := Z) (H := H) f hf)
      (inclusionHom (X := X) (Y := Y) (H := H) e he) =
      inclusionHom (X := X) (Y := Z) (H := H) (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) := by
  apply DFunLike.ext
  intro T
  apply Subtype.ext
  change operatorConjugation (inclusionIsometry f) (operatorConjugation (inclusionIsometry e) T.val) =
    operatorConjugation (inclusionIsometry (e.trans f)) T.val
  rw [operatorConjugation_comp, inclusionIsometry_comp]

end DiscreteRoe

namespace Rips

variable [PseudoMetricSpace X] [PseudoMetricSpace Y] [PseudoMetricSpace Z]

omit [DecidableEq X] [DecidableEq Y] [DecidableEq Z] in
theorem embeddingMap_comp (e : X ↪ Y) (f : Y ↪ Z)
    (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (hf : ∀ x y, dist (f x) (f y) ≤ dist x y) (r : ℝ) :
    (embeddingMap f hf r).comp (embeddingMap e he r) =
      embeddingMap (e.trans f) (fun x y => (hf (e x) (e y)).trans (he x y)) r := by
  apply CocompactMap.ext
  intro x
  exact mapPoint_comp e f he hf x

end Rips

end CoarseAssembly

end

end OAI
