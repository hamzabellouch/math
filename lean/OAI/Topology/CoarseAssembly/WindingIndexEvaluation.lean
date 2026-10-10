import OAI.Topology.CoarseAssembly.WindingHomotopy

namespace OAI

/-! # Reducing the winding index formula to one generator evaluation

The pairing, its naturality, homotopy invariance and power law are proved.
Only an actual circle class with coordinate index one remains to construct.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

theorem circleUnitary_degree (n : ℤ) : circleUnitary (circleDegree n) =
    circleUnitary (ContinuousMap.id WindingCircle) ^ n := by
  apply ContinuousMap.ext
  intro z
  exact AddCircle.toCircle_zsmul z n

theorem winding_index_hom (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ))
    (hL : ∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle)) :
    compactIndexPairing (circleUnitary g) =
      n • compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) := by
  let toCircleMap : C(WindingCircle, Circle) := ⟨AddCircle.toCircle, AddCircle.continuous_toCircle⟩
  have h := compactIndexPairing_homotopy
    ((ContinuousMap.Homotopy.refl toCircleMap).comp (windingHomotopy g n L hL))
  change compactIndexPairing (circleUnitary g) = compactIndexPairing (circleUnitary (circleDegree n)) at h
  rw [circleUnitary_degree, compactIndexPairing_zpow] at h
  exact h

theorem winding_index (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ))
    (hL : ∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle))
    (α : LocallyFiniteK1 WindingCircle) :
    compactIndexPairing (circleUnitary g) α =
      n * compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) α := by
  simpa only [AddMonoidHom.smul_apply, zsmul_eq_mul, Int.cast_id] using
    DFunLike.congr_fun (winding_index_hom g n L hL) α

/-- All the published circle fields follow from a single coordinate-index-one class. -/
def circleInputOfIndexOne (α : LocallyFiniteK1 WindingCircle)
    (hα : compactIndexPairing (circleUnitary (ContinuousMap.id WindingCircle)) α = 1) :
    PublishedCircleInput where
  fundamental := α
  pairing f := compactIndexPairing (circleUnitary f)
  loop_naturality f γ := by
    have h := DFunLike.congr_fun (compactIndexPairing_natural (circleUnitary f) γ) α
    exact h
  winding g n L hL := by
    rw [winding_index g n L hL α, hα, mul_one]

end CoarseAssembly

end

end OAI
