import OAI.Topology.CoarseAssembly.RipsProperEmbedding

namespace OAI

/-! # Real-radius classes at integer coarsening stages -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {X Y : Type} [PseudoMetricSpace X] [PseudoMetricSpace Y]

def classAt (n : ℕ) (r : ℝ) (h : r = (n : ℝ))
    (a : LocallyFiniteK1 (Point X r)) : KX1 X := by
  refine (coarsening X).of n ?_
  change LocallyFiniteK1 (Point X (n : ℝ))
  exact h ▸ a

theorem classAt_zero (n : ℕ) (r : ℝ) (h : r = (n : ℝ)) :
    classAt (X := X) n r h 0 = 0 := by
  subst r
  exact (coarsening X).of n |>.map_zero

theorem embedding_classAt (e : X ↪ Y) (he : ∀ x y, dist (e x) (e y) ≤ dist x y)
    (n : ℕ) (r : ℝ) (h : r = (n : ℝ))
    (a : LocallyFiniteK1 (Point X r)) :
    (embeddingCoarsening e he).homologyMap (classAt (X := X) n r h a) =
      classAt (X := Y) n r h (pushforward (embeddingMap e he r) a) := by
  subst r
  dsimp only [classAt]
  exact CoarseningMorphism.homologyMap_of (embeddingCoarsening e he) n a

end CoarseAssembly.Rips

end

end OAI
