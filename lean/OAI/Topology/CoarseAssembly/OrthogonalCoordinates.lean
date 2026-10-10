import OAI.Topology.CoarseAssembly.ProductIndex

namespace OAI

/-! # Coordinates for an orthogonal direct sum of Fredholm cycles -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [NonUnitalCStarAlgebra A] {c d e : OddCycle A}

def OddCycle.IsDirectSum.coordinates (h : c.IsDirectSum d e) : e.space →L[ℂ] c.space × d.space :=
  h.left.toContinuousLinearMap.adjoint.prod h.right.toContinuousLinearMap.adjoint

def OddCycle.IsDirectSum.inclusion (h : c.IsDirectSum d e) : c.space × d.space →L[ℂ] e.space :=
  h.left.toContinuousLinearMap.coprod h.right.toContinuousLinearMap

theorem OddCycle.IsDirectSum.orthogonal_reverse (h : c.IsDirectSum d e) :
    h.right.toContinuousLinearMap.adjoint ∘L h.left.toContinuousLinearMap = 0 := by
  have hz := congrArg ContinuousLinearMap.adjoint h.orthogonal
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    map_zero] using hz

theorem OddCycle.IsDirectSum.coordinates_inclusion (h : c.IsDirectSum d e) :
    h.coordinates ∘L h.inclusion = ContinuousLinearMap.id ℂ (c.space × d.space) := by
  apply ContinuousLinearMap.ext
  intro x
  apply Prod.ext
  · change h.left.toContinuousLinearMap.adjoint (h.left x.1 + h.right x.2) = x.1
    rw [map_add, adjoint_apply_isometry]
    have hz : h.left.toContinuousLinearMap.adjoint (h.right x.2) = 0 :=
      DFunLike.congr_fun h.orthogonal x.2
    rw [hz, add_zero]
  · change h.right.toContinuousLinearMap.adjoint (h.left x.1 + h.right x.2) = x.2
    rw [map_add, adjoint_apply_isometry]
    have hz : h.right.toContinuousLinearMap.adjoint (h.left x.1) = 0 :=
      DFunLike.congr_fun h.orthogonal_reverse x.1
    rw [hz, zero_add]

theorem OddCycle.IsDirectSum.inclusion_coordinates (h : c.IsDirectSum d e) :
    h.inclusion ∘L h.coordinates = ContinuousLinearMap.id ℂ e.space := by
  apply ContinuousLinearMap.ext
  intro x
  exact DFunLike.congr_fun h.exhaustive x

def OddCycle.IsDirectSum.coordinateEquiv (h : c.IsDirectSum d e) :
    e.space ≃L[ℂ] c.space × d.space :=
  ContinuousLinearEquiv.equivOfInverse' h.coordinates h.inclusion
    h.coordinates_inclusion h.inclusion_coordinates

end CoarseAssembly.Analytic

end

end OAI
