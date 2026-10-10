import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.BoundedTransformCompact

namespace OAI

/-! # Rational normalization of unital self-adjoint cycles and homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.boundedTransform_compact (c : OddCycle A)
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    IsCompactOperator (boundedTransform c.operator hs - c.operator : End c.space) := by
  apply boundedTransform_sub_compact
  simpa only [hπ, mul_one] using c.square_compact 1

theorem OddCycle.boundedTransform_star_compact (c : OddCycle A)
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    IsCompactOperator (star (boundedTransform c.operator hs - c.operator) : End c.space) := by
  rw [((boundedTransform_selfAdjoint c.operator hs).sub hs).star_eq]
  exact c.boundedTransform_compact hπ hs

theorem OddCycle.bounded_class (c : OddCycle A)
    (hπ : c.representation 1 = 1) (hs : IsSelfAdjoint c.operator) :
    cycleClass A (c.bounded hπ hs) = cycleClass A c := by
  have he : c.bounded hπ hs = c.compactPerturb _ (c.boundedTransform_compact hπ hs)
      (c.boundedTransform_star_compact hπ hs) := by
    simp only [bounded, compactPerturb, add_sub_cancel]
  rw [he]
  exact compactPerturb_class _ _ _ _

def OddHomotopy.bounded (h : OddHomotopy A)
    (hπ : ∀ t, h.representation t 1 = 1) (hs : ∀ t, IsSelfAdjoint (h.operator t)) :
    OddHomotopy A where
  space := h.space
  representation := h.representation
  operator t := boundedTransform (h.operator t) (hs t)
  continuous_representation := h.continuous_representation
  continuous_operator := continuous_boundedTransform h.operator hs h.continuous_operator
  commutator_compact t a := ((h.eval t).bounded (hπ t) (hs t)).commutator_compact a
  square_compact t a := ((h.eval t).bounded (hπ t) (hs t)).square_compact a
  adjoint_compact t a := ((h.eval t).bounded (hπ t) (hs t)).adjoint_compact a

@[simp] theorem OddHomotopy.bounded_eval (h : OddHomotopy A)
    (hπ : ∀ t, h.representation t 1 = 1) (hs : ∀ t, IsSelfAdjoint (h.operator t)) (t : Interval) :
    (h.bounded hπ hs).eval t = (h.eval t).bounded (hπ t) (hs t) := rfl

end CoarseAssembly.Analytic

end

end OAI
