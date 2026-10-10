import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.ContinuousUnitalization

namespace OAI

/-! # Explicit norm-one representatives compatible with analytic homotopies -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.regularize_class (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    cycleClass A (c.regularize χ) = cycleClass A c :=
  ((c.unitalSelfAdjoint χ).bounded_class (c.unitalSelfAdjoint_unital χ)
    (c.unitalSelfAdjoint_selfAdjoint χ)).trans (c.unitalSelfAdjoint_class χ)

theorem OddCycle.regularize_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.regularize χ).representation 1 = 1 := c.unitalSelfAdjoint_unital χ

theorem OddCycle.regularize_selfAdjoint (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    IsSelfAdjoint (c.regularize χ).operator := boundedTransform_selfAdjoint _ _

theorem OddCycle.regularize_norm_le (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    ‖(c.regularize χ).operator‖ ≤ 1 := boundedTransform_norm_le _ _

def OddHomotopy.regularize (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) : OddHomotopy A :=
  (h.unitalSelfAdjoint χ).bounded
    (fun t => (h.eval t).unitalSelfAdjoint_unital χ)
    (fun t => (h.eval t).unitalSelfAdjoint_selfAdjoint χ)

@[simp] theorem OddHomotopy.regularize_eval (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) (t : Interval) :
    (h.regularize χ).eval t = (h.eval t).regularize χ := rfl

end CoarseAssembly.Analytic

end

end OAI
