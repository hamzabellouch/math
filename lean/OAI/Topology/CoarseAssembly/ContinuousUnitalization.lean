import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.UnitalRepresentative
import OAI.Topology.CoarseAssembly.BoundedCycleTransform

namespace OAI

/-! # A path-compatible unital self-adjoint representative -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type} [CStarAlgebra A]

theorem OddCycle.unitalSelfAdjoint_unital (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).representation 1 = 1 :=
  characterExtension_unital c.cutDown χ (cutDown_selfAdjoint c) (cutDown_complement c)
    (cutDown_square_compact c)

theorem OddCycle.unitalSelfAdjoint_selfAdjoint (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    IsSelfAdjoint (c.unitalSelfAdjoint χ).operator := cutDown_selfAdjoint c

theorem OddCycle.unitalSelfAdjoint_class (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    cycleClass A (c.unitalSelfAdjoint χ) = cycleClass A c :=
  (characterExtension_class c.cutDown χ (cutDown_selfAdjoint c) (cutDown_complement c)
    (cutDown_square_compact c)).trans (cutDown_class c)

theorem OddCycle.unitalSelfAdjoint_operator (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) :
    (c.unitalSelfAdjoint χ).operator = symmetricCutDown (c.representation 1) c.operator :=
  c.cutDown_operator

theorem OddCycle.unitalSelfAdjoint_representation (c : OddCycle A) (χ : A →⋆ₐ[ℂ] ℂ) (a : A) :
    (show End c.space from (c.unitalSelfAdjoint χ).representation a) =
      c.representation a + χ a • (1 - c.representation 1) := rfl

variable {T : Type*} [TopologicalSpace T] {H : HilbertSpace}

theorem continuous_symmetricCutDown (P F : T → End H)
    (hP : Continuous P) (hF : Continuous F) :
    Continuous (fun t => symmetricCutDown (P t) (F t)) := by
  unfold symmetricCutDown
  fun_prop

def OddHomotopy.unitalSelfAdjoint (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ) : OddHomotopy A where
  space := h.space
  representation t := ((h.eval t).unitalSelfAdjoint χ).representation
  operator t := ((h.eval t).unitalSelfAdjoint χ).operator
  continuous_representation a := by
    change Continuous (fun t => h.representation t a + χ a • (1 - h.representation t 1))
    have hp : Continuous (fun t => (1 : End h.space) - h.representation t 1) :=
      continuous_const.sub (h.continuous_representation 1)
    exact (h.continuous_representation a).add
      ((continuous_const : Continuous (fun _ : Interval => χ a)).smul hp)
  continuous_operator := by
    have hc := continuous_symmetricCutDown (fun t => h.representation t 1) h.operator
      (h.continuous_representation 1) h.continuous_operator
    exact hc.congr (fun t => ((h.eval t).unitalSelfAdjoint_operator χ).symm)
  commutator_compact t a := ((h.eval t).unitalSelfAdjoint χ).commutator_compact a
  square_compact t a := ((h.eval t).unitalSelfAdjoint χ).square_compact a
  adjoint_compact t a := ((h.eval t).unitalSelfAdjoint χ).adjoint_compact a

@[simp] theorem OddHomotopy.unitalSelfAdjoint_eval (h : OddHomotopy A) (χ : A →⋆ₐ[ℂ] ℂ)
    (t : Interval) : (h.unitalSelfAdjoint χ).eval t = (h.eval t).unitalSelfAdjoint χ := rfl

end CoarseAssembly.Analytic

end

end OAI
