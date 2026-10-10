import OAI.Topology.CoarseAssembly.Definitions
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import OAI.Topology.CoarseAssembly.Conjugation

namespace OAI

/-!
# Odd analytic Fredholm modules

These are the actual operator cycles for `KK₁(A, ℂ)`: a separable Hilbert
space, a star representation of `A`, and an operator whose commutator,
self-adjointness defect and square defect are locally compact. We keep
degenerate cycles, unitary equivalence, direct sum and norm homotopy explicit
so that the analytic group can be formed as a quotient, rather than supplied
as an arbitrary abelian group.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

attribute [instance] HilbertSpace.normed HilbertSpace.inner
  HilbertSpace.complete HilbertSpace.secondCountable

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A} {B : Type u} [NonUnitalCStarAlgebra B]

namespace OddCycle

theorem Degenerate.precomp {c : OddCycle A} (hc : c.Degenerate)
    (φ : B →⋆ₙₐ[ℂ] A) : (c.precomp φ).Degenerate :=
  ⟨fun b => hc.1 (φ b), fun b => hc.2.1 (φ b), fun b => hc.2.2 (φ b)⟩

@[simp] theorem precomp_id (c : OddCycle A) :
    c.precomp (NonUnitalStarAlgHom.id ℂ A) = c := by cases c; rfl

@[simp] theorem precomp_comp {C : Type u} [NonUnitalCStarAlgebra C]
    (c : OddCycle A) (φ : B →⋆ₙₐ[ℂ] A) (ψ : C →⋆ₙₐ[ℂ] B) :
    (c.precomp φ).precomp ψ = c.precomp (φ.comp ψ) := rfl

end OddCycle

namespace OddHomotopy

@[simp] theorem precomp_eval (h : OddHomotopy A) (φ : B →⋆ₙₐ[ℂ] A) (t : Interval) :
    (h.precomp φ).eval t = (h.eval t).precomp φ := rfl

end OddHomotopy

end CoarseAssembly.Analytic

end

end OAI
