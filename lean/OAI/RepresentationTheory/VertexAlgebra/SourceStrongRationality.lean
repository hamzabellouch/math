import OAI.RepresentationTheory.VertexAlgebra.Foundations

namespace OAI

noncomputable section
namespace StronglyRationalVOA.CFTTypeVOA
universe u v
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (A : CFTTypeVOA V)
 
abbrev GradedDual := DirectSum ℕ (fun d => Module.Dual ℂ (A.grade d))
 

def gradedDualPairing (φ : A.GradedDual) (b : V) : ℂ := by
  classical
  exact φ.sum (fun d f => f (A.gradingEquiv b d))
 

def IsSelfContragredient : Prop :=
  ∃ e : V ≃ₗ[ℂ] A.GradedDual,
    ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n : ℤ, ∀ b c : V,
      A.gradedDualPairing (e (mode A.fields a n b)) c =
        ((-1 : ℂ)^d) * ∑ j ∈ Finset.range (d+1), ((j.factorial : ℂ)⁻¹) *
          A.gradedDualPairing (e b)
            (mode A.fields ((A.virasoroMode 1 ^ j) a) (2*(d:ℤ)-j-n-2) c)
 

def IsStronglyRational : Prop :=
  A.IsSelfContragredient ∧ A.IsRational.{u,v} ∧ A.toVertexAlgebra.C2Cofinite
end StronglyRationalVOA.CFTTypeVOA

end

end OAI
