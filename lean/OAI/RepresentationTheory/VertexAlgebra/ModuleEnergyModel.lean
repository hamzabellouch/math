import OAI.RepresentationTheory.VertexAlgebra.SourceStrongRationality

namespace OAI

noncomputable section
universe u v
namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [AddCommGroup V] [Module ℂ V] (A : CFTTypeVOA V)

 

structure GradingRestrictedModule (W : Type v) [AddCommGroup W] [Module ℂ W]
    extends WeakModule A.toVertexAlgebra W where
  grade : ℂ → Submodule ℂ W
  grading_internal : DirectSum.IsInternal grade
  grade_finite : ∀ z, FiniteDimensional ℂ (grade z)
  conformal_energy : ∀ z, ∀ x ∈ grade z,
    mode fields A.conformalVector 1 x = z • x
  weights_bounded_below : ∃ B : ℝ, ∀ z : ℂ, z.re < B → grade z = ⊥

namespace GradingRestrictedModule
variable {A} {W : Type v} [AddCommGroup W] [Module ℂ W]
    (M : A.GradingRestrictedModule W)
 

theorem lower_truncated (z : ℂ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → M.grade (z - (n : ℂ)) = ⊥ := by
  obtain ⟨B,hB⟩ := M.weights_bounded_below
  obtain ⟨N,hN⟩ := exists_nat_gt (z.re-B)
  refine ⟨N, fun n hn => hB _ ?_⟩
  simp only [Complex.sub_re, Complex.natCast_re]
  have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
  linarith

def virasoroMode (n : ℤ) : Module.End ℂ W :=
  mode M.fields A.conformalVector (n+1)
def physicalMode (a : V) (d : ℕ) (m : ℤ) : Module.End ℂ W :=
  mode M.fields a (m+d-1)
def energyShift : Module.End ℂ W := 1 + M.virasoroMode 0
instance gradeFinite (z : ℂ) : FiniteDimensional ℂ (M.grade z) := M.grade_finite z

def gradingEquiv : W ≃ₗ[ℂ] DirectSum ℂ (fun z => M.grade z) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap M.grade) M.grading_internal).symm

def gradeComponent (z : ℂ) : W →ₗ[ℂ] W :=
  (M.grade z).subtype.comp ((DirectSum.component ℂ ℂ (fun z => M.grade z) z).comp
    M.gradingEquiv.toLinearMap)

end GradingRestrictedModule
end StronglyRationalVOA.CFTTypeVOA

namespace StronglyRationalVOA.CFTTypeVOA
variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {A : CFTTypeVOA V} (U : A.UnitaryStructure)
  {W : Type v} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

namespace GradingRestrictedModule
variable (M : A.GradingRestrictedModule W)
 

structure UnitaryStructure where
  invariant : ∀ d : ℕ, ∀ a ∈ A.grade d, ∀ n : ℤ, ∀ x y : W,
    inner ℂ (mode M.fields a n x) y =
      inner ℂ x (((-1 : ℂ)^d) •
        ∑ j ∈ Finset.range (d+1), ((j.factorial : ℂ)⁻¹) •
          mode M.fields ((A.virasoroMode 1 ^ j) (U.pct a))
            (2*(d:ℤ)-j-n-2) y)

def PolynomialEnergyBound (a : V) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ p k : ℕ, ∀ n : ℤ, ∀ x : W,
    ‖mode M.fields a n x‖ ≤ C * (1+|n|)^p * ‖(M.energyShift ^ k) x‖
def PolynomialEnergyBounds : Prop := ∀ a : V, M.PolynomialEnergyBound a

 

def SourceEnergyConclusion : Prop :=
  M.PolynomialEnergyBounds ∧
  (∀ d : ℕ, 2 ≤ d → ∀ a ∈ A.grade d, A.IsQuasiPrimary a → U.IsHermitian d a →
    ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ m : ℤ, ∀ x : W,
      ‖M.physicalMode a d m x‖ ≤ C * (1+|m|)^p * ‖(M.energyShift ^ (d-1)) x‖) ∧
  (∀ a ∈ A.grade 1, ∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ m : ℤ, ∀ x : W,
      ‖M.physicalMode a 1 m x‖ ≤ C * (1+|m|)^p * ‖M.energyShift x‖) ∧
  (∃ C : ℝ, 0 < C ∧ ∃ p : ℕ, ∀ m : ℤ, ∀ x : W,
      ‖M.virasoroMode m x‖ ≤ C * (1+|m|)^p * ‖M.energyShift x‖)
end GradingRestrictedModule
end StronglyRationalVOA.CFTTypeVOA

end

end OAI
