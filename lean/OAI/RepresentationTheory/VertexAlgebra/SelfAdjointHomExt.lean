import Mathlib

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
universe u v
variable {A : Type u} {B : Type v} [Ring A] [Ring B] [StarRing A] [StarRing B]
  [Algebra ℂ A] [Algebra ℂ B] [StarModule ℂ A]

theorem complex_selfAdjoint_decomposition (a : A) :
    a = (1/2 : ℂ) • (a + star a) + (-Complex.I/2 : ℂ) •
      (Complex.I • a + star (Complex.I • a)) := by
  simp only [star_smul, Complex.star_def, Complex.conj_I]
  simp only [smul_add, smul_smul]
  have h1 : (-Complex.I / 2 : ℂ) * Complex.I = 1/2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I, neg_neg]
  have h2 : (-Complex.I / 2 : ℂ) * -Complex.I = -(1/2) := by
    rw [mul_neg, h1]
  rw [h1, h2]
  module

theorem starAlgHom_ext_selfAdjoint (π ρ : A →⋆ₐ[ℂ] B)
    (h : ∀ a : A, IsSelfAdjoint a → π a = ρ a) : π = ρ := by
  apply DFunLike.ext
  intro a
  have hr := h (a + star a) (IsSelfAdjoint.add_star_self a)
  have hi := h (Complex.I • a + star (Complex.I • a))
    (IsSelfAdjoint.add_star_self (Complex.I • a))
  calc
    π a = π ((1/2 : ℂ) • (a + star a) + (-Complex.I/2 : ℂ) •
      (Complex.I • a + star (Complex.I • a))) := congrArg π (complex_selfAdjoint_decomposition a)
    _ = (1/2 : ℂ) • π (a + star a) + (-Complex.I/2 : ℂ) •
      π (Complex.I • a + star (Complex.I • a)) := by simp only [map_add, map_smul]
    _ = (1/2 : ℂ) • ρ (a + star a) + (-Complex.I/2 : ℂ) •
      ρ (Complex.I • a + star (Complex.I • a)) := by rw [hr, hi]
    _ = ρ ((1/2 : ℂ) • (a + star a) + (-Complex.I/2 : ℂ) •
      (Complex.I • a + star (Complex.I • a))) := by simp only [map_add, map_smul]
    _ = ρ a := congrArg ρ (complex_selfAdjoint_decomposition a).symm
end StronglyRationalVOA.BicommutantDensity

end

end OAI
