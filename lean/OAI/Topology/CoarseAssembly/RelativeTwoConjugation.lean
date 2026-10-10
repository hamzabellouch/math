import OAI.Topology.CoarseAssembly.RelativeTwoDiagonal

namespace OAI

/-! # Relative two-by-two conjugation by idealizing operators -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

variable {A R : Type*} [CStarAlgebra A] [CStarAlgebra R]

def matrixTwoUnitalStarHom (φ : A →⋆ₐ[ℂ] R) :
    Matrix (Fin 2) (Fin 2) A →⋆ₐ[ℂ] Matrix (Fin 2) (Fin 2) R :=
  { matrixTwoStarHom φ.toNonUnitalStarAlgHom with
    map_one' := by
      ext i j
      by_cases h : i = j <;> simp [matrixTwoStarHom, Matrix.one_apply, h]
    commutes' := by
      intro z
      ext i j
      by_cases h : i = j <;>
        simp [matrixTwoStarHom, Algebra.algebraMap_eq_smul_one, h] }

@[simp] theorem matrixTwoUnitalStarHom_apply (φ : A →⋆ₐ[ℂ] R)
    (M : Matrix (Fin 2) (Fin 2) A) (i j : Fin 2) :
    matrixTwoUnitalStarHom φ M i j = φ (M i j) := rfl

theorem matrixTwoUnitalStarHom_continuous (φ : A →⋆ₐ[ℂ] R) (hc : Continuous φ) :
    Continuous (matrixTwoUnitalStarHom φ) :=
  matrixTwoStarHom_continuous φ.toNonUnitalStarAlgHom hc

def mapTwoUnitary (φ : A →⋆ₐ[ℂ] R)
    (u : unitary (Matrix (Fin 2) (Fin 2) A)) :
    unitary (Matrix (Fin 2) (Fin 2) R) :=
  Unitary.map (StarMonoidHom.ofClass (matrixTwoUnitalStarHom φ)) u

@[simp] theorem mapTwoUnitary_diagonal (φ : A →⋆ₐ[ℂ] R) (u v : unitary A) :
    mapTwoUnitary φ (diagonalTwoUnitary u v) =
      diagonalTwoUnitary (Unitary.map (StarMonoidHom.ofClass φ) u) (Unitary.map (StarMonoidHom.ofClass φ) v) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mapTwoUnitary, diagonalTwoUnitary, Matrix.diagonal, matrixTwoUnitalStarHom, matrixTwoStarHom]

def conjugatedTwoUnitary (w u : unitary (Matrix (Fin 2) (Fin 2) R)) :
    unitary (Matrix (Fin 2) (Fin 2) R) := w * u * star w

theorem conjugatedTwoUnitary_defect (w u : unitary (Matrix (Fin 2) (Fin 2) R)) :
    (conjugatedTwoUnitary w u : Matrix (Fin 2) (Fin 2) R) - 1 =
      (w : Matrix (Fin 2) (Fin 2) R) * ((u : Matrix (Fin 2) (Fin 2) R) - 1) *
        star (w : Matrix (Fin 2) (Fin 2) R) := by
  change w.val * u.val * star w.val - 1 = w.val * (u.val - 1) * star w.val
  have hw : w.val * star w.val = 1 := by
    have h := Unitary.coe_mul_star_self w
    change w.val * star w.val = 1 at h
    exact h
  rw [mul_sub, mul_one, sub_mul, hw]

@[simp] theorem mapTwoUnitary_one (φ : A →⋆ₐ[ℂ] R) : mapTwoUnitary φ 1 = 1 := by
  apply Subtype.ext
  exact map_one (matrixTwoUnitalStarHom φ)

theorem mapTwoUnitary_conjugate (φ : A →⋆ₐ[ℂ] R)
    (w u : unitary (Matrix (Fin 2) (Fin 2) A)) :
    mapTwoUnitary φ (conjugatedTwoUnitary w u) =
      conjugatedTwoUnitary (mapTwoUnitary φ w) (mapTwoUnitary φ u) := by
  apply Subtype.ext
  change matrixTwoUnitalStarHom φ (w.val * u.val * star w.val) =
    matrixTwoUnitalStarHom φ w.val * matrixTwoUnitalStarHom φ u.val *
      star (matrixTwoUnitalStarHom φ w.val)
  rw [map_mul, map_mul, map_star]

variable (S : NonUnitalStarSubalgebra ℂ R)

/-- The entries of the conjugation defect remain in the idealized algebra. -/
theorem conjugatedTwoUnitary_relative (φ : A →⋆ₐ[ℂ] R)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (w : unitary (Matrix (Fin 2) (Fin 2) A))
    (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    ∀ i j, ((conjugatedTwoUnitary (mapTwoUnitary φ w) u :
      Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S := by
  intro i j
  rw [conjugatedTwoUnitary_defect]
  simp only [Matrix.mul_apply]
  apply S.sum_mem
  intro k _
  rw [Finset.sum_mul]
  apply S.sum_mem
  intro l _
  rw [Matrix.star_apply]
  change φ (w.val i l) * ((u.val - 1) l k) * star (φ (w.val j k)) ∈ S
  rw [← map_star]
  exact (hφ (star (w.val j k)) _ ((hφ (w.val i l) _ (hu l k)).1)).2

variable [hS : IsClosed (S : Set R)]

theorem relativeTwoClass_conjugationPath (φ : A →⋆ₐ[ℂ] R) (hφc : Continuous φ)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (w : Analytic.Interval → unitary (Matrix (Fin 2) (Fin 2) A))
    (hw : Continuous w) (u : unitary (Matrix (Fin 2) (Fin 2) R))
    (hu : ∀ i j, ((u : Matrix (Fin 2) (Fin 2) R) - 1) i j ∈ S) :
    relativeTwoClass S (conjugatedTwoUnitary (mapTwoUnitary φ (w Analytic.start)) u)
      (conjugatedTwoUnitary_relative S φ hφ (w Analytic.start) u hu) =
    relativeTwoClass S (conjugatedTwoUnitary (mapTwoUnitary φ (w Analytic.finish)) u)
      (conjugatedTwoUnitary_relative S φ hφ (w Analytic.finish) u hu) := by
  apply relativeTwoClass_homotopy S
    (fun t => conjugatedTwoUnitary (mapTwoUnitary φ (w t)) u)
    (fun t => conjugatedTwoUnitary_relative S φ hφ (w t) u hu)
  have hc : Continuous (fun t => (mapTwoUnitary φ (w t)).val) :=
    (matrixTwoUnitalStarHom_continuous φ hφc).comp (continuous_subtype_val.comp hw)
  exact (hc.mul continuous_const).mul hc.star

end CoarseAssembly.OperatorKTheory

end

end OAI
