import Mathlib

namespace OAI

/-! A finite-dimensional spectral bound used to choose positive mesh weights. -/
namespace HarmonicArtin.ParabolicIntersections
open Unitary
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type} [Fintype V]

lemma mesh_spectral_upper {A : Matrix V V ℝ} (hA : A.IsHermitian) (d : ℝ)
    (hbound : ∀ i, hA.eigenvalues i≤d) :
    (d • (1 : Matrix V V ℝ)-A).PosSemidef := by
  let U := hA.eigenvectorUnitary
  let D := Matrix.diagonal hA.eigenvalues
  have hspec : A=conjStarAlgAut ℝ _ U D := by
    simpa [U,D] using hA.spectral_theorem
  have hdiag : d • (1 : Matrix V V ℝ)-D=Matrix.diagonal (fun i => d-hA.eigenvalues i) := by
    ext i j
    by_cases hij : i=j
    · subst j; simp [D]
    · simp [D,hij]
  have hd : (d • (1 : Matrix V V ℝ)-D).PosSemidef := by
    rw [hdiag,Matrix.posSemidef_diagonal_iff]
    intro i
    exact sub_nonneg.mpr (hbound i)
  have he : d • (1 : Matrix V V ℝ)-A=
      conjStarAlgAut ℝ _ U (d • (1 : Matrix V V ℝ)-D) := by
    rw [map_sub,map_smul,map_one,←hspec]
  rw [he,conjStarAlgAut_apply]
  exact hd.mul_mul_conjTranspose_same _

end HarmonicArtin.ParabolicIntersections

end OAI
