import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.PairForms

namespace OAI

/-! Nondegenerate Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem pairForm_orthonormal {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ)
    (hS : B.IsSymm) (hB : B.Nondegenerate) :
    ∃ L : Matrix (Fin d) (Fin d) ℂ,
      (fun j k => ∑ p : Fin d × Fin d, B p.1 p.2 * L p.1 j * L p.2 k) = (1 : Matrix (Fin d) (Fin d) ℂ) := by
  let A : Matrix (Fin d) (Fin d) ℂ := 1
  have hA : A.IsSymm := by simp [A]
  have hAn : A.Nondegenerate := by
    rw [Matrix.nondegenerate_iff_det_ne_zero]
    simp [A]
  have hBs : QuadraticMap.associated B.toBilin'.toQuadraticMap = B.toBilin' :=
    QuadraticMap.associated_left_inverse ℂ
      (fun x y => (Matrix.isSymm_toBilin'_iff_isSymm.mpr hS).eq x y)
  have hAs : QuadraticMap.associated A.toBilin'.toQuadraticMap = A.toBilin' :=
    QuadraticMap.associated_left_inverse ℂ
      (fun x y => (Matrix.isSymm_toBilin'_iff_isSymm.mpr hA).eq x y)
  obtain ⟨f⟩ := QuadraticForm.equivalent_of_isAlgClosed
    A.toBilin'.toQuadraticMap B.toBilin'.toQuadraticMap
    (by rw [hAs]; exact hAn.toBilin'.1) (by rw [hBs]; exact hB.toBilin'.1)
  have hf (x y : Fin d → ℂ) : B.toBilin' (f x) (f y) = A.toBilin' x y := by
    calc
      B.toBilin' (f x) (f y) =
          QuadraticMap.associated B.toBilin'.toQuadraticMap (f x) (f y) :=
        congrArg (fun K : LinearMap.BilinForm ℂ (Fin d → ℂ) => K (f x) (f y)) hBs.symm
      _ = QuadraticMap.associated A.toBilin'.toQuadraticMap x y := by
        simp only [QuadraticMap.associated, QuadraticMap.associated_apply,
          ← map_add f, f.map_app]
      _ = A.toBilin' x y := congrArg (fun K : LinearMap.BilinForm ℂ (Fin d → ℂ) => K x y) hAs
  refine ⟨fun i j => f (Pi.single j 1) i, ?_⟩
  ext j k
  have hh := hf (Pi.single j 1) (Pi.single k 1)
  rw [Matrix.toBilin'_single, Matrix.toBilin'_apply] at hh
  rw [Fintype.sum_prod_type]
  change (∑ i, ∑ l, B i l * f (Pi.single j 1) i * f (Pi.single k 1) l) = A j k
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem even_rows_nondegenerate_pair_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (B : Matrix (Fin d) (Fin d) ℂ)
    (hS : B.IsSymm) (hB : B.Nondegenerate)
    (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (pairFormTensor e B)).toRepresentation, F ≠ 0 := by
  obtain ⟨L,hL⟩ := pairForm_orthonormal B hS hB
  apply even_rows_pairFormTensor_support e B L 1 one_ne_zero
    (by simpa only [one_smul] using hL) μ t he hd

end Saxl
end
end

end OAI
