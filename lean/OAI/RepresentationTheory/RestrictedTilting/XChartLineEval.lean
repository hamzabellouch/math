import OAI.RepresentationTheory.RestrictedTilting.Basic

namespace OAI

namespace FiberFunctorProof
universe u
variable (k : Type u) [Field k]

noncomputable def planeLineEval (a : k) : MvPolynomial (Fin 2) k →ₐ[k] k :=
  MvPolynomial.aeval (fun i => if i = 0 then a else 0)

lemma planeLineEval_X_isUnit (a : kˣ) :
    IsUnit (planeLineEval k a (MvPolynomial.X 0)) := by
  simp [planeLineEval]

noncomputable def chartLineEval (a : kˣ) : planeCoordinateChart k 0 →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom (MvPolynomial.X 0) (planeLineEval_X_isUnit k a)

lemma chartLineEval_algebraMap (a : kˣ) (P : MvPolynomial (Fin 2) k) :
    chartLineEval k a (algebraMap (MvPolynomial (Fin 2) k) (planeCoordinateChart k 0) P) =
      planeLineEval k a P := IsLocalization.Away.lift_eq _ (planeLineEval_X_isUnit k a) _

lemma chartLineEval_coordinate (a : kˣ) (i : Fin 2) :
    chartLineEval k a (planeChartCoordinate k 0 i) = if i = 0 then (a : k) else 0 := by
  rw [planeChartCoordinate, chartLineEval_algebraMap]
  simp [planeLineEval]

lemma chartLineEval_inverse (a : kˣ) :
    chartLineEval k a (planeChartInverse k 0) = (a : k)⁻¹ := by
  have hm : planeChartCoordinate k 0 0 * planeChartInverse k 0 = 1 :=
    IsLocalization.Away.mul_invSelf (S := planeCoordinateChart k 0) (MvPolynomial.X 0)
  have h := congrArg (chartLineEval k a) hm
  simp only [map_mul, map_one, chartLineEval_coordinate] at h
  exact mul_left_cancel₀ a.ne_zero (h.trans (mul_inv_cancel₀ a.ne_zero).symm)

lemma planeXPolynomialChart_line (a : kˣ) (P : MvPolynomial (Fin 2 × Fin 2) k) :
    chartLineEval k a (planeXPolynomialChart k P) = coordinateEvaluation k P (diagonalTorus k a) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [planeXPolynomialChart, coordinateEvaluation]
  | add P Q hp hq => simp only [map_add, Pi.add_apply, hp, hq]
  | mul_X P i hp =>
    simp only [map_mul, Pi.mul_apply, hp]
    congr 1
    rw [coordinateEvaluation_apply, MvPolynomial.eval_X]
    rcases i with ⟨i,j⟩
    fin_cases i <;> fin_cases j <;>
      simp [planeXPolynomialChart, diagonalTorus, chartLineEval_coordinate, chartLineEval_inverse] <;> rfl

lemma regularXChartValue_line (a : kˣ) (f : regularSL2Functions k) :
    chartLineEval k a (regularXChartValue k f) = f.val (diagonalTorus k a) := by
  rw [regularXChartValue, planeXPolynomialChart_line]
  exact congrFun f.property.choose_spec _

variable [Infinite k]
variable (ι : Type u) [Fintype ι] [DecidableEq ι]
variable (ρ : Representation k (Multiplicative k) (ι → k))

omit [Fintype ι] [DecidableEq ι] in
lemma associatedXChart_line (a : kˣ) (f : associatedSectionsSubmodule k ι ρ) :
    (fun i => chartLineEval k a (associatedXChart k ι ρ f i)) =
      regularVectorEvaluation k ι (diagonalTorus k a) f.val := by
  funext i
  exact regularXChartValue_line k a (f.val i)

omit [Infinite k] in
lemma unipotent_inverse (t : k) : (unipotent k t)⁻¹ = unipotent k (-t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← unipotent_add, add_neg_cancel, unipotent_zero]

omit [Infinite k] [Fintype ι] [DecidableEq ι] in
lemma associatedSections_line_unipotent (a : kˣ) (t : k)
    (f : associatedSectionsSubmodule k ι ρ) :
    regularVectorEvaluation k ι (diagonalTorus k a)
      (associatedSectionsRepresentation k ι ρ (unipotent k t) f).val =
    ρ (Multiplicative.ofAdd (t / (a : k)^2))
      (regularVectorEvaluation k ι (diagonalTorus k a) f.val) := by
  change regularVectorEvaluation k ι ((unipotent k t)⁻¹ * diagonalTorus k a) f.val = _
  rw [unipotent_inverse]
  have he := diagonal_unipotent k a (-t / (a : k)^2)
  rw [mul_div_cancel₀ _ (pow_ne_zero 2 a.ne_zero)] at he
  rw [← he, f.property]
  congr 2
  rw [neg_div, neg_neg]

end FiberFunctorProof

end OAI
