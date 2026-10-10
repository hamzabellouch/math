import OAI.Topology.CoarseAssembly.IsometryDilation
import OAI.Topology.CoarseAssembly.RelativeTwoDiagonal

namespace OAI

/-! # Identity extension of a unitary along an isometry -/

noncomputable section

namespace CoarseAssembly.Analytic

variable {A : Type*} [CStarAlgebra A]

def isometryCornerHom (V : A) (hV : star V * V = 1) : A →⋆ₙₐ[ℂ] A where
  toFun a := V * a * star V
  map_zero' := by simp
  map_add' a b := by noncomm_ring
  map_mul' a b := by
    change V * (a * b) * star V = (V * a * star V) * (V * b * star V)
    calc
      _ = V * a * (star V * V) * b * star V := by rw [hV]; noncomm_ring
      _ = _ := by noncomm_ring
  map_smul' z a := by simp only [mul_smul_comm, smul_mul_assoc, MonoidHom.id_apply]
  map_star' a := by simp only [star_mul, star_star]; noncomm_ring

def isometryExtensionUnitary (V : A) (hV : star V * V = 1) (u : unitary A) :
    unitary A := by
  let Q := 1 - V * star V
  have hQQ := (isometry_complement_relations V hV).1
  have hQV := (isometry_complement_relations V hV).2.1
  have hVQ := (isometry_complement_relations V hV).2.2
  have hprod (a b : A) :
      (Q + V * a * star V) * (Q + V * b * star V) = Q + V * (a * b) * star V := by
    have ha : Q * (V * b * star V) = 0 := by
      rw [← mul_assoc, ← mul_assoc, hQV]; simp
    have hb : (V * a * star V) * Q = 0 := by
      rw [mul_assoc, hVQ]; simp
    rw [add_mul, mul_add, mul_add, hQQ, ha, hb, add_zero, zero_add]
    congr 1
    calc
      _ = V * a * (star V * V) * b * star V := by noncomm_ring
      _ = _ := by rw [hV]; noncomm_ring
  have hQ : star Q = Q := by dsimp [Q]; simp
  have huL : star (u : A) * (u : A) = 1 := Unitary.coe_star_mul_self u
  have huR : (u : A) * star (u : A) = 1 := by
    have h := Unitary.coe_mul_star_self u
    change (u : A) * star (u : A) = 1 at h
    exact h
  refine ⟨Q + V * (u : A) * star V, ?_, ?_⟩
  · change star (Q + V * (u : A) * star V) * (Q + V * (u : A) * star V) = 1
    rw [star_add, hQ, star_mul, star_mul, star_star]
    rw [← mul_assoc, hprod, huL]
    dsimp [Q]
    noncomm_ring
  · change (Q + V * (u : A) * star V) * star (Q + V * (u : A) * star V) = 1
    rw [star_add, hQ, star_mul, star_mul, star_star]
    rw [← mul_assoc, hprod, huR]
    dsimp [Q]
    noncomm_ring

@[simp] theorem isometryExtensionUnitary_val (V : A) (hV) (u : unitary A) :
    (isometryExtensionUnitary V hV u : A) = 1 + V * ((u : A) - 1) * star V := by
  change (1 - V * star V) + V * (u : A) * star V = _
  noncomm_ring

theorem isometryDilation_conjugates_unitary (V : A) (hV : star V * V = 1)
    (u : unitary A) :
    isometryDilation V *
      (OperatorKTheory.diagonalTwoUnitary 1 u : Matrix (Fin 2) (Fin 2) A) *
        star (isometryDilation V) =
      (OperatorKTheory.diagonalTwoUnitary (isometryExtensionUnitary V hV u) 1 :
        Matrix (Fin 2) (Fin 2) A) := by
  rw [(isometryDilation_selfAdjoint V).star_eq]
  have hleft : (OperatorKTheory.diagonalTwoUnitary 1 u : Matrix (Fin 2) (Fin 2) A) =
      !![1, 0; 0, (u : A)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [OperatorKTheory.diagonalTwoUnitary, Matrix.diagonal]
  rw [hleft, isometryDilation_conjugation V (u : A) hV]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [OperatorKTheory.diagonalTwoUnitary, Matrix.diagonal]

end CoarseAssembly.Analytic

end

end OAI
