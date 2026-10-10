import OAI.Topology.CoarseAssembly.RelativeTwoConjugation
import OAI.Topology.CoarseAssembly.PartialIsometryDilation

namespace OAI

/-! # Relative K₁ classes agree under equivalence of their supported corners -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A R : Type*} [CStarAlgebra A] [CStarAlgebra R]

theorem partialIsometryDilation_conjugates_unitary
    (T : A) (hT : T * star T * T = T) (u v : unitary A)
    (hleft : (star T * T) * ((u : A) - 1) = (u : A) - 1)
    (hright : ((u : A) - 1) * (star T * T) = (u : A) - 1)
    (hv : (v : A) = 1 + T * ((u : A) - 1) * star T) :
    partialIsometryDilation T * (diagonalTwoUnitary u 1).val *
      star (partialIsometryDilation T) = (diagonalTwoUnitary 1 v).val := by
  rw [(partialIsometryDilation_selfAdjoint T).star_eq]
  have hd : (diagonalTwoUnitary u 1).val = !![1 + ((u : A) - 1), 0; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagonalTwoUnitary, Matrix.diagonal]
  rw [hd, partialIsometryDilation_conjugation T ((u : A) - 1) hT hleft hright]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonalTwoUnitary, Matrix.diagonal, hv]

variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

/-- A partial isometry between supported defects gives equality in the original K₁. -/
theorem relativeClass_partialIsometry (φ : A →⋆ₐ[ℂ] R) (hφc : Continuous φ)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (T : A) (hT : T * star T * T = T) (u v : unitary A)
    (hleft : (star T * T) * ((u : A) - 1) = (u : A) - 1)
    (hright : ((u : A) - 1) * (star T * T) = (u : A) - 1)
    (hv : (v : A) = 1 + T * ((u : A) - 1) * star T)
    (huS : φ (u : A) - 1 ∈ S) (hvS : φ (v : A) - 1 ∈ S) :
    relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) u) huS =
      relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) v) hvS := by
  let W := partialIsometryDilationPath T hT
  let u' := Unitary.map (StarMonoidHom.ofClass φ) u
  let v' := Unitary.map (StarMonoidHom.ofClass φ) v
  have h0 : conjugatedTwoUnitary (mapTwoUnitary φ (W start)) (diagonalTwoUnitary u' 1) =
      diagonalTwoUnitary u' 1 := by
    change conjugatedTwoUnitary (mapTwoUnitary φ (partialIsometryDilationPath T hT start)) _ = _
    rw [partialIsometryDilationPath_start, mapTwoUnitary_one]
    simp [conjugatedTwoUnitary]
  have hd : conjugatedTwoUnitary (W finish) (diagonalTwoUnitary u 1) =
      diagonalTwoUnitary 1 v := by
    apply Subtype.ext
    change (W finish).val * (diagonalTwoUnitary u 1).val * star (W finish).val = _
    dsimp only [W]
    rw [partialIsometryDilationPath_finish]
    exact partialIsometryDilation_conjugates_unitary T hT u v hleft hright hv
  have h1 : conjugatedTwoUnitary (mapTwoUnitary φ (W finish)) (diagonalTwoUnitary u' 1) =
      diagonalTwoUnitary 1 v' := by
    have hm := congrArg (mapTwoUnitary φ) hd
    rw [mapTwoUnitary_conjugate, mapTwoUnitary_diagonal, mapTwoUnitary_diagonal] at hm
    simpa only [map_one] using hm
  have hz : ((1 : unitary R) : R) - 1 ∈ S := by simp
  have h := relativeTwoClass_conjugationPath S φ hφc hφ W
    (partialIsometryDilationPath_continuous T hT) (diagonalTwoUnitary u' 1)
    (diagonalTwoUnitary_relative S u' 1 huS hz)
  simp only [h0, h1] at h
  rw [relativeTwoClass_diagonal S u' 1 huS hz,
    relativeTwoClass_diagonal S 1 v' hz hvS, relativeClass_one S hz, add_zero, zero_add] at h
  exact h

end CoarseAssembly.OperatorKTheory

end

end OAI
