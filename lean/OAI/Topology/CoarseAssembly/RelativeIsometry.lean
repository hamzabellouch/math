import OAI.Topology.CoarseAssembly.RelativeTwoConjugation
import OAI.Topology.CoarseAssembly.IsometryUnitary

namespace OAI

/-! # Isometric stabilization preserves the actual relative K₁ class -/

noncomputable section

namespace CoarseAssembly.OperatorKTheory

open Analytic

variable {A R : Type*} [CStarAlgebra A] [CStarAlgebra R]
variable (S : NonUnitalStarSubalgebra ℂ R) [hS : IsClosed (S : Set R)]

omit hS in
theorem isometryExtensionUnitary_relative (φ : A →⋆ₐ[ℂ] R)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (V : A) (hV : star V * V = 1) (u : unitary A)
    (hu : φ (u : A) - 1 ∈ S) :
    φ (isometryExtensionUnitary V hV u : A) - 1 ∈ S := by
  rw [isometryExtensionUnitary_val, map_add, map_one, add_sub_cancel_left,
    map_mul, map_mul, map_sub, map_one]
  exact (hφ (star V) _ ((hφ V _ hu).1)).2

/-- The dilation homotopy proves equality in K₁, not just equality in a quotient of operators. -/
theorem relativeClass_isometry (φ : A →⋆ₐ[ℂ] R) (hφc : Continuous φ)
    (hφ : ∀ a b, b ∈ S → φ a * b ∈ S ∧ b * φ a ∈ S)
    (V : A) (hV : star V * V = 1) (u : unitary A)
    (hu : φ (u : A) - 1 ∈ S) :
    relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) u) hu =
      relativeClass S (Unitary.map (StarMonoidHom.ofClass φ) (isometryExtensionUnitary V hV u))
        (isometryExtensionUnitary_relative S φ hφ V hV u hu) := by
  let W := isometryDilationPath V hV
  let v := Unitary.map (StarMonoidHom.ofClass φ) u
  let e := Unitary.map (StarMonoidHom.ofClass φ) (isometryExtensionUnitary V hV u)
  have hv : (v : R) - 1 ∈ S := hu
  have he : (e : R) - 1 ∈ S := isometryExtensionUnitary_relative S φ hφ V hV u hu
  have h0 : conjugatedTwoUnitary (mapTwoUnitary φ (W start)) (diagonalTwoUnitary 1 v) =
      diagonalTwoUnitary 1 v := by
    change conjugatedTwoUnitary (mapTwoUnitary φ (isometryDilationPath V hV start)) _ = _
    rw [isometryDilationPath_start, mapTwoUnitary_one]
    simp [conjugatedTwoUnitary]
  have hd : conjugatedTwoUnitary (W finish) (diagonalTwoUnitary 1 u) =
      diagonalTwoUnitary (isometryExtensionUnitary V hV u) 1 := by
    apply Subtype.ext
    change (W finish).val * (diagonalTwoUnitary 1 u).val * star (W finish).val = _
    dsimp only [W]
    rw [isometryDilationPath_finish]
    exact isometryDilation_conjugates_unitary V hV u
  have h1 : conjugatedTwoUnitary (mapTwoUnitary φ (W finish)) (diagonalTwoUnitary 1 v) =
      diagonalTwoUnitary e 1 := by
    have hm := congrArg (mapTwoUnitary φ) hd
    rw [mapTwoUnitary_conjugate, mapTwoUnitary_diagonal, mapTwoUnitary_diagonal] at hm
    simpa only [map_one] using hm
  have hz : ((1 : unitary R) : R) - 1 ∈ S := by simp
  have h := relativeTwoClass_conjugationPath S φ hφc hφ W
    (isometryDilationPath_continuous V hV) (diagonalTwoUnitary 1 v)
    (diagonalTwoUnitary_relative S 1 v hz hv)
  simp only [h0, h1] at h
  have hleft := relativeTwoClass_diagonal S 1 v hz hv
  have hright := relativeTwoClass_diagonal S e 1 he hz
  rw [hleft, hright, relativeClass_one S hz, zero_add, add_zero] at h
  exact h

end CoarseAssembly.OperatorKTheory

end

end OAI
