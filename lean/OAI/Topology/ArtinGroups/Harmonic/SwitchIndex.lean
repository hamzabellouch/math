import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Crossing

namespace OAI

namespace HarmonicArtin.GraphConnection

variable {J K : Type*} [Fintype J] [DecidableEq J] [Field K]
  (N : J → J → Prop) [DecidableRel N]

abbrev SwitchIndex (b c : J) := {a // N b a ∧ N c a}

noncomputable def switchMatrix (μ : J → K) (A : K) (b c : J) :
    Matrix (SwitchIndex N b c) (SwitchIndex N b c) K :=
  fun a d => crossing μ A a b c d

noncomputable def unswitchMatrix (μ : J → K) (A : K) (b c : J) :
    Matrix (SwitchIndex N b c) (SwitchIndex N b c) K :=
  fun d a => crossing μ A b a d c * (μ a / μ c)

lemma switch_unswitch (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a) (b c : J) :
    switchMatrix N μ A b c * unswitchMatrix N μ A b c = 1 := by
  classical
  ext a a'
  simp only [Matrix.mul_apply,switchMatrix,unswitchMatrix,← mul_assoc,← Finset.sum_mul]
  have hs : (∑ d : SwitchIndex N b c,
      crossing μ A a b c d * crossing μ A b a' d c) =
      if a.val=a'.val then μ c / μ a else 0 := by
    rw [← crossing_square N μ hμ δ A hA hroot hPF a a' b c
      a.property.1 a'.property.1 a.property.2 a'.property.2]
    exact (Finset.sum_subtype (neighbors N b ∩ neighbors N c)
      (fun d => show d ∈ neighbors N b ∩ neighbors N c ↔ N b d ∧ N c d by simp)
      (fun d => crossing μ A a b c d * crossing μ A b a' d c)).symm
  rw [hs]
  by_cases he : a=a'
  · subst a'
    simp only [↓reduceIte,Matrix.one_apply_eq]
    field_simp [hμ]
  · rw [ite_eq_right (fun equality => he (Subtype.ext equality)), zero_mul,
      Matrix.one_apply_ne he]

lemma unswitch_switch (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a) (b c : J) :
    unswitchMatrix N μ A b c * switchMatrix N μ A b c = 1 := by
  exact mul_eq_one_comm.mp (switch_unswitch N μ hμ δ A hA hroot hPF b c)

noncomputable def switchEquiv (μ : J → K) (hμ : ∀ a, μ a ≠ 0) (δ A : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ neighbors N a, μ b = δ * μ a) (b c : J) :
    (SwitchIndex N b c → K) ≃ₗ[K] (SwitchIndex N b c → K) where
  toFun := fun x => Matrix.vecMul x (switchMatrix N μ A b c)
  invFun := fun x => Matrix.vecMul x (unswitchMatrix N μ A b c)
  left_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,switch_unswitch N μ hμ δ A hA hroot hPF,Matrix.vecMul_one]
  right_inv x := by
    dsimp only
    rw [Matrix.vecMul_vecMul,unswitch_switch N μ hμ δ A hA hroot hPF,Matrix.vecMul_one]
  map_add' x y := Matrix.add_vecMul _ x y
  map_smul' a x := Matrix.smul_vecMul a x _

end HarmonicArtin.GraphConnection

end OAI
