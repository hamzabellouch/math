import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace Matrix
open scoped _root_.Matrix
variable {R T X : Type*} [Semiring R] [Fintype T] [DecidableEq T]
  {B C : T → Type*} [∀ i, Fintype (B i)]
lemma mul_blockDiagonal'_entry (M : Matrix X (Sigma B) R)
    (S : (i:T) → Matrix (B i) (C i) R) (x:X) (j:T) (y:C j) :
    (M * _root_.Matrix.blockDiagonal' S) x ⟨j,y⟩ = ∑ z, M x ⟨j,z⟩ * S j z y := by
  rw [_root_.Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single j]
  · simp only [_root_.Matrix.blockDiagonal'_apply_eq]
  · intro i hi hij
    apply Finset.sum_eq_zero
    intro z hz
    rw [_root_.Matrix.blockDiagonal'_apply_ne _ _ _ hij,mul_zero]
  · simp
lemma blockDiagonal'_mul_entry (S : (i:T) → Matrix (C i) (B i) R)
    (M : Matrix (Sigma B) X R) (i:T) (x:C i) (y:X) :
    (_root_.Matrix.blockDiagonal' S * M) ⟨i,x⟩ y = ∑ z, S i x z * M ⟨i,z⟩ y := by
  rw [_root_.Matrix.mul_apply,Fintype.sum_sigma,Finset.sum_eq_single i]
  · simp only [_root_.Matrix.blockDiagonal'_apply_eq]
  · intro j hj hji
    apply Finset.sum_eq_zero
    intro z hz
    rw [_root_.Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hji),zero_mul]
  · simp
end Matrix

end OAI
