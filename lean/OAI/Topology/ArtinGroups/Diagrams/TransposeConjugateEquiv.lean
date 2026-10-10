import Mathlib
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel

namespace OAI

namespace HarmonicArtin.ScalarCycles
variable {K I J : Type*} [Field K] [Fintype I] [Fintype J]

noncomputable def transposeConjugateEquiv [DecidableEq I] [DecidableEq J]
    (L : Matrix I I K) (R : Matrix J J K)
    (P : I → Prop) (T : J → Prop) (S : Matrix I J K) (D : Matrix J I K)
    (hS : ∀ i j, S i j ≠ 0 → (P i ↔ T j))
    (hD : ∀ j i, D j i ≠ 0 → (T j ↔ P i))
    (hSD : S*D=1) (hDS : D*S=1) (hc : R*D=D*L) :
    supportedKernel L.transpose P ≃ₗ[K] supportedKernel R.transpose T := by
  apply conjugateEquiv _ _ _ _ D.transpose S.transpose
  · intro i j h; exact (hD j i h).symm
  · intro j i h; exact (hS i j h).symm
  · rw [← Matrix.transpose_mul,hSD,Matrix.transpose_one]
  · rw [← Matrix.transpose_mul,hDS,Matrix.transpose_one]
  · have h := congrArg Matrix.transpose hc
    simpa only [Matrix.transpose_mul] using h.symm

end HarmonicArtin.ScalarCycles

end OAI
