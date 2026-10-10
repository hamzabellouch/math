import Mathlib
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel

namespace OAI

namespace HarmonicArtin.ScalarCycles
noncomputable def congrEquiv {K I : Type*} [Field K] [Fintype I]
    (L R : Matrix I I K) (P T : I → Prop) (hL:L=R) (hP:P=T) :
    supportedKernel L P ≃ₗ[K] supportedKernel R T := by
  subst R; subst T
  exact LinearEquiv.refl K _
end HarmonicArtin.ScalarCycles

end OAI
