import Mathlib
import OAI.Topology.ArtinGroups.Functors.LeftHomIndex
import OAI.Topology.ArtinGroups.Diagrams.SupportedKernel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
attribute [local instance] Classical.propDecidable
variable {V B J K T : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
variable [Fintype T] [DecidableEq T]
    (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)

noncomputable def homSupportedCyclesEquiv
    (E : Zigzag.BasedComplex U (K := K) T) (u:V) (c:J) (b n : ℤ) :
    ScalarCycles.supportedKernel
      (leftHomMatrix Q step hstep N hN E.placement E.placement u c E.differential)
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) ≃ₗ[K]
    ScalarCycles.supportedKernel
      (rightHomMatrix Q step hstep N hN orient μ A E.placement E.placement u c E.differential)
      (fun x => (E.placement x.1).cochain=b ∧ Path.length x.2.2.val=n) := by
  apply ScalarCycles.conjugateEquiv _ _ _ _
    (homSwitch Q step hstep N hN orient μ A E.placement u c)
    (homUnswitch Q step hstep N hN orient μ A E.placement u c)
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := evaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homSwitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    by_cases hij : i=j
    · subst j
      have he := inverseEvaluationMatrix_length Q step hstep N hN orient μ A x y
        (by simpa only [homUnswitch,Matrix.blockDiagonal'_apply_eq] using h)
      simp only [he]
    · exact (h (Matrix.blockDiagonal'_apply_ne _ _ _ hij)).elim
  · exact homSwitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homUnswitch_inverse Q step hstep N hN orient μ A hμ δ hA hroot hPF _ _ _
  · exact homSwitch_naturality Q step hstep N hN orient μ A ho hμ δ hA hroot hPF _ _ _ _ _ E.entries

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
