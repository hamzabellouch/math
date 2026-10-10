import Mathlib
import OAI.Topology.ArtinGroups.Functors.LayerIndexEquiv
import OAI.Topology.ArtinGroups.Complexes.LowerTruncation

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.StringFunctor
universe u
attribute [local instance] Classical.propDecidable
variable {V B J : Type u} {K : Type*} (Q : ReversibleQuiver V B)
  (step : B → Bool) (hstep : ∀ b, step (Q.reverse b) = step b)
  (N : J → J → Prop) (hN : ∀ ⦃first second⦄, N first second → N second first)
  [Fintype V] [Fintype B] [Fintype J]
  [DecidableEq V] [DecidableEq B] [DecidableEq J] [DecidableRel N] [Field K]
  (orient : B → Bool) (μ : J → K) (A : K)
local notation "U" => Q.stringQuiver step hstep N hN
open Zigzag.BasedComplex

variable (ho : ∀ b, orient (Q.reverse b) = !(orient b))
    (hμ : ∀ a, μ a ≠ 0) (δ : K)
    (hA : A ≠ 0) (hroot : A^2+A⁻¹^2+δ=0)
    (hPF : ∀ a, ∑ b ∈ GraphConnection.neighbors N a, μ b = δ * μ a)
local notation "C" => complex Q step hstep N hN orient μ A ho hμ δ hA hroot hPF
local notation "F" => classLabelFunctor Q step hstep N hN orient μ A ho hμ δ hA hroot hPF

variable {T : Type u} [Fintype T] [DecidableEq T]
def truncationIndexEquiv (E : Zigzag.BasedComplex U (K := K) T) (d : ℤ) :
    Index N (fun i : lowerLevelSet U E d => E.placement i) ≃
      lowerLevelSet U (C E) d where
  toFun x := ⟨⟨x.1.val,x.2⟩,x.1.property⟩
  invFun x := ⟨⟨x.1.1,x.2⟩,x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq T] in
lemma truncation_eq (E : Zigzag.BasedComplex U (K := K) T) (hE : E.IsMinimal U) (d : ℤ) :
    (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d).reindex U
      (truncationIndexEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E d) = C (lowerTruncation U E hE d) := by
  apply ext_placement_differential U
  · rfl
  · rfl

noncomputable def truncationComparison (E : Zigzag.BasedComplex U (K := K) T)
    (hE : E.IsMinimal U) (d : ℤ) :
    ChainIsomorphism U
      (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
      (C (lowerTruncation U E hE d)) := by
  have e := reindexChainIsomorphism U
    (lowerTruncation U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE) d)
    (truncationIndexEquiv Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E d)
  rw [truncation_eq] at e
  exact e

lemma classLabel_truncation (d : ℤ) (x : FiniteHomotopyClass U (K := K)) :
    classLowerTruncation U d (F x) = F (classLowerTruncation U d x) := by
  let E := (minimalClassModel U x).complex
  have hE := minimalClassModel_minimal U x
  have hx : classOfComplex U E = x := minimalClassModel_class U x
  conv_lhs => rw [← hx,classLabel_complex]
  rw [classLowerTruncation_minimal U (C E) (complex_minimal Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE)]
  change _ = classOfComplex U (C (lowerTruncation U E hE d))
  exact classOfComplex_eq U
    ((truncationComparison Q step hstep N hN orient μ A ho hμ δ hA hroot hPF E hE d).toHomotopyEquivalence U)

end HarmonicArtin.ReversibleQuiver.StringFunctor

end OAI
