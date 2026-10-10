import Mathlib
import OAI.Topology.ArtinGroups.Complexes.MinimalModel
import OAI.Topology.ArtinGroups.Quivers.CoefficientMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma frameModel_negative_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (n v : ℤ) (h : n + v < 0) :
    homDimension Q (frameModel Q (K := K) hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v = 0 := by
  rw [frameModel, minimalClassModel_homDimension]
  apply unfoldedFrame_self_support Q hn M hM x α n v
  by_cases hn : n = 0
  · exact Or.inr ⟨by omega, by omega⟩
  · exact Or.inl hn

lemma frameModel_negative_coefficient_injection (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M) (x : Artin M) (α : V)
    (n v : ℤ) (h : n + v < 0)
    {f g : Matrix (frameModel Q (K := K) hn M hM x α).Index
      (frameModel Q hn M hM x α).Index (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v)
    (hg : g ∈ homSpace Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n v)
    (h₀ : CoefficientMatrix Q f) (h₁ : LinearMatrix Q g)
    (he : homDifferential Q (frameModel Q hn M hM x α).complex
      (frameModel Q hn M hM x α).complex n f =
      homDifferential Q (frameModel Q hn M hM x α).complex
        (frameModel Q hn M hM x α).complex n g) : f = 0 := by
  exact coefficient_eq_zero_of_same_differential Q _ _
    (frameModel_minimal Q hn M hM x α) (frameModel_minimal Q hn M hM x α) n v
    (frameModel_negative_homDimension Q hn M hM x α n v h) hf hg h₀ h₁ he

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
