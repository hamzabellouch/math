import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedPresentation
import OAI.Topology.ArtinGroups.Complexes.HomDimension

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def classHomDimension (n v : ℤ) :
    FiniteHomotopyClass Q (K := K) → FiniteHomotopyClass Q (K := K) → ℕ :=
  Quotient.lift₂ (fun E F => homDimension Q E.complex F.complex n v)
    (by
      intro E E' F F' ⟨e⟩ ⟨f⟩
      exact e.homDimension_eq Q f n v)

lemma classPositiveTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (classPositiveTwist Q α E) (classPositiveTwist Q α F) =
      classHomDimension Q n v E F := by
  induction E using Quotient.inductionOn with | _ E =>
    induction F using Quotient.inductionOn with | _ F =>
      exact positiveTwist_homDimension Q hn E.complex F.complex α n v

lemma classNegativeTwist_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (α : V) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (classNegativeTwist Q α E) (classNegativeTwist Q α F) =
      classHomDimension Q n v E F := by
  induction E using Quotient.inductionOn with | _ E =>
    induction F using Quotient.inductionOn with | _ F =>
      exact negativeTwist_homDimension Q hn E.complex F.complex α n v

lemma unfoldedArtinAction_homDimension (hn : ∀ a, Q.source a ≠ Q.target a)
    (M : CoxeterMatrix V) (hM : UnfoldedPresentation Q M)
    (x : Artin M) (n v : ℤ) (E F : FiniteHomotopyClass Q (K := K)) :
    classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
      (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F := by
  let H : Subgroup (Artin M) := {
    carrier := {x | ∀ E F : FiniteHomotopyClass Q (K := K),
      classHomDimension Q n v (unfoldedArtinAction Q hn M hM x E)
        (unfoldedArtinAction Q hn M hM x F) = classHomDimension Q n v E F}
    one_mem' := by intro E F; simp only [map_one, Equiv.Perm.one_apply]
    mul_mem' := by
      intro x y hx hy E F
      rw [map_mul]
      change classHomDimension Q n v
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y E))
        (unfoldedArtinAction Q hn M hM x (unfoldedArtinAction Q hn M hM y F)) = _
      rw [hx, hy]
    inv_mem' := by
      intro x hx E F
      have h := hx (unfoldedArtinAction Q hn M hM x⁻¹ E)
        (unfoldedArtinAction Q hn M hM x⁻¹ F)
      rw [map_inv] at h ⊢
      simpa only [Equiv.Perm.inv_def, Equiv.apply_symm_apply] using h.symm }
  have h := PresentedGroup.generated_by (braidRelators M) H (by
    intro α E F
    change classHomDimension Q n v
      (unfoldedArtinAction Q hn M hM (generator M α) E)
      (unfoldedArtinAction Q hn M hM (generator M α) F) = _
    rw [unfoldedArtinAction_generator]
    exact classPositiveTwist_homDimension Q hn α n v E F) x
  exact h E F

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
