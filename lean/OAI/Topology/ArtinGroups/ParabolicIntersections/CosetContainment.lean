import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic
import OAI.Topology.ArtinGroups.Harmonic.Coset

namespace OAI

/-!
# Confining paths of parabolic cosets

This is the coset argument in Proposition 6.9 of paper 082-03. A path
whose types stay in one set cannot escape its standard coset. The proof
uses actual subgroup cosets, including upward as well as downward edges.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

/-- A smaller-type coset through a point of a larger-type coset is
contained in that larger coset. -/
theorem rightCoset_subset_of_point {T D : Set S} (hTD : T ⊆ D)
    {w z : Artin M} (hw : w ∈ rightCoset M D z) :
    rightCoset M T w ⊆ rightCoset M D z := by
  intro a ha
  change a * w⁻¹ ∈ artinParabolic M T at ha
  change w * z⁻¹ ∈ artinParabolic M D at hw
  change a * z⁻¹ ∈ artinParabolic M D
  have hh := (artinParabolic M D).mul_mem (standard_mono M hTD ha) hw
  simpa only [mul_assoc, inv_mul_cancel_left] using hh

/-- A represented parabolic coset can be recentered at each of its points. -/
theorem deligne_coset_eq_at_point (P : Deligne M) (w : Artin M) (hw : w ∈ P.val.2) :
    P.val.2 = rightCoset M P.val.1 w := by
  obtain ⟨z, hz⟩ := P.property.2
  rw [hz] at hw ⊢
  ext a
  change a * z⁻¹ ∈ artinParabolic M P.val.1 ↔ a * w⁻¹ ∈ artinParabolic M P.val.1
  have he : a * z⁻¹ = (a * w⁻¹) * (w * z⁻¹) := by group
  rw [he]
  exact (artinParabolic M P.val.1).mul_mem_cancel_right hw

/-- Upward comparability preserves containment when the larger type is
still contained in the specified standard type. -/
theorem deligne_upper_contained {P R : Deligne M} (hPR : P ≤ R)
    (D : Set S) (z : Artin M) (hR : R.val.1 ⊆ D)
    (hP : P.val.2 ⊆ rightCoset M D z) : R.val.2 ⊆ rightCoset M D z := by
  obtain ⟨w, hw⟩ : P.val.2.Nonempty := by
    obtain ⟨w, hw⟩ := P.property.2
    refine ⟨w, ?_⟩
    rw [hw]
    change w * w⁻¹ ∈ artinParabolic M P.val.1
    simp
  rw [deligne_coset_eq_at_point M R w (hPR.2 hw)]
  exact rightCoset_subset_of_point M hR (hP hw)

/-- Every coset on a finite comparability path with types in `D` stays
inside the starting `D`-coset. This is the path confinement used at a
minimum of the relative height. -/
theorem deligne_path_contained (D : Set S) (z : Artin M) {P R : Deligne M}
    (hP : P.val.2 ⊆ rightCoset M D z)
    (path : Relation.ReflTransGen
      (fun A B : Deligne M => A.val.1 ⊆ D ∧ B.val.1 ⊆ D ∧ (A ≤ B ∨ B ≤ A)) P R) :
    R.val.2 ⊆ rightCoset M D z := by
  induction path with
  | refl => exact hP
  | @tail A B path edge ih =>
    rcases edge.2.2 with hAB | hBA
    · exact deligne_upper_contained M hAB D z edge.2.1 ih
    · exact hBA.2.trans ih

/-- If a confined path reaches the translate of its starting coset by
`r`, then `r` belongs to the corresponding conjugate standard subgroup. -/
theorem conjugate_membership_of_coset_path (D : Set S) (z r : Artin M)
    {P R : Deligne M} (hP : z ∈ P.val.2) (hPT : P.val.1 ⊆ D)
    (hR : z * r ∈ R.val.2)
    (path : Relation.ReflTransGen
      (fun A B : Deligne M => A.val.1 ⊆ D ∧ B.val.1 ⊆ D ∧ (A ≤ B ∨ B ≤ A)) P R) :
    r ∈ conjugate z⁻¹ (artinParabolic M D) := by
  have hstart : P.val.2 ⊆ rightCoset M D z := by
    rw [deligne_coset_eq_at_point M P z hP]
    exact rightCoset_subset_of_point M hPT (by
      change z * z⁻¹ ∈ artinParabolic M D
      simp)
  have hend := deligne_path_contained M D z hstart path hR
  change (z * r) * z⁻¹ ∈ artinParabolic M D at hend
  simpa only [mem_conjugate, inv_inv] using hend

end HarmonicArtin.ParabolicIntersections

end OAI
