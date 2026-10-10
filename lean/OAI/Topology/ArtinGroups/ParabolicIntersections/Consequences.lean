import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic

namespace OAI

/-!
# Consequences of the inside-parabolic intersection theorem

These are the deductions in the introduction of paper 082-03. The premise
`InsideIntersectionProperty` is a **new result of that paper**, not a
published input and not an established instance. These deductions alone
do not constitute a formalization of its main intersection theorem.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type*} (M : CoxeterMatrix S)

/-- The inside-parabolic conclusion of §8. Its proof, for arbitrary
Artin matrices, must come from the relative stabilizer argument. -/
def InsideIntersectionProperty : Prop :=
  ∀ (X Y : Set S) (g : Artin M), ∃ (Z : Set S) (c : Artin M),
    Z ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      artinParabolic M Y ⊓ conjugate g (artinParabolic M X) =
        conjugate c (artinParabolic M Z)

theorem inside_conjugate (h : InsideIntersectionProperty M)
    (Y : Set S) (g : Artin M) {P : Subgroup (Artin M)} (hP : IsParabolic M P) :
    ∃ (Z : Set S) (c : Artin M), Z ⊆ Y ∧ c ∈ artinParabolic M Y ∧
      conjugate g (artinParabolic M Y) ⊓ P =
        conjugate (g * c) (artinParabolic M Z) := by
  obtain ⟨X, a, rfl⟩ := hP
  obtain ⟨Z, c, hZ, hc, he⟩ := h X Y (g⁻¹ * a)
  refine ⟨Z, c, hZ, hc, ?_⟩
  have hh := congrArg (conjugate g) he
  rw [conjugate_inf, ← conjugate_mul, ← conjugate_mul] at hh
  simpa only [mul_inv_cancel_left] using hh

/-- The exact pairwise statement of Theorem 1.1, deduced from its stronger
inside-parabolic form. The hypothesis still needs to be proved. -/
theorem pairwise_of_inside (h : InsideIntersectionProperty M)
    (X Y : Set S) (g a : Artin M) :
    ∃ (Z : Set S) (k : Artin M),
      conjugate g (artinParabolic M X) ⊓ conjugate a (artinParabolic M Y) =
        conjugate k (artinParabolic M Z) := by
  obtain ⟨Z, c, _, _, he⟩ := inside_conjugate M h X g
    (show IsParabolic M (conjugate a (artinParabolic M Y)) from ⟨Y, a, rfl⟩)
  exact ⟨Z, g * c, he⟩

theorem isParabolic_inf (h : InsideIntersectionProperty M)
    {P Q : Subgroup (Artin M)} (hP : IsParabolic M P) (hQ : IsParabolic M Q) :
    IsParabolic M (P ⊓ Q) := by
  obtain ⟨X, g, rfl⟩ := hP
  obtain ⟨Y, a, rfl⟩ := hQ
  exact pairwise_of_inside M h X Y g a

private theorem insert_intersection {G : Type*} [Group G]
    [DecidableEq (Subgroup G)]
    (P : Subgroup G) (F : Finset (Subgroup G)) :
    sInf (↑(insert P F) : Set (Subgroup G)) = P ⊓ sInf (↑F : Set (Subgroup G)) := by
  classical
  rw [Finset.coe_insert, sInf_insert]

variable [Finite S]

/-- The descent uses the displayed type, so no separate theorem asserting
that parabolic rank is invariant under conjugation is required. -/
private theorem finite_subfamily_aux (h : InsideIntersectionProperty M)
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    ∀ n : ℕ, ∀ (X : Set S), X.ncard = n → ∀ g : Artin M,
      ∃ F₀ : Finset (Subgroup (Artin M)),
        (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ n ∧
        conjugate g (artinParabolic M X) ⊓ sInf F =
          conjugate g (artinParabolic M X) ⊓ sInf (↑F₀ : Set (Subgroup (Artin M))) ∧
        IsParabolic M (conjugate g (artinParabolic M X) ⊓ sInf F) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro X hX g
    let Q := conjugate g (artinParabolic M X)
    by_cases hQ : Q ≤ sInf F
    · refine ⟨∅, by simp, by simp, ?_, ?_⟩
      · simp only [Finset.coe_empty, sInf_empty, inf_top_eq]
        exact inf_eq_left.mpr hQ
      · change IsParabolic M (Q ⊓ sInf F)
        rw [inf_eq_left.mpr hQ]
        exact ⟨X, g, rfl⟩
    · obtain ⟨P, hPF, hQP⟩ : ∃ P ∈ F, ¬ Q ≤ P := by
        by_contra hn
        push Not at hn
        exact hQ (le_sInf hn)
      obtain ⟨Z, c, hZX, hc, he⟩ := inside_conjugate M h X g (hF P hPF)
      have hne : Z ≠ X := by
        intro hz
        rw [hz, conjugate_mul, conjugate_eq_self hc] at he
        exact hQP (inf_eq_left.mp he)
      have hlt : Z.ncard < n := by
        rw [← hX]
        exact Set.ncard_lt_ncard (ssubset_of_subset_of_ne hZX hne)
      obtain ⟨F₀, hF₀, hcard, hEq, hPar⟩ := ih Z.ncard hlt Z rfl (g * c)
      refine ⟨insert P F₀, ?_, ?_, ?_, ?_⟩
      · intro A hA
        rcases Finset.mem_insert.mp hA with rfl | hA
        · exact hPF
        · exact hF₀ hA
      · have hi := Finset.card_insert_le P F₀
        omega
      · rw [insert_intersection]
        calc
          Q ⊓ sInf F = (Q ⊓ P) ⊓ sInf F := by
            rw [inf_assoc, inf_eq_right.mpr (sInf_le hPF)]
          _ = conjugate (g * c) (artinParabolic M Z) ⊓ sInf F := by rw [he]
          _ = conjugate (g * c) (artinParabolic M Z) ⊓ sInf (↑F₀ : Set _) := hEq
          _ = Q ⊓ (P ⊓ sInf (↑F₀ : Set _)) := by rw [← he, inf_assoc]
      · have heF : Q ⊓ sInf F =
            conjugate (g * c) (artinParabolic M Z) ⊓ sInf F := by
          rw [← he, inf_assoc, inf_eq_right.mpr (sInf_le hPF)]
        rw [heF]
        exact hPar

/-- The full subfamily bound in Corollary 1.2, including the empty family.
This is conditional on the new inside-intersection theorem, explicitly. -/
theorem arbitrary_intersections_of_inside (h : InsideIntersectionProperty M)
    (F : Set (Subgroup (Artin M))) (hF : ∀ P ∈ F, IsParabolic M P) :
    (∃ F₀ : Finset (Subgroup (Artin M)),
      (↑F₀ : Set (Subgroup (Artin M))) ⊆ F ∧ F₀.card ≤ Nat.card S ∧
        sInf F = sInf (↑F₀ : Set (Subgroup (Artin M)))) ∧
    IsParabolic M (sInf F) := by
  obtain ⟨F₀, hF₀, hcard, he, hp⟩ :=
    finite_subfamily_aux M h F hF (Set.univ : Set S).ncard Set.univ rfl 1
  simp only [standard_univ, conjugate_top, top_inf_eq, Set.ncard_univ] at he hp hcard
  exact ⟨⟨F₀, hF₀, hcard, he⟩, hp⟩

/-- The unique smallest parabolic containing an arbitrary subset, rather
than merely a smallest parabolic containing a finite set. -/
theorem parabolic_closure_of_inside (h : InsideIntersectionProperty M)
    (E : Set (Artin M)) :
    ∃! P : Subgroup (Artin M), IsParabolic M P ∧ E ⊆ P ∧
      ∀ Q : Subgroup (Artin M), IsParabolic M Q → E ⊆ Q → P ≤ Q := by
  let F := {P : Subgroup (Artin M) | IsParabolic M P ∧ E ⊆ P}
  have hp := (arbitrary_intersections_of_inside M h F (fun _ hP => hP.1)).2
  have he : E ⊆ (sInf F : Subgroup (Artin M)) := by
    intro a ha
    exact Subgroup.mem_sInf.mpr (fun P hP => hP.2 ha)
  refine ⟨sInf F, ⟨hp, he, ?_⟩, ?_⟩
  · intro Q hQ hEQ
    exact sInf_le ⟨hQ, hEQ⟩
  · intro Q hQ
    exact le_antisymm (hQ.2.2 _ hp he) (sInf_le ⟨hQ.1, hQ.2.1⟩)

end HarmonicArtin.ParabolicIntersections

end OAI
