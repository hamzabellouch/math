import OAI.Topology.ArtinGroups.ParabolicIntersections.Basic

namespace OAI

/-!
# The relative diagram in §2.1 of paper 082-03

Adjoin the color `f`, with label 2 to the chosen standard type `X` and
label 3 to its complement. The existing fusion construction subsequently
adjoins the universal auxiliary color `o`. The map on Artin presentations
is constructed directly; no parabolic embedding theorem is assumed here.
-/

namespace HarmonicArtin.ParabolicIntersections

attribute [local instance] Classical.propDecidable

variable {S : Type*} (M : CoxeterMatrix S) (X : Set S)

noncomputable def relativeMatrix : CoxeterMatrix (S ⊕ Unit) := by
  classical
  exact {
    M := fun a b => match a, b with
      | .inl s, .inl t => M s t
      | .inl s, .inr _ => if s ∈ X then 2 else 3
      | .inr _, .inl s => if s ∈ X then 2 else 3
      | .inr _, .inr _ => 1
    isSymm := by
      apply Matrix.ext
      intro a b
      cases a <;> cases b <;> dsimp [Matrix.transpose]
      exact M.symmetric _ _
    diagonal := by intro a; cases a <;> simp
    off_diagonal := by
      intro a b h
      cases a with
      | inl s =>
        cases b with
        | inl t => exact M.off_diagonal s t (fun e => h (congrArg Sum.inl e))
        | inr u => dsimp; split_ifs <;> norm_num
      | inr u =>
        cases b with
        | inl t => dsimp; split_ifs <;> norm_num
        | inr v => exact (h (by cases u; cases v; rfl)).elim }

@[simp] theorem relativeMatrix_original (s t : S) :
    relativeMatrix M X (.inl s) (.inl t) = M s t := rfl

@[simp] theorem relativeMatrix_frame (s : S) :
    relativeMatrix M X (.inl s) (.inr ()) = if s ∈ X then 2 else 3 := by
  classical
  rfl

private theorem alternating_lift_inclusion (s t : S) (n : ℕ) :
    FreeGroup.lift (fun s => generator (relativeMatrix M X) (.inl s))
      (alternating s t n) =
    FreeGroup.lift (generator (relativeMatrix M X))
      (alternating (.inl s) (.inl t) n) := by
  induction n generalizing s t with
  | zero => simp [alternating]
  | succ n ih => simp only [alternating, map_mul, FreeGroup.lift_apply_of, ih]

private theorem relative_relators : ∀ r ∈ braidRelators M,
    FreeGroup.lift (fun s => generator (relativeMatrix M X) (.inl s)) r = 1 := by
  rintro r ⟨⟨s, t⟩, rfl⟩
  rw [map_mul, map_inv, alternating_lift_inclusion, alternating_lift_inclusion]
  change FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X)))
    (alternating (.inl s) (.inl t) (M s t)) *
    (FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X)))
      (alternating (.inl t) (.inl s) (M s t)))⁻¹ = 1
  rw [← map_inv, ← map_mul]
  have hl : FreeGroup.lift (PresentedGroup.of (rels := braidRelators (relativeMatrix M X))) =
      PresentedGroup.mk (braidRelators (relativeMatrix M X)) := by
    apply FreeGroup.ext_hom
    intro s
    rfl
  rw [hl]
  exact PresentedGroup.one_of_mem ⟨(.inl s, .inl t), rfl⟩

/-- The canonical homomorphism into the Artin group of the relative diagram. -/
noncomputable def relativeArtinHom : Artin M →* Artin (relativeMatrix M X) :=
  PresentedGroup.toGroup (relative_relators M X)

@[simp] theorem relativeArtinHom_generator (s : S) :
    relativeArtinHom M X (generator M s) =
      generator (relativeMatrix M X) (.inl s) :=
  PresentedGroup.toGroup.of _

/-- Standard parabolics map onto the corresponding standard parabolics
of the extended diagram. Injectivity is not needed for this identity. -/
theorem relativeArtinHom_parabolic (Y : Set S) :
    (artinParabolic M Y).map (relativeArtinHom M X) =
      artinParabolic (relativeMatrix M X) (Sum.inl '' Y) := by
  simp only [artinParabolic, MonoidHom.map_closure, Set.image_image,
    relativeArtinHom_generator]

end HarmonicArtin.ParabolicIntersections

end OAI
