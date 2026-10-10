import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeDiagram
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedFamily

namespace OAI

/-!
# The relative categorical family of paper 082-03

The family consists of actual bounded-projective homotopy classes in the
extended diagram. Its initial color is the new relative color `f`; the
auxiliary universal color is the one already adjoined by the fusion model.
-/

namespace HarmonicArtin.ParabolicIntersections

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (X : Set S)
local instance : LinearOrder (S ⊕ Unit) := Sum.Lex.linearOrder
local notation "N" => relativeMatrix M X

abbrev RelativeLabel := PointedLabel N
abbrev RelativeClass := PointedClass N
abbrev RelativeFamilySpace := PointedFamilySpace N

noncomputable def relativeAction : Artin M →* Equiv.Perm (RelativeClass M X) :=
  (pointedAction N).comp (relativeArtinHom M X)

noncomputable def relativeInitial : RelativeFamilySpace M X := pointedInitial N (.inr ())

noncomputable def relativeFamily (x : Artin M) : RelativeFamilySpace M X :=
  fun L => relativeAction M X x (relativeInitial M X L)

@[simp] theorem relativeFamily_one : relativeFamily M X 1 = relativeInitial M X := by
  funext L
  simp [relativeFamily]

theorem relativeFamily_mul (g x : Artin M) (L : RelativeLabel M X) :
    relativeFamily M X (g * x) L = relativeAction M X g (relativeFamily M X x L) := by
  simp only [relativeFamily, map_mul, Equiv.Perm.mul_apply]

/-- The easy inclusion in Proposition 8.3. -/
theorem relative_generator_fixes_initial (s : S) (hs : s ∈ X) (L : RelativeLabel M X) :
    relativeAction M X (generator M s) (relativeInitial M X L) = relativeInitial M X L := by
  change pointedAction N (relativeArtinHom M X (generator M s))
    (pointedInitial N (.inr ()) L) = _
  rw [relativeArtinHom_generator]
  exact pointed_generator_fixes_initial N (.inl s) (.inr ()) (by simp [hs]) L

/-- Verified containment of the standard subgroup in the actual initial stabilizer. -/
theorem standard_fixes_relativeInitial (g : Artin M) (hg : g ∈ artinParabolic M X)
    (L : RelativeLabel M X) :
    relativeAction M X g (relativeInitial M X L) = relativeInitial M X L := by
  apply pointed_standard_fixes_initial N (Sum.inl '' X) (.inr ())
  · rintro _ ⟨s, hs, rfl⟩
    simp [hs]
  · rw [← relativeArtinHom_parabolic]
    exact ⟨g, hg, rfl⟩

noncomputable instance relativeFamilyMulAction : MulAction (Artin M) (RelativeFamilySpace M X) where
  smul g F := fun L => relativeAction M X g (F L)
  one_smul F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_one (relativeAction M X))
  mul_smul g h F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_mul (relativeAction M X) g h)

@[simp] theorem relativeFamily_eq_smul (x : Artin M) :
    relativeFamily M X x = x • relativeInitial M X := rfl

theorem standard_le_relative_stabilizer :
    artinParabolic M X ≤ MulAction.stabilizer (Artin M) (relativeInitial M X) := by
  intro g hg
  apply funext
  exact standard_fixes_relativeInitial M X g hg

end HarmonicArtin.ParabolicIntersections

end OAI
