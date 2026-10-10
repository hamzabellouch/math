import OAI.Topology.ArtinGroups.Harmonic.ArtinAction
import OAI.Topology.ArtinGroups.Harmonic.FusionQuiverSimpleEdge
import OAI.Topology.ArtinGroups.Complexes.ScalarExactNotZero

namespace OAI

/-! The existing categorical action with an arbitrary original color as frame. -/

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "d" => coxeterFusionEdge M
local notation "hd" => coxeterFusionEdge_symm M
local notation "diag" => coxeterFusionEdge_diag M
local notation "Q" => fusionQuiver m d hd

abbrev PointedLabel := FusionLabel m
abbrev PointedClass := FiniteHomotopyClass Q (K := ℂ)
abbrev PointedFamilySpace := PointedLabel M → PointedClass M

noncomputable def pointedAction : Artin M →* Equiv.Perm (PointedClass M) :=
  sourceArtinAction M (K := ℂ)

noncomputable def pointedInitial (f : S) : PointedFamilySpace M :=
  fun L => initialClass Q (.inl f, L)

noncomputable def pointedFamily (f : S) (x : Artin M) : PointedFamilySpace M :=
  fun L => pointedAction M x (pointedInitial M f L)

@[simp] theorem pointedAction_generator (s : S) :
    pointedAction M (generator M s) = fusionPacketPerm m d hd diag (.inl s) :=
  sourceArtinAction_generator M s

private theorem pointed_orthogonal (s f : S) (hsf : M s f = 2)
    (L H : PointedLabel M) : OrthogonalVertices Q (.inl s, L) (.inl f, H) := by
  have hne : s ≠ f := by
    intro he
    subst f
    rw [M.diagonal] at hsf
    norm_num at hsf
  apply fusionQuiver_orthogonal
  · intro he
    exact hne (Sum.inl.inj (congrArg Prod.fst he))
  · simp only [coxeterFusionEdge, hne, ↓reduceDIte, hsf,
      OfNat.ofNat_ne_zero, FusionEdge.multiplicity]
    split <;> rfl

/-- A color nonadjacent to the frame fixes each initial projective. -/
theorem pointed_generator_fixes_initial (s f : S) (hsf : M s f = 2)
    (L : PointedLabel M) :
    pointedAction M (generator M s) (pointedInitial M f L) = pointedInitial M f L := by
  rw [pointedAction_generator, fusionPacketPerm, ← classPacketPerm_toList]
  have hlist (l : List (PointedLabel M)) :
      (l.map (fun H => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
        (.inl s, H))).prod (pointedInitial M f L) = pointedInitial M f L := by
    induction l with
    | nil => rfl
    | cons H l ih =>
      change classPositiveTwist Q (.inl s, H)
        ((l.map (fun J => classTwistPerm Q (fusionQuiver_no_loops m d hd diag)
          (.inl s, J))).prod (pointedInitial M f L)) = _
      rw [ih]
      exact classPositiveTwist_initial_orthogonal Q (pointed_orthogonal M s f hsf H L)
  exact hlist _

/-- The whole standard subgroup of nonadjacent colors fixes the frame. -/
theorem pointed_standard_fixes_initial (X : Set S) (f : S)
    (hX : ∀ s ∈ X, M s f = 2) (g : Artin M) (hg : g ∈ artinParabolic M X)
    (L : PointedLabel M) :
    pointedAction M g (pointedInitial M f L) = pointedInitial M f L := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨s, hs, rfl⟩ := hg
    exact pointed_generator_fixes_initial M s f (hX s hs) L
  | one => simp only [map_one, Equiv.Perm.one_apply]
  | mul g h hg hh ihg ihh =>
    simp only [map_mul, Equiv.Perm.mul_apply, ihh, ihg]
  | inv g hg ih =>
    rw [map_inv]
    apply (pointedAction M g).injective
    change (pointedAction M g) ((pointedAction M g).symm (pointedInitial M f L)) = _
    rw [Equiv.apply_symm_apply, ih]

noncomputable instance pointedFamilyMulAction : MulAction (Artin M) (PointedFamilySpace M) where
  smul g F := fun L => pointedAction M g (F L)
  one_smul F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_one (pointedAction M))
  mul_smul g h F := by
    funext L
    exact congrArg (fun p => p (F L)) (map_mul (pointedAction M) g h)

end HarmonicArtin.ParabolicIntersections

end OAI
