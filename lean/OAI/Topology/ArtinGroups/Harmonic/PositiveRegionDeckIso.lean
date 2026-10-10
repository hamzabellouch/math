import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveRegion
import OAI.Topology.ArtinGroups.Realizations.RestrictedLiftedCell
import OAI.Topology.ArtinGroups.Realizations.FiniteWeightsCompact

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def positiveRegionDeckIso (g : Artin M) :
    PositiveRegion M 1 ≃o PositiveRegion M g where
  toFun a := ⟨liftedDeck M g a.val, by
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p, by change g*a.val.1 = _; simpa using congrArg (g * ·) hp⟩⟩
  invFun a := ⟨liftedDeck M g⁻¹ a.val, by
    obtain ⟨p,hp⟩ := a.property
    exact ⟨p, by change g⁻¹*a.val.1 = _; simp [hp]⟩⟩
  left_inv a := by apply Subtype.ext; ext <;> simp [liftedDeck]
  right_inv a := by apply Subtype.ext; ext <;> simp [liftedDeck]
  map_rel_iff' := by intro a b; exact (liftedDeck M g).map_rel_iff

def SphericalPositiveRegion (T : Set S) (hT : IsSpherical M T)
    (g : Artin (restrictedMatrix M T)) : Set (SphericalLiftedFiber M T) :=
  restrictedLiftedCell M T hT '' PositiveRegion (restrictedMatrix M T) g

noncomputable def sphericalPositiveRegionIso (T : Set S) (hT : IsSpherical M T)
    (g : Artin (restrictedMatrix M T)) :
    PositiveRegion (restrictedMatrix M T) g ≃o SphericalPositiveRegion M T hT g where
  toFun a := ⟨restrictedLiftedCell M T hT a.val, a.val,a.property,rfl⟩
  invFun a := ⟨(restrictedLiftedFiberIso M T hT).symm a.val, by
    obtain ⟨b,hb,he⟩ := a.property
    change (restrictedLiftedFiberIso M T hT) b = a.val at he
    rw [←he,(restrictedLiftedFiberIso M T hT).symm_apply_apply]
    exact hb⟩
  left_inv a := Subtype.ext ((restrictedLiftedFiberIso M T hT).symm_apply_apply a.val)
  right_inv a := Subtype.ext ((restrictedLiftedFiberIso M T hT).apply_symm_apply a.val)
  map_rel_iff' := by intro a b; exact (restrictedLiftedFiberIso M T hT).map_rel_iff

lemma sphericalPositiveRegion_down (T : Set S) (hT : IsSpherical M T)
    (g : Artin (restrictedMatrix M T)) {a b : SphericalLiftedFiber M T}
    (hab : a ≤ b) (hb : b ∈ SphericalPositiveRegion M T hT g) :
    a ∈ SphericalPositiveRegion M T hT g := by
  obtain ⟨b',hb',rfl⟩ := hb
  let a' := (restrictedLiftedFiberIso M T hT).symm a
  have ha' : restrictedLiftedCell M T hT a' = a :=
    (restrictedLiftedFiberIso M T hT).apply_symm_apply a
  refine ⟨a',positiveRegion_face_closed _ g ?_ hb',ha'⟩
  apply (restrictedLiftedFiberIso M T hT).le_iff_le.mp
  change restrictedLiftedCell M T hT a' ≤ restrictedLiftedCell M T hT b'
  rw [ha']; exact hab

lemma sphericalPositiveRegion_contains_finite (T : Set S) (hT : IsSpherical M T)
    (A : Set (SphericalLiftedFiber M T)) (hA : A.Finite) :
    ∃ g, A ⊆ SphericalPositiveRegion M T hT g := by
  let e := restrictedLiftedFiberIso M T hT
  let F := hA.toFinset.image e.symm
  obtain ⟨g,hg⟩ := spherical_positiveRegion_contains_finset M T hT F
  refine ⟨g,?_⟩
  intro a ha
  refine ⟨e.symm a,hg _ (Finset.mem_image.mpr ⟨a,hA.mem_toFinset.mpr ha,rfl⟩),?_⟩
  exact e.apply_symm_apply a

theorem spherical_compact_map_factors {X : Type u} [TopologicalSpace X] [CompactSpace X]
    (T : Set S) (hT : IsSpherical M T) (f : C(X,OrderWeights (SphericalLiftedFiber M T))) :
    ∃ g, ∃ F : C(X,OrderWeights (SphericalPositiveRegion M T hT g)),
      (weightMapContinuous (weightInclusion (SphericalPositiveRegion M T hT g))).comp F = f :=
  compact_map_factors_cover (SphericalPositiveRegion M T hT)
    (sphericalPositiveRegion_contains_finite M T hT) f

end HarmonicArtin

end OAI
