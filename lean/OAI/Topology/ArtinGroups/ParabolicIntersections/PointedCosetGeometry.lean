import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.Coset
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Candidate

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_upper_outside {P R:Deligne M} (h:P≤R) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl:S→S⊕Unit) '' R.val.1) :
    pointedCosetVector M f R k i=pointedCosetVector M f P k i := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  rw [pointedCosetVector_eq M f R x (h.2 hx),pointedCosetVector_eq M f P x hx,
    pointedHarmonicAt_outside M f R.val.1 x k i hi,
    pointedHarmonicAt_outside M f P.val.1 x k i (fun he=>hi (Set.image_mono h.1 he))]

lemma pointedCosetVector_upper_harmonize {P R:Deligne M} (h:P≤R) (k:ℤ) :
    pointedCosetVector M f R k=harmonicExtension (framedCartan M)
      ((Sum.inl:S→S⊕Unit) '' R.val.1) (pointedCosetVector M f P k) :=
  harmonicExtension_unique _ _ (framed_spherical_posDef M R.val.1 R.property.1) _ _
    (pointedCosetVector_upper_outside M f h k) (pointedCosetVector_harmonic M f R k)

theorem pointedCosetVector_upper_change {P R:Deligne M} (h:P≤R) (k:ℤ) :
    (fun vertex : (Sum.inl:S→S⊕Unit) '' R.val.1 =>
      pointedCosetVector M f R k vertex-pointedCosetVector M f P k vertex) =
      -(((framedCartan M).submatrix Subtype.val Subtype.val :
          Matrix ((Sum.inl:S→S⊕Unit) '' R.val.1) ((Sum.inl:S→S⊕Unit) '' R.val.1) ℝ)⁻¹ *ᵥ
        fun vertex : (Sum.inl:S→S⊕Unit) '' R.val.1 =>
          (framedCartan M *ᵥ pointedCosetVector M f P k) vertex) := by
  convert harmonic_upper_change (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1)
    (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f P k) (pointedCosetVector M f R k)
    (pointedCosetVector_upper_outside M f h k) (pointedCosetVector_harmonic M f R k) using 1
  congr! (postTransparency := .reducible)

end HarmonicArtin.ParabolicIntersections

end OAI
