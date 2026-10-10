import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetGeometry
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveComponent
import OAI.Topology.ArtinGroups.Harmonic.Coset
import OAI.Topology.ArtinGroups.Harmonic.CosetProfile

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_eq_of_upper_rows {P R:Deligne M} (h:P≤R) (k:ℤ)
    (hr:∀i∈R.val.1,i∉P.val.1→(framedCartan M *ᵥ pointedCosetVector M f P k) (.inl i)=0) :
    pointedCosetVector M f R k=pointedCosetVector M f P k := by
  rw [pointedCosetVector_upper_harmonize M f h k]
  symm
  apply harmonicExtension_unique (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1) (framed_spherical_posDef M R.val.1 R.property.1)
    (pointedCosetVector M f P k) (pointedCosetVector M f P k)
  · intro _ _; rfl
  · rintro ⟨_,⟨i,hi,rfl⟩⟩
    by_cases ht:i∈P.val.1
    · exact pointedCosetVector_harmonic M f P k ⟨.inl i,⟨i,ht,rfl⟩⟩
    · exact hr i hi ht

end HarmonicArtin.ParabolicIntersections

end OAI
