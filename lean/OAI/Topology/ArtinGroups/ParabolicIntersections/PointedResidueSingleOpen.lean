import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueSingleOpen
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedResidue_single_open {strict:Bool} (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (q:ℤ) (j:S) (hj:j∈P.val.1)
    (hcap:∀k:ℤ,q<k→pointedMultiplicity M f z k (.inl j)=0)
    (hbound:if strict then pointedMultiplicity M f z q (.inl j)<pointedCosetVector M f P q (.inl j)
      else pointedMultiplicity M f z q (.inl j)≤ pointedCosetVector M f P q (.inl j)) :
    Nonempty (PointedResidue M f strict P q) := by
  let T:=P.val.1\{j}
  have ht:T⊆P.val.1:=Set.sdiff_subset
  let R:=sourceCoset M T (source_spherical_mono M ht P.property.1) z
  have hr:R≤P := by
    rw [←sourceCoset_eq M P z hz]
    exact sourceCoset_le M ht z
  have hrlt:R<P := by
    apply lt_of_le_of_ne hr
    intro he
    have he':T=P.val.1:=congrArg (fun A:Deligne M=>A.val.1) he
    have hm:j∈T:=by rw [he'];exact hj
    exact hm.2 rfl
  have hrz:z∈R.val.2:=rightCoset_self M T z
  refine ⟨R,hrlt,?_⟩
  intro i hi hn
  have hei:i=j := by
    by_contra hne
    exact hn ⟨hi,hne⟩
  subst i
  have hvec(k:ℤ):pointedCosetVector M f R k (.inl j)=pointedMultiplicity M f z k (.inl j):=
    pointedCosetVector_open_at M f R z hrz _ (by
      rintro ⟨i,hi,he⟩;exact hn ((Sum.inl_injective he) ▸ hi)) k
  simpa only [hvec] using And.intro hcap hbound

end HarmonicArtin.ParabolicIntersections

end OAI
