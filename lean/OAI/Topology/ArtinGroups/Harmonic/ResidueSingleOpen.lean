import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceResidue_single_open {strict:Bool} (P:Deligne M) (z:Artin M) (hz:z∈P.val.2)
    (q:ℤ) (j:S) (hj:j∈P.val.1)
    (hcap:∀k:ℤ,q<k→sourceMultiplicity M z k (.inl j)=0)
    (hbound:if strict then sourceMultiplicity M z q (.inl j)<sourceCosetVector M P q (.inl j)
      else sourceMultiplicity M z q (.inl j)≤ sourceCosetVector M P q (.inl j)) :
    Nonempty (SourceResidue M strict P q) := by
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
  have hvec(k:ℤ):sourceCosetVector M R k (.inl j)=sourceMultiplicity M z k (.inl j):=
    sourceCosetVector_open_at M R z hrz _ (by
      rintro ⟨i,hi,he⟩;exact hn ((Sum.inl_injective he) ▸ hi)) k
  simpa only [hvec] using And.intro hcap hbound

end HarmonicArtin

end OAI
