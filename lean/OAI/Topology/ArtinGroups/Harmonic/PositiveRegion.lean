import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellDeligne
import OAI.Topology.ArtinGroups.Cancellation.SphericalPositiveCancelMonoid

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} (M:CoxeterMatrix S)

def PositiveRegion (g:Artin M) : Set (LiftedCell M) :=
  {a | ∃p:PositiveArtin M,a.1=g*positiveToArtin M p}

lemma positiveRegion_face_closed (g:Artin M) {a b:LiftedCell M}
    (h:a≤b) (hb:b∈PositiveRegion M g) : a∈PositiveRegion M g := by
  obtain ⟨p,hp⟩:=hb
  obtain ⟨_,w,_,_,_,he⟩:=(lifted_le_iff_face M _ _).mp h
  refine ⟨p*wordPositive M w,?_⟩
  rw [map_mul,positiveToArtin_word,←mul_assoc,←hp,he]

lemma positiveRegion_subset_of_factor (g k:Artin M) (p:PositiveArtin M)
    (h:g=k*positiveToArtin M p) : PositiveRegion M g⊆PositiveRegion M k := by
  rintro a ⟨q,hq⟩
  exact ⟨p*q,by rw [hq,h,map_mul,mul_assoc]⟩

section Spherical
variable {A:Type} [Fintype A] [LinearOrder A] (N:CoxeterMatrix A)
  (T:Set A) (hT:IsSpherical N T)

include hT in
omit [LinearOrder A] in
theorem spherical_positiveRegions_directed
    (g h:Artin (restrictedMatrix N T)) :
    ∃k:Artin (restrictedMatrix N T),
      PositiveRegion (restrictedMatrix N T) g⊆PositiveRegion (restrictedMatrix N T) k ∧
      PositiveRegion (restrictedMatrix N T) h⊆PositiveRegion (restrictedMatrix N T) k := by
  let f:=positiveToArtin (restrictedMatrix N T)
  obtain ⟨c,d,hcd⟩:=(spherical_positive_monoid_fractions N T hT (g⁻¹*h)).2
  let k:=g*(f c)⁻¹
  have hg:g=k*f c:=by dsimp [k];group
  have hh:h=k*f d:=by
    calc h=g*(g⁻¹*h):=by group
         _=g*((f c)⁻¹*f d):=by rw [hcd]
         _=k*f d:=by dsimp [k];group
  exact ⟨k,positiveRegion_subset_of_factor _ g k c hg,
    positiveRegion_subset_of_factor _ h k d hh⟩

include hT in
omit [LinearOrder A] in
theorem spherical_positiveRegion_contains_finset
    (F:Finset (LiftedCell (restrictedMatrix N T))) :
    ∃g:Artin (restrictedMatrix N T),∀a∈F,a∈PositiveRegion (restrictedMatrix N T) g := by
  induction F using Finset.induction_on with
  | empty=>exact ⟨1,by simp⟩
  | @insert a F _ ih=>
    obtain ⟨g,hg⟩:=ih
    obtain ⟨k,hak,hgk⟩:=spherical_positiveRegions_directed N T hT a.1 g
    refine ⟨k,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl|hb
    · exact hak ⟨1,by simp⟩
    · exact hgk (hg b hb)

end Spherical
end HarmonicArtin

end OAI
