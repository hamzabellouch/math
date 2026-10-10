import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength
import OAI.Topology.ArtinGroups.Harmonic.PositiveLiftSimple

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M:CoxeterMatrix S) (J:Set S)

lemma restrictedArtin_relators : ∀ r∈braidRelators (restrictedMatrix M J),
    FreeGroup.lift (fun s:J=>generator M s) r=1 := by
  have ha:∀ i j:J,∀n,
      FreeGroup.lift (fun s:J=>generator M s) (alternating i j n)=
        wordArtin M (altList (i:S) (j:S) n) := by
    intro i j n
    induction n generalizing i j with
    | zero => simp [alternating,wordArtin,altList]
    | succ n ih => simp only [alternating,map_mul,FreeGroup.lift_apply_of,
        wordArtin,altList_succ,List.map_cons,List.prod_cons,ih]
  rintro r ⟨⟨i,j⟩,rfl⟩
  rw [map_mul,map_inv,ha,ha]
  exact mul_inv_eq_one.mpr (wordArtin_braid M i j)

noncomputable def restrictedArtinHom : Artin (restrictedMatrix M J) →* Artin M :=
  PresentedGroup.toGroup (restrictedArtin_relators M J)

@[simp] lemma restrictedArtinHom_generator (s:J) :
    restrictedArtinHom M J (generator (restrictedMatrix M J) s)=generator M s :=
  PresentedGroup.toGroup.of _

lemma restrictedArtinHom_word (w:List J) :
    restrictedArtinHom M J (wordArtin (restrictedMatrix M J) w)=wordArtin M (w.map Subtype.val) := by
  induction w with
  | nil => simp [wordArtin]
  | cons s w ih =>
    change restrictedArtinHom M J (generator (restrictedMatrix M J) s * wordArtin _ w)=
      generator M s * wordArtin M (w.map Subtype.val)
    rw [map_mul,restrictedArtinHom_generator,ih]

lemma restrictedArtinHom_range : (restrictedArtinHom M J).range=artinParabolic M J := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    have hg:g∈Subgroup.closure (Set.range (generator (restrictedMatrix M J))) := by
      have hh:Subgroup.closure (Set.range (generator (restrictedMatrix M J)))=⊤:=
        PresentedGroup.closure_range_of (braidRelators (restrictedMatrix M J))
      rw [hh]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨s,rfl⟩:=hx
      rw [restrictedArtinHom_generator]
      exact Subgroup.subset_closure ⟨s,s.property,rfl⟩
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y hx hy hix hiy => rw [map_mul]; exact Subgroup.mul_mem _ hix hiy
    | inv x hx hix => rw [map_inv]; exact Subgroup.inv_mem _ hix
  · apply (Subgroup.closure_le _).2
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨generator (restrictedMatrix M J) ⟨s,hs⟩,restrictedArtinHom_generator M J _⟩

theorem sphericalParabolic_positive_fraction [Fintype S] (hJ:IsSpherical M J)
    {g:Artin M} (hg:g∈artinParabolic M J) :
    ∃ u v:List S,(∀s∈u,s∈J) ∧ (∀s∈v,s∈J) ∧ g=wordArtin M u*(wordArtin M v)⁻¹ := by
  rw [← restrictedArtinHom_range M J] at hg
  obtain ⟨a,rfl⟩:=hg
  let : Finite (restrictedMatrix M J).Group := restricted_finite M J hJ
  obtain ⟨u,v,h⟩:=finiteArtin_positive_fraction (restrictedMatrix M J) a
  refine ⟨u.map Subtype.val,v.map Subtype.val,?_,?_,?_⟩
  · intro s hs; obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hs; exact t.property
  · intro s hs; obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hs; exact t.property
  rw [h,map_mul,map_inv,restrictedArtinHom_word,restrictedArtinHom_word]

end HarmonicArtin

end OAI
