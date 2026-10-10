import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.LiftedDeck
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHomSpherical
import OAI.Topology.ArtinGroups.Harmonic.TopBlockMatchingKey

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma restriction_parabolic_map (T : Set S) (R : Set T) :
    (coxeterParabolic (restrictedMatrix M T) R).map (restrictionHom M T) =
      coxeterParabolic M (Subtype.val '' R) := by
  rw [coxeterParabolic, MonoidHom.map_closure, Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨(s:S), ⟨s,hs,rfl⟩, restrictionHom_simple M T s |>.symm⟩
  · rintro ⟨s, ⟨t,ht,rfl⟩, rfl⟩
    exact ⟨t,ht,restrictionHom_simple M T t⟩

omit [Fintype S] [LinearOrder S] in
lemma restriction_wordCoxeter (T : Set S) (w : List T) :
    restrictionHom M T (wordCoxeter (restrictedMatrix M T) w) =
      wordCoxeter M (w.map Subtype.val) :=
  restriction_wordProd M T w

noncomputable def restrictedLiftedCell (T : Set S) (hT : IsSpherical M T)
    (a : LiftedCell (restrictedMatrix M T)) : SphericalLiftedFiber M T :=
  ⟨(restrictedArtinHom M T a.1, ⟨Subtype.val '' a.2.val,
      spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩; exact s.property) hT⟩),
    (by rintro _ ⟨s,_,rfl⟩; exact s.property),
    (by rw [←restrictedArtinHom_range M T]; exact ⟨a.1,rfl⟩)⟩

lemma restrictedLiftedCell_injective (T : Set S) (hT : IsSpherical M T) :
    Function.Injective (restrictedLiftedCell M T hT) := by
  intro a b h
  apply Prod.ext
  · apply restrictedArtinHom_spherical_injective M T hT
    exact congrArg (fun c : SphericalLiftedFiber M T => c.val.1) h
  · apply Subtype.ext
    have he : Subtype.val '' a.2.val = Subtype.val '' b.2.val :=
      congrArg (fun c : SphericalLiftedFiber M T => c.val.2.val) h
    exact Set.image_injective.mpr Subtype.val_injective he

omit [LinearOrder S] in
lemma restrictedLiftedCell_surjective (T : Set S) (hT : IsSpherical M T) :
    Function.Surjective (restrictedLiftedCell M T hT) := by
  intro a
  have ha : a.val.1 ∈ (restrictedArtinHom M T).range := by
    simpa only [restrictedArtinHom_range] using a.property.2
  obtain ⟨g,hg⟩ := ha
  let R : Set T := Subtype.val ⁻¹' a.val.2.val
  let : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  have hR : IsSpherical (restrictedMatrix M T) R :=
    show Finite (coxeterParabolic (restrictedMatrix M T) R) from inferInstance
  refine ⟨(g,⟨R,hR⟩),?_⟩
  apply Subtype.ext
  apply Prod.ext hg
  apply Subtype.ext
  change Subtype.val '' R = a.val.2.val
  ext s
  constructor
  · rintro ⟨t,ht,rfl⟩; exact ht
  · intro hs
    exact ⟨⟨s,a.property.1 hs⟩,hs,rfl⟩

lemma restrictedLiftedCell_face_iff (T : Set S) (hT : IsSpherical M T)
    (a b : LiftedCell (restrictedMatrix M T)) :
    LiftedFace M (restrictedLiftedCell M T hT a).val
      (restrictedLiftedCell M T hT b).val ↔ LiftedFace (restrictedMatrix M T) a b := by
  constructor
  · rintro ⟨hAB,w,hw,hr,hm,he⟩
    have hwt : ∀ s ∈ w, s ∈ T := by
      intro s hs
      obtain ⟨t,_,ht⟩ := hw s hs
      exact ht ▸ t.property
    let v : List T := w.attach.map fun s => ⟨s.val,hwt s.val s.property⟩
    have hv : v.map Subtype.val = w := by
      simp [v,List.map_map,Function.comp_def]
    have hr' : (restrictedMatrix M T).toCoxeterSystem.length
        (wordCoxeter (restrictedMatrix M T) v) = v.length := by
      rw [←restriction_length M T, restriction_wordCoxeter, hv]
      simpa [v] using hr
    refine ⟨?_,v,?_,hr',?_,?_⟩
    · intro s hs
      obtain ⟨t,ht,he⟩ := hAB ⟨s,hs,rfl⟩
      exact (Subtype.val_injective he) ▸ ht
    · intro s hs
      have hsw : (s:S) ∈ w := hv ▸ List.mem_map_of_mem hs
      obtain ⟨t,ht,he⟩ := hw s hsw
      exact (Subtype.val_injective he) ▸ ht
    · intro q
      have hq : restrictionHom M T q.val ∈ coxeterParabolic M (Subtype.val '' a.2.val) := by
        rw [←restriction_parabolic_map M T a.2.val]
        exact ⟨q.val,q.property,rfl⟩
      have hh := hm ⟨restrictionHom M T q.val,hq⟩
      rw [←hv,←restriction_wordCoxeter,←map_mul,restriction_length,restriction_length] at hh
      exact hh
    · apply restrictedArtinHom_spherical_injective M T hT
      rw [map_mul,restrictedArtinHom_word,hv]
      exact he
  · rintro ⟨hAB,v,hv,hr,hm,he⟩
    refine ⟨Set.image_mono hAB,v.map Subtype.val,?_,?_,?_,?_⟩
    · intro s hs
      obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hs
      exact ⟨t,hv t ht,rfl⟩
    · rw [←restriction_wordCoxeter,restriction_length,List.length_map]
      exact hr
    · intro q
      have hq := q.property
      change q.val ∈ coxeterParabolic M (Subtype.val '' a.2.val) at hq
      rw [←restriction_parabolic_map M T a.2.val] at hq
      obtain ⟨r,hrq,heq⟩ := hq
      have hh := hm ⟨r,hrq⟩
      rw [←restriction_length M T,←restriction_length M T] at hh
      rw [map_mul,restriction_wordCoxeter,heq] at hh
      exact hh
    · change restrictedArtinHom M T a.1 = restrictedArtinHom M T b.1 * _
      rw [he,map_mul,restrictedArtinHom_word]

noncomputable def restrictedLiftedFiberIso (T : Set S) (hT : IsSpherical M T) :
    LiftedCell (restrictedMatrix M T) ≃o SphericalLiftedFiber M T where
  toEquiv := Equiv.ofBijective (restrictedLiftedCell M T hT)
    ⟨restrictedLiftedCell_injective M T hT,restrictedLiftedCell_surjective M T hT⟩
  map_rel_iff' := by
    intro a b
    change (restrictedLiftedCell M T hT a).val ≤ (restrictedLiftedCell M T hT b).val ↔ a ≤ b
    rw [lifted_le_iff_face,lifted_le_iff_face]
    exact restrictedLiftedCell_face_iff M T hT a b

end HarmonicArtin

end OAI
