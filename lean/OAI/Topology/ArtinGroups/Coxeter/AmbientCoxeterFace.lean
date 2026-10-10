import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.TopBlockMatchingKey
import OAI.Topology.ArtinGroups.Coxeter.ArtinCoxeter

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

omit [Fintype S] [DecidableEq S] in
lemma restriction_parabolic_image (T : Set S) (R : Set T) :
    (coxeterParabolic (restrictedMatrix M T) R).map (restrictionHom M T) =
      coxeterParabolic M (Subtype.val '' R) := by
  rw [coxeterParabolic,MonoidHom.map_closure,Set.image_image]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s,hs,rfl⟩
    exact ⟨(s:S),⟨s,hs,rfl⟩,(restrictionHom_simple M T s).symm⟩
  · rintro ⟨s,⟨t,ht,rfl⟩,rfl⟩
    exact ⟨t,ht,restrictionHom_simple M T t⟩

omit [Fintype S] [DecidableEq S] in
lemma restriction_word (T : Set S) (w : List T) :
    restrictionHom M T (wordCoxeter (restrictedMatrix M T) w) = wordCoxeter M (w.map Subtype.val) :=
  restriction_wordProd M T w

noncomputable def ambientCoxeterFace (T : Set S) (c : CoxeterCellFace (restrictedMatrix M T)) :
    CoxeterCellFace M :=
  ⟨(restrictionHom M T c.val.1,Subtype.val '' c.val.2),by
    intro v hv
    rw [←restriction_parabolic_image M T c.val.2] at hv
    obtain ⟨q,hq,rfl⟩ := hv
    rw [←map_mul,restriction_length,restriction_length]
    exact c.property q hq⟩

lemma ambientCoxeterFace_le_iff (T : Set S) (c d : CoxeterCellFace (restrictedMatrix M T)) :
    ambientCoxeterFace M T c ≤ ambientCoxeterFace M T d ↔ c ≤ d := by
  rw [CoxeterCellFace.le_iff,CoxeterCellFace.le_iff]
  change (Subtype.val '' c.val.2 ⊆ Subtype.val '' d.val.2 ∧
    (restrictionHom M T d.val.1)⁻¹*restrictionHom M T c.val.1 ∈
      coxeterParabolic M (Subtype.val '' d.val.2)) ↔ _
  rw [←map_inv,←map_mul,←restriction_parabolic_image]
  have hs : Subtype.val '' c.val.2 ⊆ Subtype.val '' d.val.2 ↔ c.val.2 ⊆ d.val.2 :=
    Set.image_subset_image_iff Subtype.val_injective
  rw [hs]
  constructor
  · rintro ⟨h,⟨w,hw,he⟩⟩
    refine ⟨h,?_⟩
    change d.val.1⁻¹*c.val.1 ∈ coxeterParabolic (restrictedMatrix M T) d.val.2
    rw [←restrictionHom_injective M T he]
    exact hw
  · rintro ⟨h,hw⟩
    exact ⟨h,⟨_,hw,rfl⟩⟩

noncomputable def sourceFaceLifted (T : SphericalType M)
    (c : CoxeterCellFace (restrictedMatrix M T.val)) : LiftedCell M :=
  (positiveLift M (restrictionHom M T.val c.val.1),⟨Subtype.val '' c.val.2,
    spherical_type_mono M (by rintro _ ⟨s,_,rfl⟩;exact s.property) T.property⟩)

lemma sourceFaceLifted_le_iff (T : SphericalType M)
    (c d : CoxeterCellFace (restrictedMatrix M T.val)) :
    sourceFaceLifted M T c ≤ sourceFaceLifted M T d ↔ c ≤ d := by
  rw [←ambientCoxeterFace_le_iff M T.val c d,CoxeterCellFace.le_iff,lifted_le_iff_face]
  constructor
  · rintro ⟨ht,w,hw,_,_,he⟩
    refine ⟨ht,?_⟩
    have hp := congrArg (artinCoxeter M) he
    simp only [sourceFaceLifted,map_mul,artinCoxeter_word,artinCoxeter_positiveLift] at hp
    change (restrictionHom M T.val d.val.1)⁻¹*restrictionHom M T.val c.val.1 ∈
      coxeterParabolic M (Subtype.val '' d.val.2)
    rw [hp,inv_mul_cancel_left]
    exact wordCoxeter_mem_parabolic M _ w hw
  · rintro ⟨ht,hm⟩
    let a := ambientCoxeterFace M T.val c
    let b := ambientCoxeterFace M T.val d
    let q := b.val.1⁻¹*a.val.1
    have hq : q ∈ coxeterParabolic M b.val.2 := hm
    have hp : b.val.1*q=a.val.1 := mul_inv_cancel_left _ _
    have hadd := length_mul_of_right_minimum M.toCoxeterSystem b.val.2 b.val.1 b.property q hq
    have hmin : ∀ v ∈ coxeterParabolic M a.val.2,
        M.toCoxeterSystem.length q ≤ M.toCoxeterSystem.length (q*v) := by
      intro v hv
      have H := a.property v hv
      have ha := length_mul_of_right_minimum M.toCoxeterSystem b.val.2 b.val.1 b.property
        (q*v) ((coxeterParabolic M b.val.2).mul_mem hq (coxeterParabolic_mono M ht hv))
      rw [←hp,mul_assoc,ha] at H
      rw [hadd] at H
      omega
    obtain ⟨w,hw,hr,he⟩ := (mem_parabolic_iff_reduced_word M.toCoxeterSystem b.val.2 q).mp hq
    refine ⟨ht,w,hw,hr,?_,?_⟩
    · intro v
      change wordCoxeter M w=q at he
      rw [he]
      exact hmin v v.property
    · change positiveLift M a.val.1 = positiveLift M b.val.1*wordArtin M w
      rw [←positiveLift_word M w hr]
      change wordCoxeter M w=q at he
      rw [he,←positiveLift_mul M _ _ hadd,hp]

lemma sourceFaceLifted_full (T : SphericalType M)
    (c : CoxeterCellFace (restrictedMatrix M T.val)) : sourceFaceLifted M T c ≤ (1,T) := by
  let a := ambientCoxeterFace M T.val c
  have hmem : a.val.1 ∈ coxeterParabolic M T.val := restrictionHom_mem_parabolic M T.val c.val.1
  obtain ⟨w,hw,hr,he⟩ := (mem_parabolic_iff_reduced_word M.toCoxeterSystem T.val a.val.1).mp hmem
  rw [lifted_le_iff_face]
  refine ⟨(by rintro _ ⟨s,_,rfl⟩;exact s.property),w,hw,hr,?_,?_⟩
  · intro v
    change wordCoxeter M w=a.val.1 at he
    rw [he]
    exact a.property v v.property
  · change positiveLift M a.val.1=1*wordArtin M w
    rw [one_mul,←positiveLift_word M w hr]
    exact congrArg (positiveLift M) he.symm

lemma sourceFaceLifted_surjective (T : SphericalType M) (b : LiftedCell M) (hb : b ≤ (1,T)) :
    ∃ c,sourceFaceLifted M T c=b := by
  obtain ⟨hRT,w,hw,hr,hm,he⟩ := (lifted_le_iff_face M _ _).mp hb
  let v : List T.val := w.attach.map fun s => ⟨s.val,hw s.val s.property⟩
  have hv : v.map Subtype.val=w := by simp [v,List.map_map,Function.comp_def]
  let R : Set T.val := Subtype.val ⁻¹' b.2.val
  have hR : Subtype.val '' R=b.2.val := by
    ext s
    constructor
    · rintro ⟨t,ht,rfl⟩;exact ht
    · intro hs;exact ⟨⟨s,hRT hs⟩,hs,rfl⟩
  let c : CoxeterCellFace (restrictedMatrix M T.val) :=
    ⟨(wordCoxeter (restrictedMatrix M T.val) v,R),by
      intro q hq
      have hq' : restrictionHom M T.val q ∈ coxeterParabolic M b.2.val := by
        rw [←hR,←restriction_parabolic_image]
        exact ⟨q,hq,rfl⟩
      have hh := hm ⟨restrictionHom M T.val q,hq'⟩
      rw [←hv,←restriction_word,←map_mul,restriction_length,restriction_length] at hh
      exact hh⟩
  refine ⟨c,Prod.ext ?_ (Subtype.ext hR)⟩
  change positiveLift M (restrictionHom M T.val (wordCoxeter (restrictedMatrix M T.val) v))=b.1
  rw [restriction_word,hv,positiveLift_word M w hr]
  simpa only [one_mul] using he.symm

noncomputable def sourceCellFaceIso (T : SphericalType M) :
    CoxeterCellFace (restrictedMatrix M T.val) ≃o Set.Iic ((1,T) : LiftedCell M) :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff
      (fun c => (⟨sourceFaceLifted M T c,sourceFaceLifted_full M T c⟩ : Set.Iic ((1,T) : LiftedCell M)))
      (fun c d => sourceFaceLifted_le_iff M T c d)) (by
        rintro ⟨b,hb⟩
        obtain ⟨c,hc⟩ := sourceFaceLifted_surjective M T b hb
        exact ⟨c,Subtype.ext hc⟩)

end HarmonicArtin

end OAI
