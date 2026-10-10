import Mathlib
import OAI.Topology.ArtinGroups.Geometry.StrictLinearBoundInterior
import OAI.Topology.ArtinGroups.Realizations.LiftedFaceChart

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric Topology

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

lemma liftedFaceEmbedding_injective (a : LiftedCell M) :
    Function.Injective (liftedFaceEmbedding M a) :=
  Subtype.val_injective.comp (liftedFaceChart M a).injective

lemma liftedFaceEmbedding_le_iff (a : LiftedCell M)
    (c d : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    liftedFaceEmbedding M a c ≤ liftedFaceEmbedding M a d ↔ c ≤ d :=
  (liftedFaceChart M a).le_iff_le

lemma liftedFaceEmbedding_le (a : LiftedCell M)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    liftedFaceEmbedding M a c ≤ a := (liftedFaceChart M a c).property

lemma liftedFaceEmbedding_full (a : LiftedCell M) :
    liftedFaceEmbedding M a (fullCoxeterFace (restrictedMatrix M a.2.val))=a := by
  apply le_antisymm (liftedFaceChart M a _).property
  have h := (liftedFaceChart M a).monotone
    (face_le_full (restrictedMatrix M a.2.val) ((liftedFaceChart M a).symm ⟨a,le_refl a⟩))
  rw [OrderIso.apply_symm_apply] at h
  exact h

lemma liftedFaceEmbedding_one (T : SphericalType M)
    (c : CoxeterCellFace (restrictedMatrix M T.val)) :
    liftedFaceEmbedding M (1,T) c=sourceFaceLifted M T c := by
  exact Prod.ext (one_mul _) rfl

lemma sourceCellMap_face_iff (a : LiftedCell M) (x : SourceModelCell M a.2)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    x.val ∈ facePolytope (restrictedMatrix M a.2.val) c ↔
      ∀ p ∈ (sourceCellMap M a x).weights.support,p ≤ liftedFaceEmbedding M a c := by
  let : DecidableEq (LiftedCell M) := Classical.decEq _
  obtain ⟨w,rfl⟩ := (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val)).surjective x
  rw [permutahedronBarycentricHomeomorph_apply,barycentric_point_face_iff,
    sourceCellMap_barycentric,weightMap_support_embedding _ (liftedFaceEmbedding_injective M a)]
  constructor
  · intro hw p hp
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp hp
    exact (liftedFaceEmbedding M a).monotone (hw d hd)
  · intro hw d hd
    exact (liftedFaceEmbedding_le_iff M a d c).mp (hw _ (Finset.mem_image.mpr ⟨d,hd,rfl⟩))

lemma sourceModelFaceMap_range (b : LiftedCell M)
    (c : CoxeterCellFace (restrictedMatrix M b.2.val)) (z : SourceModelCell M b.2) :
    z.val ∈ facePolytope (restrictedMatrix M b.2.val) c ↔
      ∃ x,sourceModelFaceMap M (liftedFaceEmbedding_le M b c) x=z := by
  rw [sourceCellMap_face_iff]
  constructor
  · intro hz
    obtain ⟨x,hx⟩ := sourceCellMap_range M (liftedFaceEmbedding M b c) (sourceCellMap M b z) hz
    refine ⟨x,sourceCellMap_injective M b ?_⟩
    exact (sourceModelFaceMap_included M (liftedFaceEmbedding_le M b c) x).trans hx
  · rintro ⟨x,rfl⟩
    rw [sourceModelFaceMap_included]
    exact sourceCellMap_support M _ x

lemma sourceModelFaceMap_injective {a b : LiftedCell M} (h : a ≤ b) :
    Function.Injective (sourceModelFaceMap M h) := by
  intro x y he
  apply sourceCellMap_injective M a
  rw [←sourceModelFaceMap_included M h,←sourceModelFaceMap_included M h,he]

noncomputable def sourceModelFaceHomeomorph (b : LiftedCell M)
    (c : CoxeterCellFace (restrictedMatrix M b.2.val)) :
    SourceModelCell M (liftedFaceEmbedding M b c).2 ≃ₜ
      {z : SourceModelCell M b.2 // z.val ∈ facePolytope (restrictedMatrix M b.2.val) c} := by
  letI : CompactSpace (SourceModelCell M (liftedFaceEmbedding M b c).2) :=
    isCompact_iff_compactSpace.mp (permutahedron_compact (restrictedMatrix M (liftedFaceEmbedding M b c).2.val))
  let f : SourceModelCell M (liftedFaceEmbedding M b c).2 →
      {z : SourceModelCell M b.2 // z.val ∈ facePolytope (restrictedMatrix M b.2.val) c} := fun x =>
    ⟨sourceModelFaceMap M (liftedFaceEmbedding_le M b c) x,
      (sourceModelFaceMap_range M b c _).mpr ⟨x,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · exact fun x y h => sourceModelFaceMap_injective M _ (congrArg Subtype.val h)
    · intro z
      obtain ⟨x,hx⟩ := (sourceModelFaceMap_range M b c z.val).mp z.property
      exact ⟨x,Subtype.ext hx⟩
  exact (show Continuous (Equiv.ofBijective f hf) from
    (sourceModelFaceMap M (liftedFaceEmbedding_le M b c)).continuous.subtype_mk _).homeoOfEquivCompactToT2

lemma sourceCellMap_frontier_iff (a : LiftedCell M) (x : SourceModelCell M a.2) :
    x.val ∈ frontier (permutahedron (restrictedMatrix M a.2.val)) ↔
      weightMax (sourceCellMap M a x) ≠ a := by
  rw [permutahedron_frontier_faces]
  constructor
  · rintro ⟨c,hc,hx⟩ he
    have hm := (sourceCellMap_face_iff M a x c).mp hx _ (weightMax_mem (sourceCellMap M a x))
    rw [he] at hm
    have hh := (liftedFaceEmbedding_full M a).trans_le hm
    exact hc.not_ge ((liftedFaceEmbedding_le_iff M a _ _).mp hh)
  · intro hn
    let d : Set.Iic a := ⟨weightMax (sourceCellMap M a x),
      sourceCellMap_support M a x _ (weightMax_mem (sourceCellMap M a x))⟩
    let c := (liftedFaceChart M a).symm d
    have he : liftedFaceEmbedding M a c=weightMax (sourceCellMap M a x) :=
      congrArg Subtype.val ((liftedFaceChart M a).apply_symm_apply d)
    refine ⟨c,lt_of_le_of_ne (face_le_full _ c) ?_,(sourceCellMap_face_iff M a x c).mpr ?_⟩
    · intro h
      have hh := congrArg (liftedFaceEmbedding M a) h
      rw [he,liftedFaceEmbedding_full] at hh
      exact hn hh
    · rw [he]
      exact le_weightMax _

lemma sourceCellMap_interior_iff (a : LiftedCell M) (x : SourceModelCell M a.2) :
    x.val ∈ interior (permutahedron (restrictedMatrix M a.2.val)) ↔
      weightMax (sourceCellMap M a x)=a := by
  have hc := (permutahedron_compact (restrictedMatrix M a.2.val)).isClosed
  have hf := sourceCellMap_frontier_iff M a x
  rw [frontier, hc.closure_eq,Set.mem_sdiff,and_iff_right x.property] at hf
  exact not_iff_not.mp hf

end HarmonicArtin

end OAI
