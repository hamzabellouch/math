import Mathlib
import OAI.Topology.ArtinGroups.Realizations.LiftedFaceChart

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric Topology

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

lemma sourceFaceMap_labels (T : SphericalType M)
    (c : CoxeterCellFace (restrictedMatrix M T.val))
    (d : CoxeterCellFace (restrictedMatrix M (sourceFaceLifted M T c).2.val)) :
    restrictionHom M T.val (geometricFaceInclusion M (sourceFaceLifted_full M T c) d).val.1 =
      restrictionHom M T.val c.val.1 * restrictionHom M (sourceFaceLifted M T c).2.val d.val.1 ∧
    Subtype.val '' (geometricFaceInclusion M (sourceFaceLifted_full M T c) d).val.2 =
      Subtype.val '' d.val.2 := by
  simpa only [map_one,one_mul,sourceFaceLifted,artinCoxeter_positiveLift] using
    geometricFaceInclusion_labels M (sourceFaceLifted_full M T c) d

omit [Fintype S] [DecidableEq S] in
lemma coxeterParabolic_empty_eq : coxeterParabolic M ∅ = ⊥ := by
  simp [coxeterParabolic]

noncomputable def vertexCoxeterFace (v : M.Group) : CoxeterCellFace M :=
  ⟨(v,∅),by
    intro w hw
    rw [coxeterParabolic_empty_eq,Subgroup.mem_bot] at hw
    rw [hw,mul_one]⟩

omit [Fintype S] [DecidableEq S] in
lemma vertexCoxeterFace_vertices (v : M.Group) : (vertexCoxeterFace M v).vertexSet={v} := by
  ext w
  change v⁻¹*w ∈ coxeterParabolic M ∅ ↔ w=v
  rw [coxeterParabolic_empty_eq,Subgroup.mem_bot,inv_mul_eq_one]
  exact eq_comm

omit [Fintype S] [DecidableEq S] in
lemma face_empty_eq_vertex (c : CoxeterCellFace M) (h : c.val.2=∅) :
    c=vertexCoxeterFace M c.val.1 := Subtype.ext (Prod.ext rfl h)

lemma faceCenter_vertex [Finite M.Group] (v : M.Group) :
    faceCenter M (vertexCoxeterFace M v)=orbitPoint M v := by
  have hf := faceCenter_mem M (vertexCoxeterFace M v)
  rw [facePolytope,vertexCoxeterFace_vertices,Set.image_singleton,convexHull_singleton] at hf
  exact hf

lemma permutahedron_vertex_point [Finite M.Group] (v : M.Group) :
    (permutahedronBarycentricHomeomorph M (weightVertex (vertexCoxeterFace M v))).val=
      orbitPoint M v := by
  rw [permutahedronBarycentricHomeomorph_apply,weightAffineValue_vertex,faceCenter_vertex]

lemma geometricFaceInclusion_vertex_type {a b : LiftedCell M} (h : a ≤ b)
    (v : (restrictedMatrix M a.2.val).Group) :
    (geometricFaceInclusion M h (vertexCoxeterFace (restrictedMatrix M a.2.val) v)).val.2=∅ := by
  have ht := (geometricFaceInclusion_labels M h (vertexCoxeterFace (restrictedMatrix M a.2.val) v)).2
  change Subtype.val '' _ = Subtype.val '' (∅ : Set a.2.val) at ht
  rw [Set.image_empty] at ht
  exact Set.image_eq_empty.mp ht

lemma sourceModelFaceMap_vertex {a b : LiftedCell M} (h : a ≤ b)
    (v : (restrictedMatrix M a.2.val).Group) :
    (sourceModelFaceMap M h (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val)
      (weightVertex (vertexCoxeterFace (restrictedMatrix M a.2.val) v)))).val =
      orbitPoint (restrictedMatrix M b.2.val)
        (geometricFaceInclusion M h (vertexCoxeterFace (restrictedMatrix M a.2.val) v)).val.1 := by
  rw [sourceModelFaceMap_affine,weightAffineValue_vertex]
  rw [face_empty_eq_vertex _ _ (geometricFaceInclusion_vertex_type M h v),faceCenter_vertex]
  rfl

lemma sourceModelFaceMap_center {a b : LiftedCell M} (h : a ≤ b)
    (c : CoxeterCellFace (restrictedMatrix M a.2.val)) :
    (sourceModelFaceMap M h (permutahedronBarycentricHomeomorph (restrictedMatrix M a.2.val)
      (weightVertex c))).val=faceCenter (restrictedMatrix M b.2.val) (geometricFaceInclusion M h c) := by
  rw [sourceModelFaceMap_affine,weightAffineValue_vertex]

end HarmonicArtin

end OAI
