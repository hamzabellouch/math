import Mathlib
import OAI.Topology.ArtinGroups.Geometry.OrbitHalfspace
import OAI.Topology.ArtinGroups.Realizations.AffineWeightMax
import OAI.Topology.ArtinGroups.Realizations.FiniteWeightsCompact

namespace OAI

namespace HarmonicArtin
open scoped BigOperators unitInterval

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def weightUpperCone {P : Type*} [PartialOrder P] (c : P) (w : OrderWeights P)
    (hc : ∀ p ∈ w.weights.support,p ≤ c) (t : unitInterval) : OrderWeights P :=
  coneWeights (weightInclusion (Set.Iic c)) c (fun q => Or.inl q.property) t
    (weightRestrict (Set.Iic c) w (fun p hp => hc p hp))

lemma weightUpperCone_support {P : Type*} [PartialOrder P] (c : P) (w : OrderWeights P)
    (hc : ∀ p ∈ w.weights.support,p ≤ c) (t : unitInterval) :
    ∀ p ∈ (weightUpperCone c w hc t).weights.support,p ≤ c := by
  intro p hp
  rcases Finset.mem_insert.mp (coneWeights_support _ _ _ _ _ hp) with hp|hp
  · exact hp ▸ le_rfl
  · obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact q.property

lemma weightUpperCone_value {P E : Type*} [PartialOrder P] [AddCommGroup E] [Module ℝ E]
    (z : P → E) (c : P) (w : OrderWeights P) (hc : ∀ p ∈ w.weights.support,p ≤ c)
    (t : unitInterval) : weightAffineValue z (weightUpperCone c w hc t) =
      (1-t.val) • weightAffineValue z w + t.val • z c := by
  unfold weightUpperCone
  rw [weightAffineValue_cone]
  have h := weightRestrict_map (Set.Iic c) w (fun p hp => hc p hp)
  exact congrArg (fun v => (1-t.val) • weightAffineValue z v + t.val • z c) h

namespace Geometric
open CoxeterExchange _root_.Matrix _root_.OAI.Matrix

variable {S : Type*} (M : CoxeterMatrix S) [Fintype S] [DecidableEq S] [Finite M.Group]

noncomputable def fullCoxeterFace : CoxeterCellFace M :=
  ⟨(1,Set.univ),fun v _ => by simp only [M.toCoxeterSystem.length_one]; exact Nat.zero_le _⟩

omit [Fintype S] [DecidableEq S] [Finite M.Group] in
lemma fullCoxeterFace_vertices : (fullCoxeterFace M).vertexSet = Set.univ := by
  ext w
  simp only [Set.mem_univ,iff_true]
  change 1⁻¹*w ∈ coxeterParabolic M Set.univ
  rw [inv_one,one_mul]
  obtain ⟨u,hu,rfl⟩ := M.toCoxeterSystem.exists_isReduced w
  exact (mem_parabolic_iff_reduced_word M.toCoxeterSystem Set.univ _).mpr
    ⟨u,by intros; trivial,hu,rfl⟩

lemma fullCoxeterFace_polytope : facePolytope M (fullCoxeterFace M) = permutahedron M := by
  rw [facePolytope,fullCoxeterFace_vertices,Set.image_univ]
  rfl

omit [Finite M.Group] in
lemma face_le_full (c : CoxeterCellFace M) : c ≤ fullCoxeterFace M := by
  rw [CoxeterCellFace.le_iff_vertices,fullCoxeterFace_vertices]
  exact Set.subset_univ _

theorem face_barycentric_surjective (c : CoxeterCellFace M) (x : S → ℝ)
    (hx : x ∈ facePolytope M c) :
    ∃ w : OrderWeights (CoxeterCellFace M),
      (∀ p ∈ w.weights.support,p ≤ c) ∧ weightAffineValue (faceCenter M) w = x := by
  induction c using (wellFounded_lt (α := CoxeterCellFace M)).induction generalizing x with
  | h c ih =>
    by_cases he : x = faceCenter M c
    · refine ⟨weightVertex c,?_,?_⟩
      · intro p hp
        have hp' : p = c := Finset.mem_singleton.mp (Finsupp.support_single_subset hp)
        exact hp' ▸ le_rfl
      · rw [weightAffineValue_vertex,he]
    · obtain ⟨d,y,t,hd,hy,ht,ht1,hx⟩ := face_boundary_step M c x hx he
      obtain ⟨w,hw,hval⟩ := ih d hd y hy
      have hc : ∀ p ∈ w.weights.support,p ≤ c := fun p hp => (hw p hp).trans hd.le
      let u : unitInterval := ⟨1-t,by linarith,by linarith⟩
      refine ⟨weightUpperCone c w hc u,weightUpperCone_support c w hc u,?_⟩
      rw [weightUpperCone_value,hval]
      change (1-(1-t)) • y+(1-t) • faceCenter M c=x
      rw [sub_sub_cancel,add_comm,←hx]

lemma barycentric_point_mem (w : OrderWeights (CoxeterCellFace M)) :
    weightAffineValue (faceCenter M) w ∈ permutahedron M := by
  apply weightAffineValue_mem _ w _ (convex_convexHull ℝ _)
  intro p _
  exact (facePolytope_eq_level M p ▸ faceCenter_mem M p).1

noncomputable def permutahedronBarycentric : OrderWeights (CoxeterCellFace M) → permutahedron M :=
  fun w => ⟨weightAffineValue (faceCenter M) w,barycentric_point_mem M w⟩

lemma permutahedronBarycentric_continuous : Continuous (permutahedronBarycentric M) := by
  let := Fintype.ofFinite (CoxeterCellFace M)
  exact (weightAffineValue_continuous (faceCenter M)).subtype_mk _

lemma permutahedronBarycentric_bijective : Function.Bijective (permutahedronBarycentric M) := by
  let := Fintype.ofFinite (CoxeterCellFace M)
  constructor
  · intro x y h
    exact weightAffineValue_injective (faceCenter M) (faceCovector M) (faceLevel M)
      (faceCenter_covector_le M) (faceCenter_covector_eq_iff M) (congrArg Subtype.val h)
  · intro x
    obtain ⟨w,_,hw⟩ := face_barycentric_surjective M (fullCoxeterFace M) x.val
      ((fullCoxeterFace_polytope M).symm ▸ x.property)
    exact ⟨w,Subtype.ext hw⟩

noncomputable def permutahedronBarycentricHomeomorph :
    OrderWeights (CoxeterCellFace M) ≃ₜ permutahedron M :=
  (show Continuous (Equiv.ofBijective (permutahedronBarycentric M)
    (permutahedronBarycentric_bijective M)) from permutahedronBarycentric_continuous M).homeoOfEquivCompactToT2

lemma permutahedronBarycentricHomeomorph_apply (w : OrderWeights (CoxeterCellFace M)) :
    (permutahedronBarycentricHomeomorph M w).val = weightAffineValue (faceCenter M) w := rfl

lemma barycentric_point_face_iff (w : OrderWeights (CoxeterCellFace M)) (c : CoxeterCellFace M) :
    weightAffineValue (faceCenter M) w ∈ facePolytope M c ↔ ∀ p ∈ w.weights.support,p ≤ c := by
  let := Fintype.ofFinite (CoxeterCellFace M)
  rw [facePolytope_eq_level]
  change (weightAffineValue (faceCenter M) w ∈ permutahedron M ∧
    faceCovector M c (weightAffineValue (faceCenter M) w) = faceLevel M c) ↔ _
  rw [and_iff_right (barycentric_point_mem M w)]
  rw [weightAffineValue_eq_iff _ _ _ _ (fun p => faceCenter_covector_le M p c)]
  simp only [faceCenter_covector_eq_iff]

end Geometric
end HarmonicArtin

end OAI
