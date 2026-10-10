import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ChamberPoint
import OAI.Topology.ArtinGroups.Geometry.FiniteHalfspaceBoundaryStep

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M : CoxeterMatrix S) [Fintype S] [DecidableEq S] [Finite M.Group]

lemma permutahedron_compact : IsCompact (permutahedron M) :=
  (Set.finite_range (orbitPoint M)).isCompact_convexHull ℝ

noncomputable def orbitHalfspace (k : M.Group × S) : (S → ℝ) →ₗ[ℝ] ℝ :=
  (LinearMap.proj k.2).comp (representation M.toCoxeterSystem k.1).toLinearMap

lemma chamberCovector_basis (i : S) (x : S → ℝ) : chamberCovector (Pi.single i 1) x = x i := by
  simp [chamberCovector_apply,Pi.single_apply]

lemma orbitHalfspace_bound (k : M.Group × S) (w : M.Group) :
    orbitHalfspace M k (orbitPoint M w) ≤ chamberPoint M k.2 := by
  have h := orbit_dominant_bound M.toCoxeterSystem (chamberPoint M) (chamberPoint_spec M)
    (Pi.single k.2 1)
    (by intro coordinate; simp only [Pi.single_apply]; split_ifs <;> norm_num) (k.1*w)
  simp only [chamberCovector_basis] at h
  simpa only [orbitHalfspace,LinearMap.comp_apply,LinearMap.proj_apply,LinearEquiv.coe_coe,
    orbitPoint,map_mul,LinearEquiv.mul_apply] using h

lemma permutahedron_halfspaces : permutahedron M =
    {x | ∀ k : M.Group × S, orbitHalfspace M k x ≤ chamberPoint M k.2} := by
  ext x
  constructor
  · intro hx k
    exact linear_le_on_convexHull _ _ _ (by rintro _ ⟨w,rfl⟩; exact orbitHalfspace_bound M k w) x hx
  · intro hx
    by_contra hn
    obtain ⟨f,b,hb,hfb⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      (permutahedron_compact M).isClosed hn
    let := Fintype.ofFinite M.Group
    obtain ⟨q,a,ha,hf⟩ := dual_chamber_cover M.toCoxeterSystem f.toLinearMap
    have hf' (v : S → ℝ) : f v = ∑ i, a i * representation M.toCoxeterSystem q v i := hf v
    have hbound : f x ≤ ∑ i,a i * chamberPoint M i := by
      rw [hf']
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hx (q,i)) (ha i)
    have he : f (orbitPoint M q⁻¹) = ∑ i,a i*chamberPoint M i := by
      rw [hf']
      simp only [orbitPoint,←LinearEquiv.mul_apply,←map_mul,mul_inv_cancel,map_one]
      rfl
    have hh := hb (orbitPoint M q⁻¹) (subset_convexHull ℝ _ (Set.mem_range_self _))
    rw [he] at hh
    linarith

lemma support_face_of_attains (f : (S → ℝ) →ₗ[ℝ] ℝ) (b : ℝ)
    (hb : ∀ w, f (orbitPoint M w) ≤ b) (y : S → ℝ)
    (hy : y ∈ permutahedron M) (he : f y = b) :
    ∃ d : CoxeterCellFace M,
      facePolytope M d = {x | x ∈ permutahedron M ∧ f x = b} := by
  obtain ⟨d,hd,heq⟩ := orbit_support_face M f
  have hh := linear_le_on_convexHull f _ _ (by rintro _ ⟨w,rfl⟩; exact hd w) y hy
  have hm : f (orbitPoint M d.val.1) = b := by linarith [hb d.val.1]
  refine ⟨d,?_⟩
  change convexHull ℝ (orbitPoint M '' d.vertexSet) =
    {x | x ∈ convexHull ℝ (Set.range (orbitPoint M)) ∧ f x = b}
  rw [convexHull_supporting_level _ _ _ (by rintro _ ⟨w,rfl⟩; exact hb w)]
  congr 1
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨Set.mem_range_self _,hm ▸ (heq w).mpr hw⟩
  · rintro ⟨⟨w,rfl⟩,hw⟩
    exact ⟨w,(heq w).mp (hw.trans hm.symm),rfl⟩

theorem face_boundary_step (c : CoxeterCellFace M) (x : S → ℝ)
    (hx : x ∈ facePolytope M c) (hne : x ≠ faceCenter M c) :
    ∃ (d : CoxeterCellFace M) (y : S → ℝ) (t : ℝ),
      d < c ∧ y ∈ facePolytope M d ∧ 0 < t ∧ t ≤ 1 ∧
      x = (1-t) • faceCenter M c + t • y := by
  let := Fintype.ofFinite M.Group
  have hc := faceCenter_mem M c
  rw [facePolytope_eq_level] at hc hx
  obtain ⟨y,r,k,hy,hr,hyr,hyk,hck⟩ := finite_halfspace_boundary_step (orbitHalfspace M)
    (fun k => chamberPoint M k.2) (permutahedron M) (permutahedron_halfspaces M)
    (permutahedron_compact M) (faceCenter M c) x hc.1 hx.1 hne
  have hyc := boundary_step_level hyr (faceCovector M c) hc.2 hx.2
  let f := faceCovector M c + orbitHalfspace M k
  let b := faceLevel M c + chamberPoint M k.2
  have hb (w : M.Group) : f (orbitPoint M w) ≤ b :=
    add_le_add (faceCovector_bound M c w) (orbitHalfspace_bound M k w)
  have hey : f y = b := by
    change faceCovector M c y + orbitHalfspace M k y = faceLevel M c + chamberPoint M k.2
    rw [hyc,hyk]
  obtain ⟨d,hd⟩ := support_face_of_attains M f b hb y hy hey
  have hdy : y ∈ facePolytope M d := by rw [hd]; exact ⟨hy,hey⟩
  have hdc : d ≤ c := by
    apply (facePolytope_subset_iff M d c).mp
    intro z hz
    rw [hd] at hz
    rw [facePolytope_eq_level]
    refine ⟨hz.1,?_⟩
    have h1 := linear_le_on_convexHull (faceCovector M c) _ _
      (by rintro _ ⟨w,rfl⟩; exact faceCovector_bound M c w) z hz.1
    have h2 := linear_le_on_convexHull (orbitHalfspace M k) _ _
      (by rintro _ ⟨w,rfl⟩; exact orbitHalfspace_bound M k w) z hz.1
    have hz' : faceCovector M c z + orbitHalfspace M k z = faceLevel M c + chamberPoint M k.2 := hz.2
    linarith
  have hne' : d ≠ c := by
    intro he
    have hh : faceCenter M c ∈ facePolytope M d := by rw [he]; exact faceCenter_mem M c
    rw [hd] at hh
    have hh' : faceCovector M c (faceCenter M c) + orbitHalfspace M k (faceCenter M c) = faceLevel M c + chamberPoint M k.2 := hh.2
    linarith [hc.2]
  refine ⟨d,y,r⁻¹,lt_of_le_of_ne hdc hne',hdy,inv_pos.mpr (by linarith),?_,?_⟩
  · exact (inv_le_one₀ (by linarith : 0 < r)).mpr hr
  · exact boundary_step_combo hr hyr

end HarmonicArtin.Geometric

end OAI
