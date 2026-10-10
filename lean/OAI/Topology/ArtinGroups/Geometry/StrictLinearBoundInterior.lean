import Mathlib
import OAI.Topology.ArtinGroups.Realizations.WeightUpperCone
import OAI.Topology.ArtinGroups.Geometry.PermutahedronBallHomeomorph

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange _root_.Matrix _root_.OAI.Matrix Topology

attribute [local instance] Classical.decEq Classical.propDecidable

lemma strict_linear_bound_of_interior {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (K : Set E) (b : ℝ)
    (hb : ∀ x ∈ K,f x ≤ b) (x : E) (hx : x ∈ interior K) : f x < b := by
  obtain ⟨v,hv⟩ : ∃ v,f v ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    ext v
    exact hn v
  let F : E →L[ℝ] ℝ := ⟨f,f.continuous_of_finiteDimensional⟩
  have hs : Function.Surjective F := by
    intro a
    refine ⟨(a/f v) • v,?_⟩
    change f ((a/f v) • v)=a
    rw [map_smul,smul_eq_mul,div_mul_cancel₀ _ hv]
  have hh : x ∈ interior (F ⁻¹' Set.Iic b) := interior_mono hb hx
  rw [F.interior_preimage hs] at hh
  have hh' : F x ∈ interior (Set.Iic b) := hh
  rw [interior_Iic] at hh'
  exact hh'

variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S) [Finite M.Group]

lemma proper_face_covector_ne_zero {c : CoxeterCellFace M} (hc : c < fullCoxeterFace M) :
    faceCovector M c ≠ 0 := by
  intro hf
  have hh := (faceCenter_covector_eq_iff M c c).mpr le_rfl
  have ht : faceCovector M c (faceCenter M (fullCoxeterFace M)) = faceLevel M c := by
    simpa only [hf,LinearMap.zero_apply] using hh
  exact (not_le_of_gt hc) ((faceCenter_covector_eq_iff M _ _).mp ht)

lemma proper_face_subset_frontier {c : CoxeterCellFace M} (hc : c < fullCoxeterFace M) :
    facePolytope M c ⊆ frontier (permutahedron M) := by
  intro x hx
  rw [facePolytope_eq_level] at hx
  refine ⟨subset_closure hx.1,?_⟩
  intro hi
  have hs := strict_linear_bound_of_interior (faceCovector M c) (proper_face_covector_ne_zero M hc)
    (permutahedron M) (faceLevel M c)
    (linear_le_on_convexHull _ _ _ (by rintro _ ⟨w,rfl⟩;exact faceCovector_bound M c w)) x hi
  rw [hx.2] at hs
  exact (lt_irrefl _ hs)

lemma frontier_active_halfspace (x : S → ℝ) (hx : x ∈ frontier (permutahedron M)) :
    ∃ k : M.Group × S,orbitHalfspace M k x=chamberPoint M k.2 := by
  have hm : x ∈ permutahedron M := (permutahedron_compact M).isClosed.closure_eq ▸ hx.1
  have hb := Set.ext_iff.mp (permutahedron_halfspaces M) x |>.mp hm
  by_contra hn
  push Not at hn
  have hstrict : ∀ k,orbitHalfspace M k x < chamberPoint M k.2 :=
    fun k => lt_of_le_of_ne (hb k) (hn k)
  have ho : IsOpen {y | ∀ k : M.Group × S,orbitHalfspace M k y < chamberPoint M k.2} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite (fun k =>
      isOpen_lt (orbitHalfspace M k).continuous_of_finiteDimensional continuous_const)
  have hsub : {y | ∀ k : M.Group × S,orbitHalfspace M k y < chamberPoint M k.2} ⊆
      permutahedron M := by
    rw [permutahedron_halfspaces]
    exact fun _ hy k => (hy k).le
  exact hx.2 (mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (ho.mem_nhds hstrict) hsub))

lemma orbitHalfspace_strict_vertex (k : M.Group × S) :
    orbitHalfspace M k (orbitPoint M (k.1⁻¹*M.toCoxeterSystem.simple k.2)) =
      chamberPoint M k.2 - 1 := by
  change representation M.toCoxeterSystem k.1 (orbitPoint M _) k.2 = _
  rw [orbitPoint,←LinearEquiv.mul_apply,←map_mul,mul_inv_cancel_left]
  change orbitPoint M (M.toCoxeterSystem.simple k.2) k.2 = _
  rw [orbitPoint_simple]
  simp

theorem permutahedron_frontier_faces (x : S → ℝ) :
    x ∈ frontier (permutahedron M) ↔
      ∃ c : CoxeterCellFace M,c < fullCoxeterFace M ∧ x ∈ facePolytope M c := by
  constructor
  · intro hx
    obtain ⟨k,hk⟩ := frontier_active_halfspace M x hx
    have hm : x ∈ permutahedron M := (permutahedron_compact M).isClosed.closure_eq ▸ hx.1
    obtain ⟨c,hc⟩ := support_face_of_attains M (orbitHalfspace M k) (chamberPoint M k.2)
      (orbitHalfspace_bound M k) x hm hk
    refine ⟨c,lt_of_le_of_ne (face_le_full M c) ?_,?_⟩
    · intro he
      have hv : orbitPoint M (k.1⁻¹*M.toCoxeterSystem.simple k.2) ∈ facePolytope M c := by
        rw [he,fullCoxeterFace_polytope]
        exact subset_convexHull ℝ _ (Set.mem_range_self _)
      rw [hc] at hv
      have hh := hv.2
      rw [orbitHalfspace_strict_vertex] at hh
      linarith
    · rw [hc]
      exact ⟨hm,hk⟩
  · rintro ⟨c,hc,hx⟩
    exact proper_face_subset_frontier M hc hx

end HarmonicArtin.Geometric

end OAI
