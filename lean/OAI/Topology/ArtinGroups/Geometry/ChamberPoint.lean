import Mathlib
import OAI.Topology.ArtinGroups.Geometry.ChamberCovector
import OAI.Topology.ArtinGroups.Coxeter.ArtinCoxeter
import OAI.Topology.ArtinGroups.Geometry.LinearConvexHull

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric _root_.Matrix _root_.OAI.Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} (M : CoxeterMatrix S)

lemma simple_mem_coxeterParabolic_iff [Fintype S] [DecidableEq S] (R : Set S) (i : S) :
    M.toCoxeterSystem.simple i ∈ coxeterParabolic M R ↔ i ∈ R := by
  constructor
  · intro h
    obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word M.toCoxeterSystem R _).mp h
    have hl : u.length = 1 := by rw [←hr.eq,he,M.toCoxeterSystem.length_simple]
    obtain ⟨j,rfl⟩ := List.length_eq_one_iff.mp hl
    have hj : j = i := simple_injective M.toCoxeterSystem (by simpa using he)
    subst j
    exact hu i (by simp)
  · exact simple_mem_parabolic M.toCoxeterSystem R

namespace CoxeterCellFace
variable {M}
lemma le_iff_vertices [Fintype S] [DecidableEq S] (c d : CoxeterCellFace M) : c ≤ d ↔ c.vertexSet ⊆ d.vertexSet := by
  refine ⟨fun h => h.2,fun h => ⟨?_,h⟩⟩
  intro i hi
  have hc : c.val.1*M.toCoxeterSystem.simple i ∈ c.vertexSet := by
    change c.val.1⁻¹*(c.val.1*M.toCoxeterSystem.simple i) ∈ coxeterParabolic M c.val.2
    rw [inv_mul_cancel_left]
    exact simple_mem_parabolic M.toCoxeterSystem _ hi
  have h1 := h c.source_mem
  have h2 := h hc
  have hm := (coxeterParabolic M d.val.2).mul_mem
    ((coxeterParabolic M d.val.2).inv_mem h1) h2
  have he : (d.val.1⁻¹*c.val.1)⁻¹ * (d.val.1⁻¹*(c.val.1*M.toCoxeterSystem.simple i)) =
      M.toCoxeterSystem.simple i := by group
  rw [he] at hm
  exact (simple_mem_coxeterParabolic_iff M _ i).mp hm

instance [Finite S] [Finite M.Group] : Finite (CoxeterCellFace M) :=
  inferInstanceAs (Finite {c : M.Group × Set S //
    ∀ v ∈ coxeterParabolic M c.2,
      M.toCoxeterSystem.length c.1 ≤ M.toCoxeterSystem.length (c.1*v)})

instance vertices_nonempty (c : CoxeterCellFace M) : Nonempty c.vertexSet := ⟨⟨c.val.1,c.source_mem⟩⟩
noncomputable instance vertices_fintype [Finite M.Group] (c : CoxeterCellFace M) :
    Fintype c.vertexSet := Fintype.ofFinite _

end CoxeterCellFace

namespace Geometric
variable [Fintype S] [DecidableEq S] [Finite M.Group]

noncomputable def chamberPoint : S → ℝ := by
  letI := Fintype.ofFinite M.Group
  exact (exists_strict_chamber M.toCoxeterSystem).choose

lemma chamberPoint_spec : cartan M *ᵥ chamberPoint M = 1 := by
  let := Fintype.ofFinite M.Group
  exact funext (exists_strict_chamber M.toCoxeterSystem).choose_spec

noncomputable def orbitPoint (w : M.Group) : S → ℝ := representation M.toCoxeterSystem w (chamberPoint M)

lemma orbitPoint_inj : Function.Injective (orbitPoint M) :=
  orbitPoint_injective M.toCoxeterSystem _ (chamberPoint_spec M)

noncomputable def permutahedron : Set (S → ℝ) := convexHull ℝ (Set.range (orbitPoint M))

noncomputable def faceCoefficient (R : Set S) (i : S) : ℝ := if i ∈ R then 0 else 1

omit [Fintype S] [DecidableEq S] in
lemma faceCoefficient_nonneg (R : Set S) (i : S) : 0 ≤ faceCoefficient R i := by
  dsimp [faceCoefficient]; split <;> norm_num

omit [Fintype S] [DecidableEq S] in
lemma faceCoefficient_zero (R : Set S) : {i | faceCoefficient R i = 0} = R := by
  ext i; simp [faceCoefficient]

noncomputable def faceCovector (c : CoxeterCellFace M) : (S → ℝ) →ₗ[ℝ] ℝ :=
  (chamberCovector (faceCoefficient c.val.2)).comp
    (representation M.toCoxeterSystem c.val.1⁻¹).toLinearMap

noncomputable def faceLevel (c : CoxeterCellFace M) : ℝ :=
  chamberCovector (faceCoefficient c.val.2) (chamberPoint M)

lemma faceCovector_orbit (c : CoxeterCellFace M) (w : M.Group) :
    faceCovector M c (orbitPoint M w) =
      chamberCovector (faceCoefficient c.val.2) (orbitPoint M (c.val.1⁻¹*w)) := by
  simp only [faceCovector,LinearMap.comp_apply,LinearEquiv.coe_coe,orbitPoint,map_mul,LinearEquiv.mul_apply]

lemma faceCovector_bound (c : CoxeterCellFace M) (w : M.Group) :
    faceCovector M c (orbitPoint M w) ≤ faceLevel M c := by
  rw [faceCovector_orbit]
  exact orbit_dominant_bound M.toCoxeterSystem _ (chamberPoint_spec M) _
    (faceCoefficient_nonneg c.val.2) _

lemma faceCovector_eq_iff (c : CoxeterCellFace M) (w : M.Group) :
    faceCovector M c (orbitPoint M w) = faceLevel M c ↔ w ∈ c.vertexSet := by
  rw [faceCovector_orbit]
  change chamberCovector _ (representation _ _ _) = chamberCovector _ _ ↔ _
  rw [orbit_dominant_equality M.toCoxeterSystem _ (chamberPoint_spec M) _
    (faceCoefficient_nonneg c.val.2),faceCoefficient_zero]
  rfl

noncomputable def facePolytope (c : CoxeterCellFace M) : Set (S → ℝ) :=
  convexHull ℝ (orbitPoint M '' c.vertexSet)

lemma facePolytope_eq_level (c : CoxeterCellFace M) :
    facePolytope M c = {x | x ∈ permutahedron M ∧ faceCovector M c x = faceLevel M c} := by
  change convexHull ℝ (orbitPoint M '' c.vertexSet) = {x | x ∈ convexHull ℝ (Set.range (orbitPoint M)) ∧ faceCovector M c x = faceLevel M c}
  rw [convexHull_supporting_level _ _ _ (by rintro _ ⟨w,rfl⟩; exact faceCovector_bound M c w)]
  congr 1
  ext x
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨Set.mem_range_self w,(faceCovector_eq_iff M c w).mpr hw⟩
  · rintro ⟨⟨w,rfl⟩,hw⟩
    exact ⟨w,(faceCovector_eq_iff M c w).mp hw,rfl⟩

lemma orbit_mem_facePolytope (c : CoxeterCellFace M) (w : M.Group) :
    orbitPoint M w ∈ facePolytope M c ↔ w ∈ c.vertexSet := by
  rw [facePolytope_eq_level]
  exact ⟨fun h => (faceCovector_eq_iff M c w).mp h.2,fun h =>
    ⟨subset_convexHull ℝ _ (Set.mem_range_self w),(faceCovector_eq_iff M c w).mpr h⟩⟩

lemma facePolytope_mono {c d : CoxeterCellFace M} (h : c ≤ d) :
    facePolytope M c ⊆ facePolytope M d := convexHull_mono (Set.image_mono h.2)

lemma facePolytope_subset_iff (c d : CoxeterCellFace M) :
    facePolytope M c ⊆ facePolytope M d ↔ c ≤ d := by
  refine ⟨fun h => (CoxeterCellFace.le_iff_vertices c d).mpr ?_,facePolytope_mono M⟩
  intro w hw
  exact (orbit_mem_facePolytope M d w).mp (h ((orbit_mem_facePolytope M c w).mpr hw))

noncomputable def faceCenter (c : CoxeterCellFace M) : S → ℝ :=
  (Fintype.card c.vertexSet : ℝ)⁻¹ • ∑ w : c.vertexSet,orbitPoint M w

lemma faceCenter_mem (c : CoxeterCellFace M) : faceCenter M c ∈ facePolytope M c := by
  have he : Set.range (fun w : c.vertexSet => orbitPoint M w) = orbitPoint M '' c.vertexSet := by
    ext x; simp
  rw [facePolytope,←he]
  exact finite_average_mem _

lemma faceCenter_covector_le (c d : CoxeterCellFace M) :
    faceCovector M d (faceCenter M c) ≤ faceLevel M d :=
  finite_average_le _ _ _ (fun w => faceCovector_bound M d w)

lemma faceCenter_covector_eq_iff (c d : CoxeterCellFace M) :
    faceCovector M d (faceCenter M c) = faceLevel M d ↔ c ≤ d := by
  rw [faceCenter,finite_average_eq_iff _ _ _ (fun w : c.vertexSet => faceCovector_bound M d w)]
  simp only [faceCovector_eq_iff]
  rw [CoxeterCellFace.le_iff_vertices]
  exact ⟨fun h w hw => h ⟨w,hw⟩,fun h w => h w.property⟩

theorem orbit_support_face (f : (S → ℝ) →ₗ[ℝ] ℝ) :
    ∃ c : CoxeterCellFace M,
      (∀ w, f (orbitPoint M w) ≤ f (orbitPoint M c.val.1)) ∧
       (∀ w, f (orbitPoint M w) = f (orbitPoint M c.val.1) ↔ w ∈ c.vertexSet) := by
  let := Fintype.ofFinite M.Group
  obtain ⟨q,a,ha,hf⟩ := dual_chamber_cover M.toCoxeterSystem f
  let R : Set S := {i | a i = 0}
  obtain ⟨u,v,hv,hu,he,_⟩ := exists_right_parabolic_decomposition M.toCoxeterSystem R q⁻¹
  let c : CoxeterCellFace M := ⟨(u,R),hu⟩
  have hval (w : M.Group) : f (orbitPoint M w) =
      chamberCovector a (orbitPoint M (q*w)) := by
    rw [hf,chamberCovector_apply]
    simp only [orbitPoint,map_mul,LinearEquiv.mul_apply]
  have hb (w : M.Group) : f (orbitPoint M w) ≤ chamberCovector a (chamberPoint M) := by
    rw [hval]
    exact orbit_dominant_bound M.toCoxeterSystem _ (chamberPoint_spec M) a ha _
  have heq (w : M.Group) : f (orbitPoint M w) = chamberCovector a (chamberPoint M) ↔
      w ∈ c.vertexSet := by
    rw [hval]
    change chamberCovector a (representation M.toCoxeterSystem (q*w) (chamberPoint M)) = _ ↔ _
    rw [orbit_dominant_equality M.toCoxeterSystem _ (chamberPoint_spec M) a ha]
    have hq : q = v⁻¹*u⁻¹ := by rw [←_root_.mul_inv_rev,←he,inv_inv]
    rw [hq,mul_assoc]
    exact (parabolic M.toCoxeterSystem R).mul_mem_cancel_left
      ((parabolic M.toCoxeterSystem R).inv_mem hv)
  have hc := (heq u).mpr c.source_mem
  refine ⟨c,?_,?_⟩
  · intro w; change f (orbitPoint M w) ≤ f (orbitPoint M u); rw [hc]; exact hb w
  · intro w; change f (orbitPoint M w) = f (orbitPoint M u) ↔ _; rw [hc]; exact heq w

end Geometric
end HarmonicArtin

end OAI
