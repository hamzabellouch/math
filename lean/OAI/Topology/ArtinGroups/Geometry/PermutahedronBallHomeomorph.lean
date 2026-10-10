import Mathlib
import OAI.Topology.ArtinGroups.Geometry.OrbitHalfspace

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S) [Finite M.Group]

lemma orbitPoint_simple (i : S) : orbitPoint M (M.toCoxeterSystem.simple i) =
    chamberPoint M - Pi.single i 1 := by
  rw [orbitPoint,representation_simple,simpleReflection_apply,chamberPoint_spec]
  simp

lemma permutahedron_affineSpan : affineSpan ℝ (permutahedron M) = ⊤ := by
  let A := affineSpan ℝ (permutahedron M)
  have hv : ∀ w,orbitPoint M w ∈ A := fun w => subset_affineSpan ℝ _
    (subset_convexHull ℝ _ ⟨w,rfl⟩)
  have hp : chamberPoint M ∈ A := by simpa [orbitPoint] using hv 1
  apply (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨_,hp⟩).mp
  apply top_unique
  intro x _
  have he : ∀ i,Pi.single i (1:ℝ) ∈ A.direction := by
    intro i
    have hh := AffineSubspace.vsub_mem_direction hp (hv (M.toCoxeterSystem.simple i))
    rw [orbitPoint_simple] at hh
    simpa only [vsub_eq_sub,sub_sub_cancel] using hh
  have hx : x = ∑ i,x i • Pi.single i (1:ℝ) := by
    funext j
    simp [Pi.single_apply]
  rw [hx]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (he i))

lemma permutahedron_interior_nonempty : (interior (permutahedron M)).Nonempty :=
  (convex_convexHull ℝ _).interior_nonempty_iff_affineSpan_eq_top.mpr (permutahedron_affineSpan M)

theorem permutahedron_ball_pair : ∃ h : (S → ℝ) ≃ₜ (S → ℝ),
    h '' interior (permutahedron M) = Metric.ball 0 1 ∧
    h '' permutahedron M = Metric.closedBall 0 1 ∧
    h '' frontier (permutahedron M) = Metric.sphere 0 1 := by
  obtain ⟨h,hi,hc,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (convex_convexHull ℝ (Set.range (orbitPoint M))) (permutahedron_interior_nonempty M)
      (permutahedron_compact M).isBounded
  change h '' closure (permutahedron M) = Metric.closedBall 0 1 at hc
  rw [(permutahedron_compact M).isClosed.closure_eq] at hc
  exact ⟨h,hi,hc,hf⟩

noncomputable def permutahedronBallHomeomorph :
    permutahedron M ≃ₜ Metric.closedBall (0 : S → ℝ) 1 := by
  let h := (permutahedron_ball_pair M).choose
  have he : h '' permutahedron M = Metric.closedBall 0 1 :=
    (permutahedron_ball_pair M).choose_spec.2.1
  exact h.sets (by rw [←he,Set.preimage_image_eq _ h.injective])

omit [DecidableEq S] [Finite M.Group] in
lemma permutahedron_dimension : Module.finrank ℝ (S → ℝ) = Fintype.card S := by simp

end HarmonicArtin.Geometric

end OAI
