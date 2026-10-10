import OAI.Topology.CoarseAssembly.FilledEdges
import OAI.Topology.CoarseAssembly.CocyclePathLifting
import OAI.Topology.CoarseAssembly.LoopCircle

namespace OAI

/-! # Filling the actual parametrized lattice walks

Straight segments in the compact polygon follow the same concatenation as
the barycentric graph path. Thus every closed base walk, with its original
parametrization, factors through the filled polygon.
-/

noncomputable section

namespace CoarseAssembly

open Rips

theorem discEdgeBound {j : ℕ} (u v : Disc j) (h : (discGraph j).Adj u v) :
    dist u v ≤ (1 : ℝ) := by
  rw [discGraphMetric_eq]
  change ((discGraph j).dist u v : ℝ) ≤ 1
  exact_mod_cast (show (discGraph j).dist u v ≤ 1 by
    simpa using (discGraph j).dist_le h.toWalk)

def filledWalk {j : ℕ} : {u v : Disc j} → (discGraph j).Walk u v →
    Path (filledVertex u) (filledVertex v)
  | _, _, .nil => Path.refl _
  | _, _, .cons _ p => (filledSegment (filledVertex _) (filledVertex _)).trans (filledWalk p)

theorem filledToRips_walk {j : ℕ} {u v : Disc j} (p : (discGraph j).Walk u v)
    (t : unitInterval) :
    filledToRipsPoint j (filledWalk p t) =
      walkPath (by norm_num : (0 : ℝ) ≤ 1) discEdgeBound p t := by
  induction p generalizing t with
  | nil => exact filledToRips_vertex _
  | cons h p ih =>
    simp only [filledWalk, walkPath, Path.trans_apply]
    split_ifs
    · exact filledToRips_edge h _
    · exact ih _

/-- Exact factorization through the filled compact polygon, not a homotopy
or a change of parametrization. -/
theorem filledToRips_loop {j : ℕ} {u : Disc j} (p : (discGraph j).Walk u u) :
    (filledToRips j).comp (loopCircle (filledWalk p)) =
      loopCircle (walkPath (by norm_num : (0 : ℝ) ≤ 1) discEdgeBound p) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [ContinuousMap.comp_apply, loopCircle_apply]
  exact filledToRips_walk p t

end CoarseAssembly

end

end OAI
