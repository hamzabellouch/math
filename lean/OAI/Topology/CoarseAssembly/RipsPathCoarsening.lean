import OAI.Topology.CoarseAssembly.CocyclePathLifting
import OAI.Topology.CoarseAssembly.LoopCircle

namespace OAI

/-! # Coarsening preserves the parametrized graph loop

The paths at different Rips scales are the same barycentric paths. This
gives equality of their pushed-forward analytic classes, not merely a
choice of unrelated loops at successive scales.
-/

noncomputable section

namespace CoarseAssembly.Rips

variable {X : Type*} [PseudoMetricSpace X] {r s : ℝ}

theorem coarsen_interpolate (hrs : r ≤ s) (p q : Point X r) (hpq) (t : unitInterval) :
    coarsen hrs (interpolate p q hpq t) =
      interpolate (coarsen hrs p) (coarsen hrs q)
        (fun x hx y hy => (hpq x hx y hy).trans hrs) t := by
  apply Point.ext
  rfl

theorem coarsen_edgePath (hrs : r ≤ s) {x y : X} (hxy : dist x y ≤ r) (t : unitInterval) :
    coarsen hrs (edgePath hxy t) = edgePath (hxy.trans hrs) t := by
  apply Point.ext
  rfl

theorem coarsen_walkPath {G : SimpleGraph X} (hrs : r ≤ s) (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) {x y : X} (p : G.Walk x y)
    (t : unitInterval) :
    coarsen hrs (walkPath hr hE p t) =
      walkPath (hr.trans hrs) (fun x y h => (hE x y h).trans hrs) p t := by
  induction p generalizing t with
  | nil =>
    apply Point.ext
    rfl
  | cons h p ih =>
    simp only [walkPath, Path.trans_apply]
    split_ifs
    · exact coarsen_edgePath hrs _ _
    · exact ih _

theorem coarsen_loopCircle {G : SimpleGraph X} (hrs : r ≤ s) (hr : 0 ≤ r)
    (hE : ∀ x y, G.Adj x y → dist x y ≤ r) {x : X} (p : G.Walk x x) :
    (inclusion hrs).toContinuousMap.comp (loopCircle (walkPath hr hE p)) =
      loopCircle (walkPath (hr.trans hrs) (fun x y h => (hE x y h).trans hrs) p) := by
  apply ContinuousMap.ext
  intro z
  obtain ⟨t, rfl⟩ := circle_parameter_surjective z
  simp only [ContinuousMap.comp_apply, loopCircle_apply]
  exact coarsen_walkPath hrs hr hE p t

end CoarseAssembly.Rips

end

end OAI
