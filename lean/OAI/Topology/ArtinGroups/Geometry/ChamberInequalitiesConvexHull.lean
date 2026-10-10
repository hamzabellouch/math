import Mathlib
import OAI.Topology.ArtinGroups.Geometry.StrictChamber

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

theorem chamber_inequalities_convexHull (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 ≤ (representation cs w (e-σ w)) i) :
    e ∈ convexHull ℝ (Set.range σ) := by
  by_contra he
  obtain ⟨f,u,heu,hu⟩:=geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range σ)) ((Set.finite_range σ).isClosed_convexHull ℝ) he
  obtain ⟨w,a,ha,hf⟩:=dual_chamber_cover cs f.toLinearMap
  have hdiff : 0 ≤ f (e-σ w) := by
    rw [show f (e-σ w)=∑ i,a i*(representation cs w (e-σ w)) i from hf _]
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (ha i) (h w i))
  have hs:=hu (σ w) (subset_convexHull ℝ (Set.range σ) (Set.mem_range_self w))
  rw [map_sub] at hdiff
  linarith

theorem chamber_inequalities_interior (σ:W → S → ℝ) (e:S → ℝ)
    (h : ∀ w i,0 < (representation cs w (e-σ w)) i) :
    e ∈ interior (convexHull ℝ (Set.range σ)) := by
  let U : Set (S → ℝ) := {x | ∀ w i,0 < (representation cs w (x-σ w)) i}
  have ho : IsOpen U := by
    have hU : U=(⋂ w:W,⋂ i:S,{x:S → ℝ | 0 < (representation cs w (x-σ w)) i}) := by
      ext x
      simp [U]
    rw [hU]
    apply isOpen_iInter_of_finite
    intro w
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x:S → ℝ=>representation cs w (x-σ w)) :=
      ((representation cs w).toLinearMap.continuous_of_finiteDimensional).comp
      (continuous_id.sub continuous_const)
    exact isOpen_lt continuous_const ((continuous_apply i).comp hc)
  have hsub : U ⊆ convexHull ℝ (Set.range σ) := by
    intro x hx
    exact chamber_inequalities_convexHull cs σ x (fun w i=>(hx w i).le)
  exact interior_maximal hsub ho h

end HarmonicArtin.Geometric

end OAI
