import Mathlib
import OAI.Topology.ArtinGroups.Geometry.CoordinateExtension

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_chamber_convexHull (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (σ:coxeterParabolic M J → J → ℝ) (e:J → ℝ)
    (h:∀ (w:coxeterParabolic M J) (i:J),0 ≤ (representation M.toCoxeterSystem w
      (coordinateExtension J (e-σ w))) i) :
    e ∈ convexHull ℝ (Set.range σ) := by
  let : Finite (coxeterParabolic M J):=hJ
  let : Fintype (coxeterParabolic M J):=Fintype.ofFinite _
  by_contra he
  obtain ⟨f,u,heu,hu⟩:=geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range σ)) ((Set.finite_range σ).isClosed_convexHull ℝ) he
  obtain ⟨w,a,ha,hf⟩:=spherical_dual_chamber_cover M J hJ f.toLinearMap
  have hdiff:0 ≤ f (e-σ w) := by
    rw [show f (e-σ w)=∑ i,a i*(representation M.toCoxeterSystem w
      (coordinateExtension J (e-σ w))) i from hf _]
    exact Finset.sum_nonneg (fun i _=>mul_nonneg (ha i) (h w i))
  have hs:=hu (σ w) (subset_convexHull ℝ (Set.range σ) (Set.mem_range_self w))
  rw [map_sub] at hdiff
  linarith

theorem spherical_chamber_interior (M:CoxeterMatrix S) (J:Set S)
    (hJ:IsSpherical M J) (σ:coxeterParabolic M J → J → ℝ) (e:J → ℝ)
    (h:∀ (w:coxeterParabolic M J) (i:J),0 < (representation M.toCoxeterSystem w
      (coordinateExtension J (e-σ w))) i) :
    e ∈ interior (convexHull ℝ (Set.range σ)) := by
  let : Finite (coxeterParabolic M J):=hJ
  let : Fintype (coxeterParabolic M J):=Fintype.ofFinite _
  let U:Set (J → ℝ):={x | ∀ (w:coxeterParabolic M J) (i:J),0 < (representation M.toCoxeterSystem w
    (coordinateExtension J (x-σ w))) i}
  have ho:IsOpen U := by
    have hU:U=(⋂ w:coxeterParabolic M J,⋂ i:J,{x:J → ℝ |
      0 < (representation M.toCoxeterSystem w (coordinateExtension J (x-σ w))) i}) := by
      ext x
      simp [U]
    rw [hU]
    apply isOpen_iInter_of_finite
    intro w
    apply isOpen_iInter_of_finite
    intro i
    have hc:Continuous (fun x:J → ℝ=>coordinateExtension J (x-σ w)) := by
      unfold coordinateExtension
      apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).sub continuous_const).smul continuous_const
    have hr:=((representation M.toCoxeterSystem w).toLinearMap.continuous_of_finiteDimensional).comp hc
    exact isOpen_lt continuous_const ((continuous_apply (i:S)).comp hr)
  have hsub:U ⊆ convexHull ℝ (Set.range σ) := by
    intro x hx
    exact spherical_chamber_convexHull M J hJ σ x (fun w i=>(hx w i).le)
  exact interior_maximal hsub ho h

end HarmonicArtin.Geometric

end OAI
