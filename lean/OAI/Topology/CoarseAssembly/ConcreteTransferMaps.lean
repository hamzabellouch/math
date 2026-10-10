import OAI.Topology.CoarseAssembly.ConcreteSpaces
import Mathlib.Topology.MetricSpace.Bounded

namespace OAI

/-! # The controlled fiber maps on the separated coarse union

Within a component these are compositions of graph-edge maps. On the
finitely many relevant cross-component pairs they are rank-one constant
maps. This discharges the second geometric hypothesis of the transfer
criterion on the actual coarse spaces.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

variable (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)

theorem vertexUnion_dist_same {j : ℕ} (u v : Disc j)
    (q : Quotient (discDepth j u)) (r : Quotient (discDepth j v)) :
    @dist VertexUnion (vertexUnionMetric S t).toDist
      ⟨⟨j, u⟩, q⟩ ⟨⟨j, v⟩, r⟩ =
      ((fiberedGraph S t j).dist ⟨u, q⟩ ⟨v, r⟩ : ℝ) := by
  let := componentMetric S t
  have hdist := separatedDist_same fiberBoundaryBase j ⟨u, q⟩ ⟨v, r⟩
  change _ = @dist _ (componentMetric S t j).toDist ⟨u, q⟩ ⟨v, r⟩ at hdist
  rw [componentMetric_eq S t j] at hdist
  exact hdist

private def constantMap (u v : BaseUnion) :
    lp (fun _ : BaseFiber v => ℂ) 2 →L[ℂ] lp (fun _ : BaseFiber u => ℂ) 2 :=
  (fiberConstantIsometry (BaseFiber u)).toContinuousLinearMap.comp
    (fiberConstantIsometry (BaseFiber v)).toContinuousLinearMap.adjoint

private theorem constantMap_norm (u v : BaseUnion) : ‖constantMap u v‖ ≤ 1 := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have hu := (fiberConstantIsometry (H := ℂ) (BaseFiber u)).norm_toContinuousLinearMap_le
  have hv := (fiberConstantIsometry (H := ℂ) (BaseFiber v)).norm_toContinuousLinearMap_le
  rw [← LinearIsometryEquiv.norm_map (ContinuousLinearMap.adjoint)] at hv
  exact (mul_le_mul hu hv (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

private theorem constantMap_constant (u v : BaseUnion) :
    constantMap u v (fiberConstant (BaseFiber v) (1 : ℂ)) =
      fiberConstant (BaseFiber u) 1 := by
  change (fiberConstantIsometry (BaseFiber u))
    ((fiberConstantIsometry (BaseFiber v)).toContinuousLinearMap.adjoint
      ((fiberConstantIsometry (BaseFiber v)) (1 : ℂ))) = _
  rw [adjoint_apply_isometry]
  rfl

theorem concrete_controlled_fiber_maps :
    letI : MetricSpace VertexUnion := vertexUnionMetric S t
    ControlledFiberMaps BaseFiber := by
  classical
  let : MetricSpace VertexUnion := vertexUnionMetric S t
  intro R hR
  let e := Equiv.sigmaAssoc (fun j u => Quotient (discDepth j u))
  let initial := componentPrefix (V := FiberVertex) ⌈R⌉₊
  let W : Set VertexUnion := e.symm '' (initial : Set ((j : ℕ) × FiberVertex j))
  have hW : W.Finite := initial.finite_toSet.image e.symm
  obtain ⟨B, hB⟩ := Metric.isBounded_iff.mp hW.isBounded
  let s : ℝ := max (⌈R⌉₊ : ℝ) B
  have hs : 0 ≤ s := (Nat.cast_nonneg _).trans (le_max_left _ _)
  have hex : ∀ u v : BaseUnion, ∃ O :
      lp (fun _ : BaseFiber v => ℂ) 2 →L[ℂ] lp (fun _ : BaseFiber u => ℂ) 2,
      dist u v ≤ R → ‖O‖ ≤ 1 ∧
        O (fiberConstant (BaseFiber v) (1 : ℂ)) = fiberConstant (BaseFiber u) 1 ∧
        ∀ q r, s < dist (⟨u, q⟩ : VertexUnion) ⟨v, r⟩ → O (lp.single 2 r 1) q = 0 := by
    rintro ⟨i, u⟩ ⟨j, v⟩
    by_cases hij : i = j
    · subst j
      obtain ⟨p, hp⟩ := (discGraph_connected i).exists_walk_length_eq_dist v u
      obtain ⟨O, hO, hOc, hOs⟩ := exists_base_walk_operator S t p
      refine ⟨O, fun huv => ⟨hO, hOc, ?_⟩⟩
      intro q r hdist
      by_contra hn
      obtain ⟨w, hw⟩ := hOs r q hn
      have hbase : ((discGraph i).dist v u : ℝ) ≤ R := by
        change separatedDist discBoundaryBase ⟨i, u⟩ ⟨i, v⟩ ≤ R at huv
        rw [separatedDist_same, discGraphMetric_eq] at huv
        change ((discGraph i).dist u v : ℝ) ≤ R at huv
        rwa [SimpleGraph.dist_comm]
      have hlen : (p.length : ℝ) ≤ (⌈R⌉₊ : ℝ) := by
        rw [hp]
        exact hbase.trans (Nat.le_ceil R)
      have hup : dist (⟨⟨i, u⟩, q⟩ : VertexUnion) ⟨⟨i, v⟩, r⟩ ≤ s := by
        rw [dist_comm, vertexUnion_dist_same S t]
        exact (show ((fiberedGraph S t i).dist ⟨v, r⟩ ⟨u, q⟩ : ℝ) ≤ p.length by
          exact_mod_cast (SimpleGraph.dist_le w).trans_eq hw).trans (hlen.trans (le_max_left _ _))
      exact (not_lt_of_ge hup) hdist
    · refine ⟨constantMap ⟨i, u⟩ ⟨j, v⟩, fun huv =>
        ⟨constantMap_norm _ _, constantMap_constant _ _, ?_⟩⟩
      intro q r hdist
      have hidx := separatedDist_indices discBoundaryBase ⟨i, u⟩ ⟨j, v⟩ hij huv
      have hi : i ≤ ⌈R⌉₊ := by exact_mod_cast hidx.1.trans (Nat.le_ceil R)
      have hj : j ≤ ⌈R⌉₊ := by exact_mod_cast hidx.2.trans (Nat.le_ceil R)
      have hq : (⟨⟨i, u⟩, q⟩ : VertexUnion) ∈ W := by
        exact ⟨⟨i, ⟨u, q⟩⟩, (mem_componentPrefix _ _).mpr hi, rfl⟩
      have hr : (⟨⟨j, v⟩, r⟩ : VertexUnion) ∈ W := by
        exact ⟨⟨j, ⟨v, r⟩⟩, (mem_componentPrefix _ _).mpr hj, rfl⟩
      exact False.elim ((not_lt_of_ge ((hB hq hr).trans (le_max_right _ _))) hdist)
  choose O hO using hex
  exact ⟨s, hs, O, hO⟩

end CoarseAssembly

end

end OAI
