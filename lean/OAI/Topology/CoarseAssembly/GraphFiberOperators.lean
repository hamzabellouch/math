import OAI.Topology.CoarseAssembly.CongruenceEdgeOperators
import OAI.Topology.CoarseAssembly.FiberedGraph

namespace OAI

/-! # Controlled transport along the base graph

The three depth cases give actual contractions on the finite scalar Hilbert
spaces. Their nonzero coefficients are supported on edges of the constructed
fibered graph, not on an assumed transport relation.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

private theorem isometry_norm_le_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (V : E →ₗᵢ[ℂ] F) :
    ‖V.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [LinearIsometry.coe_toContinuousLinearMap, V.norm_map, one_mul] using le_rfl (a := ‖x‖)

/-- Transport between adjacent depths, with its exact reduced support. -/
theorem exists_depth_operator (t : ℤ_[2]ˣ) (k l : ℕ) (a : ℤ)
    (hkl : |(k : ℤ) - (l : ℤ)| ≤ 1) :
    ∃ O : lp (fun _ : Quotient k => ℂ) 2 →L[ℂ] lp (fun _ : Quotient l => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient k) (1 : ℂ)) =
        fiberConstant (Quotient l) 1 ∧
      ∀ q z, O (lp.single 2 q 1) z ≠ 0 →
        ∀ m (hm : m ≤ k) (hl : m ≤ l),
          quotientMap hl z = quotientMap hm q * holonomy t m ^ a := by
  have hcases : k = l ∨ l = k + 1 ∨ k = l + 1 := by
    rw [abs_le] at hkl
    omega
  rcases hcases with rfl | rfl | rfl
  · refine ⟨(sameLevelIsometry t k a).toLinearIsometry.toContinuousLinearMap,
      isometry_norm_le_one _, sameLevelIsometry_constant t k a, ?_⟩
    intro q z hn m hm hl
    have he : z = q * holonomy t k ^ a := by
      by_contra he
      exact hn (sameLevelIsometry_support t k a q z he)
    rw [he, map_mul, map_zpow, quotientMap_holonomy]
  · refine ⟨(childIsometry t k a).toContinuousLinearMap,
      isometry_norm_le_one _, childIsometry_constant t k a, ?_⟩
    intro q z hn m hm hl
    have he : quotientMap (Nat.le_succ k) z = q * holonomy t k ^ a := by
      by_contra he
      exact hn (childIsometry_support t k a q z he)
    have hr := congrArg (quotientMap hm) he
    simpa only [map_mul, map_zpow, quotientMap_holonomy, quotientMap_comp] using hr
  · refine ⟨(childIsometry t l (-a)).toContinuousLinearMap.adjoint, ?_,
      childAdjoint_constant t l (-a), ?_⟩
    · rw [LinearIsometryEquiv.norm_map]
      exact isometry_norm_le_one _
    · intro q z hn m hm hl
      have he : quotientMap (Nat.le_succ l) q = z * holonomy t l ^ (-a) := by
        by_contra he
        exact hn (childAdjoint_support t l (-a) z q he)
      have hz : z = quotientMap (Nat.le_succ l) q * holonomy t l ^ a := by
        rw [he, zpow_neg]
        group
      have hr := congrArg (quotientMap hl) hz
      simpa only [map_mul, map_zpow, quotientMap_holonomy, quotientMap_comp] using hr

/-- Each base edge has a contraction preserving constants, whose matrix
coefficients are supported on actual edges upstairs. -/
theorem exists_base_edge_operator (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} {u v : Disc j} (huv : (discGraph j).Adj u v) :
    ∃ O : lp (fun _ : Quotient (discDepth j u) => ℂ) 2 →L[ℂ]
        lp (fun _ : Quotient (discDepth j v) => ℂ) 2,
      ‖O‖ ≤ 1 ∧ O (fiberConstant (Quotient (discDepth j u)) (1 : ℂ)) =
        fiberConstant (Quotient (discDepth j v)) 1 ∧
      ∀ q z, ¬(fiberedGraph S t j).Adj ⟨u, q⟩ ⟨v, z⟩ →
        O (lp.single 2 q 1) z = 0 := by
  obtain ⟨O, hnorm, hconst, hsupp⟩ := exists_depth_operator t
    (discDepth j u) (discDepth j v) (latticeCharge u.val v.val) (discDepth_adj huv)
  refine ⟨O, hnorm, hconst, ?_⟩
  intro q z hnot
  by_contra hn
  apply hnot
  refine ⟨?_, 1, one_mem_symmetricMoves S, Or.inr ⟨huv, rfl⟩, ?_⟩
  · intro heq
    have huv' := congrArg (fun x : FiberVertex j => x.1.val) heq
    exact huv.2.2.2 huv'
  · intro m hm hl
    simpa only [fiberCoordinate, fiberCharge, map_one, one_mul] using hsupp q z hn m hm hl

end CoarseAssembly

end

end OAI
