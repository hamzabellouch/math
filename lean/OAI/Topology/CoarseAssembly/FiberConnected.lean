import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.DiscConnected
import OAI.Topology.CoarseAssembly.PathFiberOperators

namespace OAI

/-! # Connectivity of the finite fibered graphs

Transport from a singleton boundary fiber reaches every vertex: its image
is the normalized constant vector, which has no zero coordinate. Thus
connectivity does not require an additional Cayley-generation assumption.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

@[simp] theorem discBoundaryBase_depth (j : ℕ) :
    discDepth j (discBoundaryBase j) = 0 := by
  simp [discDepth, discBoundaryBase, latticeRadius]

private theorem constant_coordinate_ne_zero (k : ℕ) (q : Quotient k) :
    fiberConstant (Quotient k) (1 : ℂ) q ≠ 0 := by
  have hc : (0 : ℝ) < Fintype.card (Quotient k) := by exact_mod_cast Fintype.card_pos
  have hn : fiberNormalization (Quotient k) ≠ 0 :=
    inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc))
  simpa only [fiberConstant_apply, smul_eq_mul, mul_one, ne_eq, Complex.ofReal_eq_zero] using hn

theorem fiberBoundary_reaches (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    (fiberedGraph S t j).Reachable (fiberBoundaryBase j) x := by
  classical
  have hsub : Subsingleton (Quotient (discDepth j (discBoundaryBase j))) := by
    rw [discBoundaryBase_depth]
    infer_instance
  let : Unique (Quotient (discDepth j (discBoundaryBase j))) :=
    ⟨⟨1⟩, fun q => hsub.elim q 1⟩
  have hc : fiberConstant (Quotient (discDepth j (discBoundaryBase j))) (1 : ℂ) =
      lp.single 2 1 1 := by
    apply lp.ext
    funext q
    simp [fiberConstant_apply, lp.single_apply, hsub.elim q 1]
  obtain ⟨p⟩ := discGraph_connected j (discBoundaryBase j) x.1
  obtain ⟨O, hnorm, hconst, hsupp⟩ := exists_base_walk_operator S t p
  have hn : O (lp.single 2 1 1) x.2 ≠ 0 := by
    rw [← hc, hconst]
    exact constant_coordinate_ne_zero _ _
  obtain ⟨w, hw⟩ := hsupp 1 x.2 hn
  exact ⟨w⟩

theorem fiberedGraph_connected (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) (j : ℕ) :
    (fiberedGraph S t j).Connected where
  preconnected x y :=
    (fiberBoundary_reaches S t x).symm.trans (fiberBoundary_reaches S t y)
  nonempty := ⟨fiberBoundaryBase j⟩

end CoarseAssembly

end

end OAI
