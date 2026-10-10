import Mathlib
import OAI.Topology.Homotopy.HomotopyFiber
import OAI.Topology.Homotopy.LoopHomotopy

namespace OAI

/-! Nontrivial homotopy kernels from finite cardinality bounds. -/

noncomputable section
universe u v w


namespace NearbyLagrangian.HomotopyFiber
open ContinuousMap
open scoped Topology Topology.Homotopy
open BasedHomotopy
variable {N X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable [DecidableEq N] [Nonempty N]

theorem nontrivial_kernel_of_large_fiber (e : C(X,Y)) (x : X)
    {K : Type*} [Fintype K]
    [Fintype (HomotopyGroup N (Path (e x) (e x)) (Path.refl (e x)))]
    (ι : K ↪ HomotopyGroup N (Fiber e (e x)) (base e x))
    (hcard : Fintype.card (HomotopyGroup N (Path (e x) (e x)) (Path.refl (e x))) < Fintype.card K) :
    ∃ a : HomotopyGroup N X x, a ≠ 1 ∧ groupMap e rfl a = 1 := by
  classical
  suffices h : ∃ k, groupMap (projection e (e x)) rfl (ι k) ≠ 1 by
    obtain ⟨k,hk⟩ := h
    exact ⟨groupMap (projection e (e x)) rfl (ι k),hk,
      (kernel_eq_projection_range e x _).mpr ⟨ι k,rfl⟩⟩
  by_contra! h
  choose q hq using fun k => (projection_kernel_eq_loop_range e x (ι k)).mp (h k)
  have hi : Function.Injective q := by
    intro k l hkl
    apply ι.injective
    have hk := hq k
    rw [hkl] at hk
    exact hk.symm.trans (hq l)
  exact (Nat.not_le_of_lt hcard) (Fintype.card_le_of_injective q hi)

theorem nontrivial_pi9_kernel_of_source_sizes (e : C(X,Y)) (x : X)
    (sphereCalculation : π_ 10 Y (e x) ≃ (Fin 3 → ZMod 2))
    (whiteheadClasses : (ZMod 8 × (ZMod 2 × ZMod 2)) ↪
      π_ 9 (Fiber e (e x)) (base e x)) :
    ∃ a : π_ 9 X x, a ≠ 1 ∧ groupMap e rfl a = 1 := by
  let calculation := (pi9LoopEquivPi10 (e x)).trans sphereCalculation
  let : Fintype (π_ 9 (Path (e x) (e x)) (Path.refl (e x))) :=
    Fintype.ofEquiv (Fin 3 → ZMod 2) calculation.symm
  apply nontrivial_kernel_of_large_fiber e x whiteheadClasses
  rw [Fintype.card_congr calculation]
  norm_num

end NearbyLagrangian.HomotopyFiber

end

end OAI
