import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.CongruenceMaps
import OAI.Topology.CoarseAssembly.LatticeCharge
import OAI.Topology.CoarseAssembly.ChosenHolonomy

namespace OAI

/-! # The actual finite graph with congruence fibers

The inter-fiber edge relation is written at the common shallower level.
This uniformly describes the equal-depth, parent and child cases. The
generating set is symmetrized and contains the identity to record pure
base moves in a common list of left/right operations.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

theorem one_mem_symmetricMoves (S : Finset ArithmeticGroup) : 1 ∈ symmetricMoves S := by
  simp [symmetricMoves]

theorem inv_mem_symmetricMoves {S : Finset ArithmeticGroup} {s : ArithmeticGroup}
    (h : s ∈ symmetricMoves S) : s⁻¹ ∈ symmetricMoves S := by
  simp only [symmetricMoves, Finset.mem_insert, Finset.mem_union, Finset.mem_image] at *
  rcases h with h | h | ⟨a, ha, rfl⟩
  · left; simp [h]
  · exact Or.inr (Or.inr ⟨s, h, rfl⟩)
  · exact Or.inr (Or.inl (by simpa using ha))

abbrev fiberLevel {j : ℕ} (x y : FiberVertex j) : ℕ :=
  min (discDepth j x.1) (discDepth j y.1)

theorem liftStep_of_common {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    {x y : FiberVertex j} (s : ArithmeticGroup) (hs : s ∈ symmetricMoves S)
    (hp : x.1 = y.1 ∨ (discGraph j).Adj x.1 y.1 ∧ s = 1)
    (he : fiberCoordinate y (min_le_right _ _) =
      reduce (fiberLevel x y) s * fiberCoordinate x (min_le_left _ _) *
        holonomy t (fiberLevel x y) ^ fiberCharge x y) :
    LiftStep S t x y := by
  refine ⟨s, hs, hp, ?_⟩
  intro l hx hy
  have hm : l ≤ fiberLevel x y := le_min hx hy
  have hred := congrArg (fun q : Quotient (fiberLevel x y) => quotientMap hm q) he
  change quotientMap hm (quotientMap (min_le_right _ _) y.2) =
    quotientMap hm (reduce (fiberLevel x y) s *
      quotientMap (min_le_left _ _) x.2 * holonomy t (fiberLevel x y) ^ fiberCharge x y)
    at hred
  simpa only [map_mul, map_zpow, quotientMap_comp, quotientMap_reduce,
    quotientMap_holonomy, fiberCoordinate] using hred

theorem liftStep_reverse {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    {x y : FiberVertex j} (h : LiftStep S t x y) : LiftStep S t y x := by
  obtain ⟨s, hs, hp, he⟩ := h
  refine ⟨s⁻¹, inv_mem_symmetricMoves hs, ?_, ?_⟩
  · rcases hp with hp | ⟨hp, rfl⟩
    · exact Or.inl hp.symm
    · exact Or.inr ⟨hp.symm, inv_one⟩
  · intro l hy hx
    have hc : fiberCharge y x = -fiberCharge x y := latticeCharge_reverse _ _
    rw [hc, map_inv, zpow_neg, he l hx hy]
    group

theorem fiberedGraph_projects {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x y : FiberVertex j) (h : (fiberedGraph S t j).Adj x y) :
    x.1.val = y.1.val ∨ triangularGraph.Adj x.1.val y.1.val := by
  obtain ⟨s, hs, hp, he⟩ := h.2
  exact hp.elim (fun e => Or.inl (congrArg Subtype.val e)) (fun e => Or.inr e.1)

/-- An edge has the same left/right description at every lower common level. -/
theorem liftStep_reduce {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j l : ℕ}
    {x y : FiberVertex j} (h : LiftStep S t x y)
    (hx : l ≤ discDepth j x.1) (hy : l ≤ discDepth j y.1) :
    ∃ s ∈ symmetricMoves S,
      fiberCoordinate y hy = reduce l s * fiberCoordinate x hx *
        holonomy t l ^ fiberCharge x y := by
  obtain ⟨s, hs, hp, he⟩ := h
  exact ⟨s, hs, he l hx hy⟩

/-- Record every edge of a walk as an integral left move and a ray charge,
after reducing all its coordinates to one common level. -/
theorem walk_reduced_lift {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    {u v : FiberVertex j} (p : (fiberedGraph S t j).Walk u v) (l : ℕ)
    (hp : ∀ w ∈ p.support, l ≤ discDepth j w.1) :
    ∃ steps : List (ArithmeticGroup × ℤ),
      steps.length = p.length ∧
      holonomyCharge steps = walkCharge fiberCharge p ∧
      (∀ s ∈ steps, s.1 ∈ symmetricMoves S ∧ s.2.natAbs ≤ 1) ∧
      holonomyEndpoint (holonomy t l) (reduceSteps l steps)
          (fiberCoordinate u (hp u p.start_mem_support)) =
        fiberCoordinate v (hp v p.end_mem_support) := by
  induction p with
  | nil => exact ⟨[], rfl, rfl, by simp, rfl⟩
  | @cons u v w h p ih =>
    have ht : ∀ z ∈ p.support, l ≤ discDepth j z.1 :=
      fun z hz => hp z (by simp [hz])
    obtain ⟨s, hs, he⟩ := liftStep_reduce h.2 (hp u (by simp))
      (hp v (by simp))
    obtain ⟨steps, hlen, hcharge, hsteps, hend⟩ := ih ht
    refine ⟨(s, fiberCharge u v) :: steps, ?_, ?_, ?_, ?_⟩
    · simpa only [List.length_cons, SimpleGraph.Walk.length_cons] using congrArg (· + 1) hlen
    · simp only [holonomyCharge, walkCharge_cons, hcharge]
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · refine ⟨hs, ?_⟩
        simp only [fiberCharge, latticeCharge]
        split_ifs <;> norm_num
      · exact hsteps a ha
    · simpa only [reduceSteps, List.map_cons, holonomyEndpoint, ← he] using hend

/-- The manuscript's small-loop assertion for the actual finite fibered
graphs. The radius estimate supplies a common deep quotient; arithmetic
trace separation then forces the ray charge to vanish. -/
theorem fiberedGraph_short_loops (S : Finset ArithmeticGroup) (A : ℕ) :
    ∃ J : ℕ, ∀ j, J ≤ j → ∀ u : FiberVertex j,
      ∀ p : (fiberedGraph S chosenHolonomyUnit j).Walk u u,
        p.length ≤ A → walkCharge fiberCharge p = 0 := by
  obtain ⟨N, hN, hsep⟩ := chosenHolonomy_short_lifts (symmetricMoves S) A
  refine ⟨N + A / 2, ?_⟩
  intro j hj u p hlen
  by_contra hc
  have hdepth : ∀ w ∈ p.support, N ≤ discDepth j w.1 := by
    intro w hw
    have hr := charged_walk_all_radius_bound (fun v : FiberVertex j => v.1.val)
      (fiberedGraph_projects) p hc hw
    have hd := discDepth_int j w.1
    omega
  obtain ⟨steps, hstepslen, hcharge, hsteps, hend⟩ := walk_reduced_lift p N hdepth
  have hz := hsep N le_rfl (fiberCoordinate u (hdepth u p.start_mem_support))
    steps (hstepslen.trans_le hlen) hsteps hend
  exact hc (hcharge ▸ hz)

end CoarseAssembly

end

end OAI
