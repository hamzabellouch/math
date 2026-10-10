import OAI.Topology.CoarseAssembly.ControlledRipsCycles

namespace OAI

/-! # The analytic coordinates of a controlled family class -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r : ℝ}

def controlledCoordinateFree (i : ℕ) :
    FreeAbelianGroup (ControlledCycleFamily Q r) →+ OddK C(Point (Q i) r, ℂ) :=
  FreeAbelianGroup.lift (fun c => cycleClass _ (c.cycle i))

theorem controlledCoordinateFree_relation (i : ℕ)
    {z : FreeAbelianGroup (ControlledCycleFamily Q r)} (hz : ControlledCycleRelation z) :
    controlledCoordinateFree i z = 0 := by
  cases hz with
  | degenerate c h =>
    simpa only [controlledCoordinateFree, FreeAbelianGroup.lift_apply_of] using
      degenerate_zero (c.cycle i) (h i)
  | unitary c d h =>
    simp only [controlledCoordinateFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (unitary_eq _ _ (h i))
  | directSum c d e h =>
    simp only [controlledCoordinateFree, map_sub, map_add, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (directSum_eq _ _ _ (h i))
  | homotopy h =>
    simp only [controlledCoordinateFree, map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (homotopy_eq (h.homotopy i))

/-- Ordinary analytic K-homology of each compact component. Injectivity or
surjectivity of the resulting coordinate family is not asserted here. -/
def controlledCoordinate (i : ℕ) : ControlledK Q r →+ OddK C(Point (Q i) r, ℂ) :=
  QuotientAddGroup.lift (controlledRelations Q r) (controlledCoordinateFree i)
    ((AddSubgroup.closure_le _).2 (fun _ hz => controlledCoordinateFree_relation i hz))

@[simp] theorem controlledCoordinate_class (i : ℕ) (c : ControlledCycleFamily Q r) :
    controlledCoordinate i (controlledClass c) = cycleClass _ (c.cycle i) :=
  FreeAbelianGroup.lift_apply_of _ _

end CoarseAssembly.Rips

end

end OAI
