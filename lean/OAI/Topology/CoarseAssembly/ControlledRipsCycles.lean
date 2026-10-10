import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.RipsUniformHomotopy
import OAI.Topology.CoarseAssembly.RipsUnitaryFamily
import OAI.Topology.CoarseAssembly.RipsDirectSumBoundary
import OAI.Topology.CoarseAssembly.RipsBoundaryDegeneracy

namespace OAI

/-! # Controlled analytic cycles for the separated finite-component application

This intermediate cycle group retains uniform analytic homotopy control.
Its map to ordinary analytic coordinates is constructed explicitly; no
identification with the full locally finite analytic group is assumed.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe Filter Topology

variable (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] (r : ℝ)

structure ControlledFamilyHomotopy where
  homotopy : ∀ i, OddHomotopy C(Point (Q i) r, ℂ)
  unital : ∀ t i, ((homotopy i).eval t).representation 1 = 1
  selfAdjoint : ∀ t i, IsSelfAdjoint ((homotopy i).eval t).operator
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  norm_le : ∀ t i, ‖(homotopy i).operator t‖ ≤ bound
  operator_continuous : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
    ‖(homotopy i).operator s - (homotopy i).operator t‖ ≤ ε
  partition_continuous : ∀ t ε, 0 < ε → ∀ᶠ s in 𝓝 t, ∀ i,
    ‖(show (homotopy i).space →L[ℂ] Module (Q i) (homotopy i).space from
        partitionMap (representedSqrt r ((homotopy i).eval s))) -
      (show (homotopy i).space →L[ℂ] Module (Q i) (homotopy i).space from
        partitionMap (representedSqrt r ((homotopy i).eval t)))‖ ≤ ε

variable {Q r}

def ControlledFamilyHomotopy.eval (h : ControlledFamilyHomotopy Q r) (t : Interval) :
    ControlledCycleFamily Q r where
  cycle i := (h.homotopy i).eval t
  unital := h.unital t
  selfAdjoint := h.selfAdjoint t
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  norm_le := h.norm_le t

inductive ControlledCycleRelation : FreeAbelianGroup (ControlledCycleFamily Q r) → Prop
  | degenerate (c : ControlledCycleFamily Q r) (h : ∀ i, (c.cycle i).Degenerate) :
      ControlledCycleRelation (FreeAbelianGroup.of c)
  | unitary (c d : ControlledCycleFamily Q r)
      (h : ∀ i, (c.cycle i).UnitaryEquivalent (d.cycle i)) :
      ControlledCycleRelation (FreeAbelianGroup.of c - FreeAbelianGroup.of d)
  | directSum (c d e : ControlledCycleFamily Q r)
      (h : ∀ i, (c.cycle i).IsDirectSum (d.cycle i) (e.cycle i)) :
      ControlledCycleRelation (FreeAbelianGroup.of e - (FreeAbelianGroup.of c + FreeAbelianGroup.of d))
  | homotopy (h : ControlledFamilyHomotopy Q r) :
      ControlledCycleRelation (FreeAbelianGroup.of (h.eval start) - FreeAbelianGroup.of (h.eval finish))

def controlledRelations (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
    [∀ i, DecidableEq (Q i)] (r : ℝ) : AddSubgroup (FreeAbelianGroup (ControlledCycleFamily Q r)) :=
  AddSubgroup.closure {z | ControlledCycleRelation z}

abbrev ControlledK (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
    [∀ i, DecidableEq (Q i)] (r : ℝ) :=
  FreeAbelianGroup (ControlledCycleFamily Q r) ⧸ controlledRelations Q r

def controlledClass (c : ControlledCycleFamily Q r) : ControlledK Q r :=
  QuotientAddGroup.mk (FreeAbelianGroup.of c)

theorem controlled_relation_zero {z : FreeAbelianGroup (ControlledCycleFamily Q r)}
    (hz : ControlledCycleRelation z) : (QuotientAddGroup.mk z : ControlledK Q r) = 0 :=
  (QuotientAddGroup.eq_zero_iff z).2 (AddSubgroup.subset_closure hz)

def controlledBoundaryFree (o : ∀ i, Q i) (hr : 0 ≤ r) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    FreeAbelianGroup (ControlledCycleFamily Q r) →+
      OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) :=
  FreeAbelianGroup.lift (fun c => c.boundary o hr)

theorem controlledBoundaryFree_relation (o : ∀ i, Q i) (hr : 0 ≤ r)
    {z : FreeAbelianGroup (ControlledCycleFamily Q r)} (hz : ControlledCycleRelation z) :
    controlledBoundaryFree o hr z = 0 := by
  let := separatedMetric o
  cases hz with
  | degenerate c h =>
    simpa only [controlledBoundaryFree, FreeAbelianGroup.lift_apply_of,
      ControlledCycleFamily.boundary] using
      ampleRipsFamilyBoundary_degenerate o r hr c.cycle c.unital c.selfAdjoint
        c.bound c.bound_nonneg c.norm_le h
  | unitary c d h =>
    simp only [controlledBoundaryFree, map_sub, FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mpr
    exact ampleRipsFamilyBoundary_unitary o r hr c.cycle d.cycle h c.unital d.unital
      c.selfAdjoint d.selfAdjoint c.bound d.bound c.bound_nonneg d.bound_nonneg c.norm_le d.norm_le
  | directSum c d e h =>
    simp only [controlledBoundaryFree, map_sub, map_add, FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mpr
    exact ampleRipsFamilyBoundary_directSum o r hr c.cycle d.cycle e.cycle h
      c.unital d.unital e.unital c.selfAdjoint d.selfAdjoint e.selfAdjoint
      c.bound d.bound e.bound c.bound_nonneg d.bound_nonneg e.bound_nonneg c.norm_le d.norm_le e.norm_le
  | homotopy h =>
    simp only [controlledBoundaryFree, map_sub, FreeAbelianGroup.lift_apply_of]
    apply sub_eq_zero.mpr
    exact ampleRipsFamilyBoundary_uniformHomotopy o r hr h.homotopy h.unital h.selfAdjoint
      h.bound h.bound_nonneg h.norm_le h.operator_continuous h.partition_continuous

/-- The constructed whole-union Roe boundary descends through every relation
of this controlled analytic cycle model. -/
def controlledAssembly (o : ∀ i, Q i) (hr : 0 ≤ r) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    ControlledK Q r →+ OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) :=
  by
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    exact QuotientAddGroup.lift (controlledRelations Q r) (controlledBoundaryFree o hr)
      ((AddSubgroup.closure_le _).2 (fun _ hz => controlledBoundaryFree_relation o hr hz))

@[simp] theorem controlledAssembly_class (o : ∀ i, Q i) (hr : 0 ≤ r)
    (c : ControlledCycleFamily Q r) :
    controlledAssembly o hr (controlledClass c) = c.boundary o hr :=
  FreeAbelianGroup.lift_apply_of _ _

end CoarseAssembly.Rips

end

end OAI
