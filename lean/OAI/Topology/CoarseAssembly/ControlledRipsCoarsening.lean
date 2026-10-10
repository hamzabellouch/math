import OAI.Topology.CoarseAssembly.ControlledRipsCoordinates
import OAI.Topology.CoarseAssembly.RipsScaleCompatibility

namespace OAI

/-! # Coarsening and the constructed controlled assembly homomorphism -/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic

variable {Q : ℕ → Type} [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)] {r s : ℝ}

def ControlledCycleFamily.coarsen (hrs : r ≤ s) (c : ControlledCycleFamily Q r) :
    ControlledCycleFamily Q s where
  cycle i := coarsenedCycle hrs (c.cycle i)
  unital i := coarsenedCycle_unital hrs (c.cycle i) (c.unital i)
  selfAdjoint := c.selfAdjoint
  bound := c.bound
  bound_nonneg := c.bound_nonneg
  norm_le := c.norm_le

def ControlledFamilyHomotopy.coarsen (hrs : r ≤ s) (h : ControlledFamilyHomotopy Q r) :
    ControlledFamilyHomotopy Q s where
  homotopy i := (h.homotopy i).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom
  unital t i := coarsenedCycle_unital hrs ((h.homotopy i).eval t) (h.unital t i)
  selfAdjoint := h.selfAdjoint
  bound := h.bound
  bound_nonneg := h.bound_nonneg
  norm_le := h.norm_le
  operator_continuous := h.operator_continuous
  partition_continuous := h.partition_continuous

theorem ControlledFamilyHomotopy.coarsen_eval (hrs : r ≤ s)
    (h : ControlledFamilyHomotopy Q r) (t : Interval) :
    (h.coarsen hrs).eval t = (h.eval t).coarsen hrs := rfl

theorem controlled_coarsen_relation (hrs : r ≤ s)
    {z : FreeAbelianGroup (ControlledCycleFamily Q r)} (hz : ControlledCycleRelation z) :
    FreeAbelianGroup.lift (fun c => controlledClass (c.coarsen hrs)) z = 0 := by
  cases hz with
  | degenerate c h =>
    have hz := controlled_relation_zero (ControlledCycleRelation.degenerate (c.coarsen hrs)
      (fun i => (h i).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom))
    simpa only [FreeAbelianGroup.lift_apply_of, controlledClass] using hz
  | unitary c d h =>
    have hz := controlled_relation_zero (ControlledCycleRelation.unitary (c.coarsen hrs) (d.coarsen hrs)
      (fun i => (h i).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom))
    simpa only [map_sub, FreeAbelianGroup.lift_apply_of, controlledClass,
      QuotientAddGroup.mk_sub] using hz
  | directSum c d e h =>
    have hz := controlled_relation_zero (ControlledCycleRelation.directSum
      (c.coarsen hrs) (d.coarsen hrs) (e.coarsen hrs)
      (fun i => (h i).precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom))
    simpa only [map_sub, map_add, FreeAbelianGroup.lift_apply_of, controlledClass,
      QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] using hz
  | homotopy h =>
    have hz := controlled_relation_zero (ControlledCycleRelation.homotopy (h.coarsen hrs))
    simpa only [map_sub, FreeAbelianGroup.lift_apply_of, controlledClass,
      QuotientAddGroup.mk_sub, ControlledFamilyHomotopy.coarsen_eval] using hz

def controlledCoarsening (hrs : r ≤ s) : ControlledK Q r →+ ControlledK Q s :=
  QuotientAddGroup.lift (controlledRelations Q r)
    (FreeAbelianGroup.lift (fun c => controlledClass (c.coarsen hrs)))
    ((AddSubgroup.closure_le _).2 (fun _ hz => controlled_coarsen_relation hrs hz))

@[simp] theorem controlledCoarsening_class (hrs : r ≤ s) (c : ControlledCycleFamily Q r) :
    controlledCoarsening hrs (controlledClass c) = controlledClass (c.coarsen hrs) :=
  FreeAbelianGroup.lift_apply_of _ _

theorem controlled_hom_ext {D : Type*} [AddCommGroup D]
    (f g : ControlledK Q r →+ D)
    (h : ∀ c, f (controlledClass c) = g (controlledClass c)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

omit [∀ i, DecidableEq (Q i)] in
@[simp] theorem ControlledCycleFamily.coarsen_refl (c : ControlledCycleFamily Q r) :
    c.coarsen le_rfl = c := by
  cases c
  rfl

omit [∀ i, DecidableEq (Q i)] in
theorem ControlledCycleFamily.coarsen_comp {t : ℝ} (hrs : r ≤ s) (hst : s ≤ t)
    (c : ControlledCycleFamily Q r) :
    (c.coarsen hrs).coarsen hst = c.coarsen (hrs.trans hst) := by
  cases c
  rfl

@[simp] theorem controlledCoarsening_refl :
    controlledCoarsening (Q := Q) (r := r) le_rfl = AddMonoidHom.id (ControlledK Q r) := by
  apply controlled_hom_ext
  intro c
  simp only [controlledCoarsening_class, ControlledCycleFamily.coarsen_refl,
    AddMonoidHom.id_apply]

theorem controlledCoarsening_comp {t : ℝ} (hrs : r ≤ s) (hst : s ≤ t) :
    (controlledCoarsening (Q := Q) hst).comp (controlledCoarsening hrs) =
      controlledCoarsening (hrs.trans hst) := by
  apply controlled_hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, controlledCoarsening_class,
    ControlledCycleFamily.coarsen_comp]

/-- Scale compatibility holds for the whole constructed map on the quotient,
not only for its chosen cycle representatives. -/
theorem controlledAssembly_coarsening (o : ∀ i, Q i) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hrs : r ≤ s) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ
        (DiscreteRoe.algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) := inferInstance
    (controlledAssembly o hs).comp (controlledCoarsening hrs) = controlledAssembly o hr := by
  let := separatedMetric o
  let : Ring (Unitization ℂ
      (DiscreteRoe.algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) := inferInstance
  apply controlled_hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, controlledCoarsening_class, controlledAssembly_class]
  exact ampleRipsFamilyBoundary_scale hrs o hr hs c.cycle c.unital c.selfAdjoint
    c.bound c.bound_nonneg c.norm_le

theorem controlledCoordinate_coarsening (i : ℕ) (hrs : r ≤ s) :
    (controlledCoordinate i).comp (controlledCoarsening (Q := Q) hrs) =
      (Analytic.precomp (scaleFunctionHom hrs).toNonUnitalStarAlgHom).comp
        (controlledCoordinate i) := by
  apply controlled_hom_ext
  intro c
  simp only [AddMonoidHom.comp_apply, controlledCoarsening_class, controlledCoordinate_class,
    Analytic.precomp_cycleClass]
  rfl

end CoarseAssembly.Rips

end

end OAI
