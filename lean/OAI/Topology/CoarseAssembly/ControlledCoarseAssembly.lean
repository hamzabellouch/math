import OAI.Topology.CoarseAssembly.ControlledRipsCoarsening
import OAI.Topology.CoarseAssembly.Assembly

namespace OAI

/-! # The coarsening-limit assembly for controlled component families

This is the direct limit of the constructed analytic quotient maps. Relating
its source to full locally finite K-homology is a separate remaining theorem.
-/

noncomputable section

namespace CoarseAssembly.Rips

open Analytic DiscreteRoe

variable (Q : ℕ → Type) [∀ i, MetricSpace (Q i)] [∀ i, Fintype (Q i)]
  [∀ i, DecidableEq (Q i)]

def controlledScaleMap (r s : ℕ) (hrs : r ≤ s) : ControlledK Q (r : ℝ) →+ ControlledK Q (s : ℝ) :=
  controlledCoarsening (by exact_mod_cast hrs)

instance controlledDirectedSystem :
    DirectedSystem (fun r : ℕ => ControlledK Q (r : ℝ)) (fun r s h => controlledScaleMap Q r s h) where
  map_self r x := by
    change controlledCoarsening (Q := Q) (r := (r : ℝ)) le_rfl x = x
    rw [controlledCoarsening_refl]
    rfl
  map_map t s r hrs hst x := by
    change controlledCoarsening (Q := Q) (show (s : ℝ) ≤ t from by exact_mod_cast hst)
      (controlledCoarsening (show (r : ℝ) ≤ s from by exact_mod_cast hrs) x) = _
    exact DFunLike.congr_fun (controlledCoarsening_comp
      (show (r : ℝ) ≤ s from by exact_mod_cast hrs)
      (show (s : ℝ) ≤ t from by exact_mod_cast hst)) x

abbrev ControlledCoarseK := AddCommGroup.DirectLimit
  (fun r : ℕ => ControlledK Q (r : ℝ)) (fun r s h => controlledScaleMap Q r s h)

def controlledCoarseOf (r : ℕ) : ControlledK Q (r : ℝ) →+ ControlledCoarseK Q :=
  AddCommGroup.DirectLimit.of (fun r : ℕ => ControlledK Q (r : ℝ))
    (fun r s h => controlledScaleMap Q r s h) r

variable {Q}

/-- An actual compatible assembly map on the controlled component model. -/
def controlledCoarseAssembly (o : ∀ i, Q i) :
    letI := separatedMetric o
    letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
      inferInstance
    ControlledCoarseK Q →+ OperatorKTheory.K1 (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2)) := by
  letI := separatedMetric o
  letI : Ring (Unitization ℂ (algebra (X := Sigma Q) (H := lp (fun _ : ℕ => ℂ) 2))) :=
    inferInstance
  apply AddCommGroup.DirectLimit.lift _ _ _ (fun r => controlledAssembly o (Nat.cast_nonneg r))
  intro r s hrs x
  exact DFunLike.congr_fun (controlledAssembly_coarsening o (Nat.cast_nonneg r) (Nat.cast_nonneg s)
    (show (r : ℝ) ≤ s from by exact_mod_cast hrs)) x

@[simp] theorem controlledCoarseAssembly_of (o : ∀ i, Q i) (r : ℕ)
    (x : ControlledK Q (r : ℝ)) :
    controlledCoarseAssembly o (controlledCoarseOf Q r x) =
      controlledAssembly o (Nat.cast_nonneg r) x :=
  AddCommGroup.DirectLimit.lift_of _ _ _ _ _

@[simp] theorem controlledCoarseAssembly_cycle (o : ∀ i, Q i) (r : ℕ)
    (c : ControlledCycleFamily Q (r : ℝ)) :
    controlledCoarseAssembly o (controlledCoarseOf Q r (controlledClass c)) =
      c.boundary o (Nat.cast_nonneg r) := by
  exact (controlledCoarseAssembly_of o r (controlledClass c)).trans
    (controlledAssembly_class o (Nat.cast_nonneg r) c)

end CoarseAssembly.Rips

end

end OAI
