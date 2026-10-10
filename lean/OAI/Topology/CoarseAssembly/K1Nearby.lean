import OAI.Topology.CoarseAssembly.K1TwoByTwo
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! # A concrete short path between nearby invertibles -/

noncomputable section

namespace CoarseAssembly.TopologicalK1

open Analytic

variable {A : Type*} [CStarAlgebra A]

def nearbyUnitPath (u v : Aˣ) (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹)
    (t : Interval) : Aˣ :=
  Units.ofNearby u ((u : A) + (t : ℝ) • ((v : A) - u)) (by
    rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg t.property.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) t.property.2).trans_lt h)

theorem nearbyUnitPath_continuous (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : Continuous (nearbyUnitPath u v h) := by
  apply (Units.isOpenEmbedding_val (R := A)).isEmbedding.continuous_iff.mpr
  change Continuous (fun t : Interval => (u : A) + (t : ℝ) • ((v : A) - u))
  exact continuous_const.add (continuous_subtype_val.smul continuous_const)

@[simp] theorem nearbyUnitPath_start (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : nearbyUnitPath u v h start = u := by
  apply Units.ext
  change (u : A) + (0 : ℝ) • ((v : A) - u) = u
  simp

@[simp] theorem nearbyUnitPath_finish (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) : nearbyUnitPath u v h finish = v := by
  apply Units.ext
  change (u : A) + (1 : ℝ) • ((v : A) - u) = v
  simp

theorem continuous_scalarUnitMatrix : Continuous (scalarUnitMatrix (R := A)) := by
  apply Continuous.units_map
  exact continuous_pi (fun i => continuous_pi (fun j => by
    change Continuous (fun x : A => if i = j then x else 0)
    split_ifs <;> fun_prop))

theorem matrixClass_scalar_eq_of_nearby (u v : Aˣ)
    (h : ‖(v : A) - u‖ < ‖(↑u⁻¹ : A)‖⁻¹) :
    matrixClass A (scalarUnitMatrix u) = matrixClass A (scalarUnitMatrix v) := by
  have hp := matrixClass_homotopy (fun t => scalarUnitMatrix (nearbyUnitPath u v h t))
    (continuous_scalarUnitMatrix.comp (nearbyUnitPath_continuous u v h))
  simpa only [nearbyUnitPath_start, nearbyUnitPath_finish] using hp

end CoarseAssembly.TopologicalK1

end

end OAI
