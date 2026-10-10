import Mathlib.Algebra.AlgebraicCard
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.LinearCombination

namespace OAI

/-!
# A transcendental principal p-adic unit

The holonomy construction chooses a transcendental element of `1 + 2ℤ₂`.
The existence proof below works for every prime: algebraic elements form a
countable set, and the Baire theorem makes its complement dense in the
complete, perfect p-adic field.
-/

namespace CoarseAssembly

open Set

variable {p : ℕ} [Fact p.Prime]

/-- Transcendental elements over the integers are dense in the p-adic field. -/
theorem dense_padic_transcendental : Dense {x : ℚ_[p] | Transcendental ℤ x} := by
  have hcount : Set.Countable {x : ℚ_[p] | IsAlgebraic ℤ x} :=
    Algebraic.countable ℤ ℚ_[p]
  have hd : Dense (⋂ x ∈ {x : ℚ_[p] | IsAlgebraic ℤ x}, ({x}ᶜ : Set ℚ_[p])) :=
    dense_biInter_of_isOpen (fun _ _ => isOpen_compl_singleton) hcount
      (fun x _ => dense_compl_singleton x)
  apply hd.mono
  intro x hx hxalg
  have hxnot := Set.mem_iInter₂.mp hx x hxalg
  exact hxnot (Set.mem_singleton x)

/-- The exact principal-unit choice needed for diagonal holonomy exists.
The specialization `p = 2` lies in `1 + 2ℤ₂`. -/
theorem exists_transcendental_principal_unit :
    ∃ t : ℤ_[p]ˣ, Transcendental ℤ (t : ℤ_[p]) ∧
      ∃ a : ℤ_[p], (t : ℤ_[p]) = 1 + (p : ℤ_[p]) * a := by
  obtain ⟨x, hx, hclose⟩ :=
    (dense_padic_transcendental (p := p)).exists_dist_lt (1 : ℚ_[p]) zero_lt_one
  have hnear : ‖x - 1‖ < 1 := by
    simpa only [dist_eq_norm, norm_sub_rev] using hclose
  have hxnorm : ‖x‖ = 1 := by
    simpa only [norm_one] using Padic.norm_eq_of_norm_sub_lt_right
      (show ‖x - 1‖ < ‖(1 : ℚ_[p])‖ by simpa using hnear)
  let z : ℤ_[p] := ⟨x, hxnorm.le⟩
  have hznorm : ‖z‖ = 1 := hxnorm
  obtain ⟨t, ht⟩ := PadicInt.isUnit_iff.mpr hznorm
  refine ⟨t, ?_, ?_⟩
  · rw [ht]
    intro hzalg
    let f : ℤ_[p] →ₐ[ℤ] ℚ_[p] :=
      { PadicInt.Coe.ringHom with commutes' := fun n => by simp }
    exact hx (hzalg.algHom f)
  · have hzclose : ‖z - 1‖ < 1 := hnear
    obtain ⟨a, ha⟩ := (PadicInt.norm_lt_one_iff_dvd (z - 1)).mp hzclose
    refine ⟨a, ?_⟩
    rw [ht]
    linear_combination ha

end CoarseAssembly

end OAI
