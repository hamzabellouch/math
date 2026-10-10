import Mathlib
import OAI.RingTheory.Multiplicity.SubalgebraStageFromBase

namespace OAI

noncomputable section
open scoped Topology
namespace Lech
open IsLocalRing Filter
lemma dimension_eq_zero_of_artinian (R : Type*) [CommRing R]
    [IsLocalRing R] [IsArtinianRing R] : dimension R = 0 := by
  have hk : ringKrullDim R = 0 :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mp inferInstance
  simp [dimension,hk]

lemma multiplicity_eq_length_of_artinian (R : Type*) [CommRing R]
    [IsLocalRing R] [IsArtinianRing R] :
    multiplicity R = ((Module.length R R).toNat : ℝ) := by
  obtain ⟨a,ha⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal R).mp inferInstance
  have he : normalizedColength R =ᶠ[atTop]
      fun _ => ((Module.length R R).toNat : ℝ) := by
    filter_upwards [eventually_ge_atTop a] with n hn
    have hp : (maximalIdeal R)^n = ⊥ := pow_eq_zero_of_le hn ha
    have hlen : Module.length R (R ⧸ (maximalIdeal R)^n) = Module.length R R := by
      rw [hp]
      exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
    simp [normalizedColength,dimension_eq_zero_of_artinian,colength,hlen]
  exact (tendsto_const_nhds.congr' he.symm).limUnder_eq

end Lech

end

end OAI
