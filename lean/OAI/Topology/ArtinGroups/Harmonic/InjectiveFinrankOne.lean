import Mathlib

namespace OAI

namespace HarmonicArtin
variable {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

lemma injective_of_finrank_le_one (h : Module.finrank K W ≤ 1)
    (L : W →ₗ[K] K) (u : W) (hu : L u ≠ 0) : Function.Injective L := by
  obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := K) (V := W)).mp h
  have hv' : L v ≠ 0 := by
    obtain ⟨c, rfl⟩ := hv u
    intro hh
    apply hu
    rw [map_smul, hh, smul_zero]
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro w hw
  change L w = 0 at hw
  change w = 0
  obtain ⟨c, rfl⟩ := hv w
  have hc : c = 0 := by
    rw [map_smul, smul_eq_mul] at hw
    exact (mul_eq_zero.mp hw).resolve_right hv'
  rw [hc, zero_smul]

end HarmonicArtin

end OAI
