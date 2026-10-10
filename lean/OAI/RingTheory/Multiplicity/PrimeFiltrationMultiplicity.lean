import Mathlib
import OAI.RingTheory.Multiplicity.PrimeFiltrationEuler

namespace OAI

noncomputable section
open Filter IsLocalRing
open scoped Topology
namespace Lech.PrimeFiltration
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
omit [IsNoetherianRing R] [IsLocalRing R] in
lemma colength_self (I : Ideal R) (n : ℕ) :
    ArtinReesLength.colength I R n=Primary.colength I n := by
  unfold ArtinReesLength.colength Primary.colength
  rw [Ideal.smul_eq_mul,Ideal.mul_top]

lemma Factors.multiplicity_self {ps : List (Ideal R)} (h : Factors (⊥ : Submodule R R) ps) :
    multiplicity R=(ps.map (fun P => ((dimension R).factorial:ℝ)*contribution (maximalIdeal R) P)).sum := by
  have hl := h.colength_limit (maximalIdeal R) (Ideal.IsPrime.radical inferInstance)
  simp only [ArtinReesLength.colength_equiv (maximalIdeal R) (Submodule.quotEquivOfEqBot _ rfl),
    colength_self] at hl
  have hu := primary_unscaled_limit (maximalIdeal R) (Ideal.IsPrime.radical inferInstance)
  have he := tendsto_nhds_unique hu hl
  rw [Primary.maximal_multiplicity_eq] at he
  rw [List.sum_map_mul_left]
  have hfac : ((dimension R).factorial:ℝ) ≠ 0 := by positivity
  rw [←he]
  field_simp
end Lech.PrimeFiltration

end

end OAI
