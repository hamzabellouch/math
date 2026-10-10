import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusFiniteLength

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal Topology
open Filter
namespace Lech
universe u
variable (B E : Type u) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
  [CommRing E] [Algebra B E] [Module.Finite B E]
  (p : ℕ) [Fact p.Prime] [CharP B p]

 

theorem exists_frobenius_tensor_transfer
    (hfaithful : ∀ g : B, g ≠ 0 → g • (LinearMap.id : E →ₗ[B] E) ≠ 0) :
    ∃ r : ℕ, 0 < r ∧ ∀ (M : ModuleCat.{u} B), IsFiniteLength B M → ∀ a : ℝ≥0∞,
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (FrobeniusModule B p n M)).toENNReal) atTop (𝓝 a) →
      Tendsto (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹ *
        (Module.length B (E ⊗[B] (FrobeniusModule B p n M))).toENNReal)
        atTop (𝓝 ((r : ℝ≥0∞)*a)) := by
  obtain ⟨r,hr,h⟩ := finite_module_tensor_asymptoticENN B E hfaithful
  refine ⟨r,hr,?_⟩
  intro M hM a ha
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨I,hI,hIM⟩ := finiteLength_primary_annihilator hM
  obtain ⟨b,f,hf⟩ := Module.Finite.exists_fin' B M
  have ht := h (fun n => FrobeniusModule B p n M)
    (fun n => I.map (iterateFrobenius B p n))
    (fun n => ((p : ℝ≥0∞)^(n*Lech.dimension B))⁻¹) a b
    (fun n => Module.length_ne_top_iff.mpr (frobeniusModule_finiteLength B p M hM n))
    (fun n => frobeniusModule_annihilator B p M I hIM n)
    (fun n => frobeniusModule_generators B p M f hf n) ha
    (fun g hg => Lech.FrobeniusGrowth.frobenius_error_tendstoENNReal I hI
      (mem_nonZeroDivisors_iff_ne_zero.mpr hg) p)
  apply ht.congr
  intro n
  congr 1
  exact congrArg ENat.toENNReal (TensorProduct.comm B (FrobeniusModule B p n M) E).length_eq
end Lech

end

end OAI
