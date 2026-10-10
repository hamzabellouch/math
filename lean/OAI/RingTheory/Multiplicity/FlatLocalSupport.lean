import Mathlib
import OAI.RingTheory.Multiplicity.SubalgebraStageFromBase

namespace OAI

noncomputable section
namespace Lech
open IsLocalRing
variable {R S : Type*} [CommRing R] [CommRing S]
    [IsNoetherianRing R] [IsNoetherianRing S]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]

lemma ringKrullDim_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    ringKrullDim S = ringKrullDim R := by
  have hh := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal S)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at hh
  simpa only [maximalIdeal_height_eq_ringKrullDim] using congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) hh

omit [IsNoetherianRing R] [IsNoetherianRing S] in
lemma colength_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) (n : ℕ) :
    colength S n = colength R n := by
  have : IsSimpleModule S (S ⧸ maximalIdeal S) :=
    isSimpleModule_iff_quot_maximal.mpr
      ⟨maximalIdeal S, inferInstance, ⟨LinearEquiv.refl S _⟩⟩
  have he := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
    ((maximalIdeal R)^n)).toLinearEquiv.length_eq
  rw [Ideal.map_pow, h] at he
  rw [IsLocalRing.length_baseChange R S (R ⧸ (maximalIdeal R)^n), h,
    Module.length_eq_one (R := S) (M := S ⧸ maximalIdeal S), mul_one] at he
  exact congrArg ENat.toNat he

lemma multiplicity_eq_of_map_maximalIdeal
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    multiplicity S = multiplicity R := by
  have hd : dimension S = dimension R := by
    unfold dimension
    rw [ringKrullDim_eq_of_map_maximalIdeal h]
  have hn : normalizedColength S = normalizedColength R := by
    funext n
    unfold normalizedColength
    rw [hd, colength_eq_of_map_maximalIdeal h]
  unfold multiplicity
  rw [hn]
end Lech

end

end OAI
