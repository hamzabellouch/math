import Mathlib
import OAI.RingTheory.Multiplicity.ScalarExtensionHomotopy

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech
universe u
variable {R : Type u} [CommRing R]

lemma finite_shortComplex_homology [IsNoetherianRing R]
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.X₂] :
    Module.Finite R S.homology := by
  let : Module.Finite R S.moduleCatLeftHomologyData.H := by
    change Module.Finite R ((LinearMap.ker S.g.hom) ⧸ LinearMap.range S.moduleCatToCycles)
    infer_instance
  exact Module.Finite.equiv S.moduleCatHomologyIso.toLinearEquiv.symm

lemma finite_cochain_homology [IsNoetherianRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) [Module.Finite R (F.X i)] :
    Module.Finite R (F.homology i) := by
  let : Module.Finite R (F.sc i).X₂ := by
    change Module.Finite R (F.X i)
    infer_instance
  exact finite_shortComplex_homology (F.sc i)

lemma shortComplex_nullScalar_radical [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    IsLocalRing.maximalIdeal R ≤ (Koszul.nullScalarIdeal F).radical := by
  intro x hx
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R : ℤ)) (dimension R+1)
    (fun i => by have := hF.term_free i; infer_instance)
    (fun i hi => hF.bounded i (by omega)) hF.homology_finite_length x hx
  exact ⟨a,ha⟩

 

lemma shortComplex_uniform_nullhomotopy [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) :
    ∃ a : ℕ, 0 < a ∧ (IsLocalRing.maximalIdeal R)^a ≤ Koszul.nullScalarIdeal F := by
  obtain ⟨a,ha⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (shortComplex_nullScalar_radical F hF)
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  exact ⟨a+1,by omega,(Ideal.pow_le_pow_right (Nat.le_succ a)).trans ha⟩

lemma finiteLength_of_maximal_le_radical_annihilator [IsLocalRing R] [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IsLocalRing.maximalIdeal R ≤ (Module.annihilator R M).radical) :
    IsFiniteLength R M := by
  apply finiteLength_of_primary_annihilator
    (Module.annihilator R M ⊓ IsLocalRing.maximalIdeal R) _ inf_le_left
  rw [Ideal.radical_inf,(IsLocalRing.maximalIdeal.isMaximal R).isPrime.radical,
    inf_eq_right.mpr hM]

 
theorem frobenius_shortComplex_homology_finiteLength
    [IsLocalRing R] [IsNoetherianRing R] (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F) (n : ℕ) (i : ℤ) :
    IsFiniteLength R ((frobeniusComplex R p n F).homology i) := by
  have := hF.term_finite i
  have : Module.Finite R ((frobeniusComplex R p n F).X i) :=
    finite_extendScalars (iterateFrobenius R p n) (F.X i)
  have := finite_cochain_homology (frobeniusComplex R p n F) i
  apply finiteLength_of_maximal_le_radical_annihilator
  intro x hx
  obtain ⟨a,ha⟩ := ProjectiveGhost.exists_nullhomotopy_power F
    (-(dimension R : ℤ)) (dimension R+1)
    (fun j => by have := hF.term_free j; infer_instance)
    (fun j hj => hF.bounded j (by omega)) hF.homology_finite_length x hx
  refine ⟨a*(p^n),?_⟩
  exact Koszul.scalar_annihilates_homology (frobeniusComplex R p n F) (x^(a*(p^n)))
    (frobenius_nullhomotopy p n a F x ha.some) i
end Lech

end

end OAI
