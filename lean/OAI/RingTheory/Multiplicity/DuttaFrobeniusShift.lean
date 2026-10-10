import Mathlib
import OAI.RingTheory.Multiplicity.DuttaPerfectResidue
import OAI.RingTheory.Multiplicity.MinimalComplex

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p]

def frobeniusComplexAddIso (F : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℕ) :
    frobeniusComplex R p m (frobeniusComplex R p n F) ≅ frobeniusComplex R p (n+m) F := by
  have he : (iterateFrobenius R p m).comp (iterateFrobenius R p n) =
      iterateFrobenius R p (n+m) := by
    ext x
    change (x^(p^n))^(p^m) = x^(p^(n+m))
    rw [← pow_mul,← pow_add]
  have e := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (iterateFrobenius R p n) (iterateFrobenius R p m))
      (.up ℤ)).app F).symm
  rw [he] at e
  exact e

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaSequence_frobenius (F : CochainComplex (ModuleCat.{u} R) ℤ) (n m : ℕ) :
    duttaSequence R p (frobeniusComplex R p n F) m =
      ((p:ℝ)^n)^dimension R * duttaSequence R p F (n+m) := by
  have hp : (p:ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he : shortEuler R (frobeniusComplex R p m (frobeniusComplex R p n F)) =
      shortEuler R (frobeniusComplex R p (n+m) F) := by
    apply Finset.sum_congr rfl
    intro j _
    have H := ((homologyFunctor (ModuleCat R) (.up ℤ) (-(j:ℤ))).mapIso
      (frobeniusComplexAddIso p F n m)).toLinearEquiv.length_eq
    change Module.length R ((frobeniusComplex R p m (frobeniusComplex R p n F)).homology (-(j:ℤ))) =
      Module.length R ((frobeniusComplex R p (n+m) F).homology (-(j:ℤ))) at H
    rw [H]
  unfold duttaSequence
  rw [he,frobenius_weight_eq,frobenius_weight_eq,pow_add,mul_pow]
  field_simp

omit [IsLocalRing R] [IsNoetherianRing R] in
lemma duttaLimit_frobenius (F : CochainComplex (ModuleCat.{u} R) ℤ) (L : ℝ)
    (hL : Tendsto (duttaSequence R p F) atTop (𝓝 L)) (n : ℕ) :
    Tendsto (duttaSequence R p (frobeniusComplex R p n F)) atTop
      (𝓝 (((p:ℝ)^n)^dimension R*L)) := by
  have ht : Tendsto (fun m : ℕ => n+m) atTop atTop := by
    simpa only [Nat.add_comm n] using tendsto_add_atTop_nat n
  have H := (hL.comp ht).const_mul (((p:ℝ)^n)^dimension R)
  apply H.congr
  intro m
  exact (duttaSequence_frobenius p F n m).symm

lemma frobenius_finiteHomology (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (n : ℕ) :
    IsFiniteHomologyComplex R (frobeniusComplex R p n F) := by
  refine ⟨fun i => ?_,fun i => ?_,fun i hi => ?_,fun i => ?_⟩
  · let := hF.term_free i
    exact free_extendScalars (iterateFrobenius R p n) (F.X i)
  · let := hF.term_finite i
    exact finite_extendScalars (iterateFrobenius R p n) (F.X i)
  · exact (ModuleCat.extendScalars (iterateFrobenius R p n)).map_isZero (hF.bounded i hi)
  · exact frobenius_shortComplex_homology_finiteLength p F hF n i
end Lech

end

end OAI
