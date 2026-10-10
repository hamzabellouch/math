import Mathlib
import OAI.RingTheory.Multiplicity.DuttaBaseChange
import OAI.RingTheory.Multiplicity.DuttaDimensionZero
import OAI.RingTheory.Multiplicity.DuttaInfinitePerfect
import OAI.RingTheory.Multiplicity.PrimeQuotientParameters
import OAI.RingTheory.Multiplicity.QuotientShort

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
attribute [local instance] quotient_local quotient_localHom
local instance duttaQuotientCharP (p : ℕ) [Fact p.Prime] [CharP R p]
    (P : Ideal R) [P.IsPrime] : CharP (R ⧸ P) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (Ideal.Quotient.mk P) (CharP.cast_eq_zero R p)
    simpa only [map_natCast,map_zero] using h)
local instance duttaResidueCharP (A : Type u) [CommRing A] [IsLocalRing A]
    (p : ℕ) [Fact p.Prime] [CharP A p] : CharP (ResidueField A) p :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (residue A) (CharP.cast_eq_zero A p)
    simpa only [map_natCast,map_zero] using h)
local instance duttaQuotientAlgebraLocal (P : Ideal R) [P.IsPrime] :
    IsLocalHom (algebraMap R (R ⧸ P)) :=
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

lemma tensor_quotient_homology_length (P : Ideal R) [P.IsPrime]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    Module.length R (((tensorModuleFunctor F).obj (ModuleCat.of R (R ⧸ P))).homology i)=
      Module.length (R ⧸ P)
        ((((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F).homology i) := by
  rw [(homologyMapIso (tensorScalarExtensionIso (S:=R ⧸ P) F) i).toLinearEquiv.length_eq]
  exact restriction_homology_length (quotient_residue_surjective P) _ i

def cyclicDuttaSequence (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) (n : ℕ) : ℝ :=
  (p:ℝ)^(-(n*dimension R:ℤ)) *
    shortEuler R ((tensorModuleFunctor (frobeniusComplex R p n F)).obj (ModuleCat.of R (R ⧸ P)))

lemma cyclicDuttaSequence_full (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) [P.IsPrime]
    (hd : dimension (R ⧸ P)=dimension R) (n : ℕ) :
    cyclicDuttaSequence p F P n=duttaSequence (R ⧸ P) p
      (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F) n := by
  unfold cyclicDuttaSequence duttaSequence shortEuler
  rw [hd]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [tensor_quotient_homology_length]
  rw [(homologyMapIso (frobeniusBaseChangeIso p (Ideal.Quotient.mk P) F n) (-(i:ℤ))).toLinearEquiv.length_eq]

lemma cyclicDuttaSequence_small (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (P : Ideal R) [P.IsPrime] (hd : dimension (R ⧸ P)<dimension R) :
    Tendsto (cyclicDuttaSequence p F P) atTop (𝓝 0) := by
  obtain ⟨zs,hlen,hzs,hprim⟩ := exists_prime_quotient_parameters P hd
  have hi (i : ℕ) := (frobenius_quotient_homology_tendsto_zero p F hF P zs hzs hprim hlen
    (-(i:ℤ))).const_mul ((-1:ℝ)^i)
  have hsum := tendsto_finsetSum (Finset.range (dimension R+1)) (fun i _ => hi i)
  simp only [mul_zero,Finset.sum_const_zero] at hsum
  apply hsum.congr
  intro n
  unfold cyclicDuttaSequence shortEuler
  rw [frobenius_weight_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have e := (NatIso.mapHomologicalComplex (TensorTotal.termTensorQuotientIso P) (.up ℤ)).app
    (frobeniusComplex R p n F)
  have he := (homologyMapIso e (-(i:ℤ))).toLinearEquiv.length_eq
  change Module.length R (((tensorModuleFunctor (frobeniusComplex R p n F)).obj
    (ModuleCat.of R (R ⧸ P))).homology (-(i:ℤ)))=_ at he
  rw [he,div_eq_mul_inv]
  unfold complexQuotient
  ring

def cyclicDuttaContribution (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (P : Ideal R) : ℝ := by
  classical
  exact if hp : P.IsPrime then
    letI := hp
    if dimension (R ⧸ P)=dimension R then
      duttaMultiplicity (R ⧸ P) p
        (((ModuleCat.extendScalars (Ideal.Quotient.mk P)).mapHomologicalComplex (.up ℤ)).obj F)
    else 0
  else 0

variable [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]
lemma cyclicDuttaSequence_tendsto (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F)
    (P : Ideal R) [P.IsPrime] :
    Tendsto (cyclicDuttaSequence p F P) atTop (𝓝 (cyclicDuttaContribution p F P)) := by
  classical
  let := prime_quotient_complete P
  let := isAlgClosed_quotient_residue P
  simp only [cyclicDuttaContribution,dite_eq_left (show P.IsPrime from inferInstance)]
  split_ifs with hd
  · have hG := shortComplex_quotient P hd F hF
    change Tendsto (fun n => cyclicDuttaSequence p F P n) atTop _
    simp_rw [cyclicDuttaSequence_full p F P hd]
    by_cases hzero : dimension (R ⧸ P)=0
    · exact (dutta_dimension_zero p hzero _ hG).1
    · exact CharP.exists_dutta_limit (R ⧸ P) p (Nat.pos_of_ne_zero hzero) _ hG.finiteHomology
  · exact cyclicDuttaSequence_small p F hF.finiteHomology P
      (lt_of_le_of_ne (PrimeFiltration.quotient_dimension_le P inferInstance) hd)

lemma cyclicDuttaContribution_lower (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F)
    (P : Ideal R) [P.IsPrime] :
    ((dimension R).factorial:ℝ) * PrimeFiltration.contribution (maximalIdeal R) P ≤
      cyclicDuttaContribution p F P := by
  classical
  let := prime_quotient_complete P
  let := isAlgClosed_quotient_residue P
  simp only [cyclicDuttaContribution,PrimeFiltration.contribution,
    dite_eq_left (show P.IsPrime from inferInstance)]
  split_ifs with hd
  · rw [map_maximalIdeal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
      Primary.maximal_multiplicity_eq]
    have hfac : ((dimension R).factorial:ℝ) ≠ 0 := by positivity
    rw [mul_div_cancel₀ _ hfac]
    have hG := shortComplex_quotient P hd F hF
    by_cases hzero : dimension (R ⧸ P)=0
    · exact (dutta_dimension_zero p hzero _ hG).2
    · exact CharP.dutta_lower_bound_infinite_perfect (R ⧸ P) p (Nat.pos_of_ne_zero hzero) _ hG
  · simp
end Lech

end

end OAI
