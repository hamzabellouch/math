import Mathlib
import OAI.RingTheory.Multiplicity.FieldNilpotentLift

namespace OAI

noncomputable section
namespace Lech.ArbitraryCoefficientField
variable {k R : Type*} [Field k] [CommRing R]
  (p : ℕ) [Fact p.Prime] [CharP k p] [CharP R p] (I : Ideal R) [I.IsMaximal]

lemma power_strictMono : StrictMono (fun n : ℕ => p^n) :=
  pow_right_strictMono₀ (Nat.Prime.one_lt (Fact.out : p.Prime))

omit [CharP R p] [I.IsMaximal] in
lemma transition_ker (n : ℕ) :
    (RingHom.ker (Ideal.Quotient.factorPow I
      ((power_strictMono p).monotone (Nat.le_succ n))))^p=⊥ := by
  rw [Ideal.Quotient.factor_ker,← Ideal.map_pow,← pow_mul,← pow_succ]
  exact Ideal.map_quotient_self _

lemma exists_next (n : ℕ) (f : k →+* R ⧸ I^(p^n)) :
    ∃ g : k →+* R ⧸ I^(p^(n+1)),
      (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp g=f := by
  let : Nontrivial (R ⧸ I^(p^(n+1))) := Ideal.Quotient.nontrivial_iff.mpr
    (ne_top_of_le_ne_top (Ideal.IsMaximal.ne_top inferInstance)
      (Ideal.pow_le_self (pow_ne_zero _ (Nat.Prime.ne_zero Fact.out))))
  let : CharP (R ⧸ I^(p^(n+1))) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
    (by rw [← map_natCast (Ideal.Quotient.mk _),CharP.cast_eq_zero,map_zero])
  exact FieldLift.exists_lift_surjective p _ (Ideal.Quotient.factor_surjective _)
    (transition_ker p I n) f

 
def stage (f : k →+* R ⧸ I) : (n : ℕ) → k →+* R ⧸ I^(p^n)
  | 0 => (Ideal.quotEquivOfEq (by simp : I=I^(p^0))).toRingHom.comp f
  | n+1 => (exists_next p I n (stage f n)).choose

lemma stage_compatible (f : k →+* R ⧸ I) (n : ℕ) :
    (Ideal.Quotient.factorPow I ((power_strictMono p).monotone (Nat.le_succ n))).comp
      (stage p I f (n+1))=stage p I f n :=
  (exists_next p I n (stage p I f n)).choose_spec

variable [IsAdicComplete I R]
 
def sectionMap (f : k →+* R ⧸ I) : k →+* R :=
  IsAdicComplete.StrictMono.liftRingHom I (power_strictMono p) (stage p I f)
    (fun {n} => stage_compatible p I f n)

lemma sectionMap_mod (f : k →+* R ⧸ I) (x : k) :
    Ideal.Quotient.mk I (sectionMap p I f x)=f x := by
  have h := IsAdicComplete.StrictMono.mk_liftRingHom I (power_strictMono p)
    (stage p I f) (fun {n} => stage_compatible p I f n) (n:=0) x
  change Ideal.Quotient.mk (I^(p^0)) (sectionMap p I f x)=
    (Ideal.quotEquivOfEq (by simp : I=I^(p^0))) (f x) at h
  apply (Ideal.quotEquivOfEq (by simp : I=I^(p^0))).injective
  simpa only [Ideal.quotEquivOfEq_mk] using h

end Lech.ArbitraryCoefficientField

namespace Lech.ArbitraryCoefficientField
open IsLocalRing
variable (R : Type*) [CommRing R] [IsLocalRing R]
  (p : ℕ) [Fact p.Prime] [CharP R p] [IsAdicComplete (maximalIdeal R) R]
 

def quotientSectionData : {g : R ⧸ maximalIdeal R →+* R //
    Function.RightInverse g (Ideal.Quotient.mk (maximalIdeal R))} := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : CharP (R ⧸ maximalIdeal R) p :=
    (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
      (by rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal R)),CharP.cast_eq_zero,map_zero])
  refine ⟨sectionMap (k:=R ⧸ maximalIdeal R) p (maximalIdeal R) (RingHom.id _),?_⟩
  intro x
  exact sectionMap_mod p (maximalIdeal R) (RingHom.id _) x

 
def localSection : R ⧸ maximalIdeal R →+* R := (quotientSectionData R p).1

lemma localSection_rightInverse :
    Function.RightInverse (localSection R p) (Ideal.Quotient.mk (maximalIdeal R)) :=
  (quotientSectionData R p).2

lemma localSection_injective : Function.Injective (localSection R p) :=
  (localSection_rightInverse R p).injective
end Lech.ArbitraryCoefficientField

end

end OAI
