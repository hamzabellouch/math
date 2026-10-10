import Mathlib
import OAI.RingTheory.Multiplicity.RootRestriction

namespace OAI

noncomputable section
namespace Lech.CoefficientReduction
open MvPolynomial HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) (h : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

abbrev grade := homogeneousSubmodule (Fin h) R

def graded : grade (R:=R) h →+*ᵍ SourceGraded.sourceGrade I h where
  toRingHom := MvPolynomial.map (Ideal.Quotient.mk I)
  map_mem {i} {x} hx := by
    intro e he
    exact hx (fun heq => he (by simp only [coeff_map,heq,map_zero]))

lemma graded_smul (r : R) (a : MvPolynomial (Fin h) R) :
    graded I h (r • a)=r • graded I h a :=
  (MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ R I)).toLinearMap.map_smul r a

lemma graded_surjective : Function.Surjective (graded I h) :=
  MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective

 

lemma homogeneous_mem_smul (j : ℕ) (a : grade (R:=R) h j)
    (ha : graded I h a.val=0) : a ∈ I • (⊤ : Submodule R (grade (R:=R) h j)) := by
  classical
  let b (e : (Fin h →₀ ℕ)) : grade (R:=R) h j :=
    if he : e.degree=j then ⟨monomial e 1,isHomogeneous_monomial 1 he⟩ else 0
  have hd (e : Fin h →₀ ℕ) (he : e ∈ a.val.support) : e.degree=j := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using a.property (mem_support_iff.mp he)
  have heq : a = ∑ e ∈ a.val.support, a.val.coeff e • b e := by
    apply Subtype.ext
    simp only [Submodule.coe_sum,Submodule.coe_smul]
    conv_lhs => rw [a.val.as_sum]
    apply Finset.sum_congr rfl
    intro e he
    dsimp [b]
    rw [dite_eq_left (hd e he)]
    simp only [smul_monomial,smul_eq_mul,mul_one]
  rw [heq]
  apply Submodule.sum_mem
  intro e he
  apply Submodule.smul_mem_smul _ Submodule.mem_top
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have hh := congrArg (fun polynomial : MvPolynomial (Fin h) (R ⧸ I) => polynomial.coeff e) ha
  change (MvPolynomial.map (Ideal.Quotient.mk I) a.val).coeff e=
    (0 : MvPolynomial (Fin h) (R ⧸ I)).coeff e at hh
  simpa only [coeff_map,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using hh

variable {f : MvPolynomial (Fin h) R} {d : ℕ} (hf : f ∈ grade (R:=R) h d)

def chartMap (f : MvPolynomial (Fin h) R) :=
  Homogeneous.awayMap (grade (R:=R) h) (SourceGraded.sourceGrade I h)
    (graded I h) (graded_smul I h) f

include hf in
lemma chartMap_surjective : Function.Surjective (chartMap I h f) :=
  Homogeneous.awayMap_surjective _ _ _ _ hf (graded_surjective I h)

lemma target_scalar_zero (r : R) (hr : r ∈ I)
    (x : Away (SourceGraded.sourceGrade I h) (graded I h f)) : r • x=0 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_smul,HomogeneousLocalization.val_zero]
  rw [←IsScalarTower.algebraMap_smul (R ⧸ I) r x.val]
  change (Ideal.Quotient.mk I r) • x.val=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr,zero_smul]

include hf in
 
lemma chartMap_kernel : (chartMap I h f).ker = I • (⊤ : Submodule R (Away (grade (R:=R) h) f)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨j,a,ha⟩ := Homogeneous.kernel_fraction (grade (R:=R) h)
      (SourceGraded.sourceGrade I h) (graded I h) (graded_smul I h) hf ⟨x,hx⟩
    change Homogeneous.fraction (grade (R:=R) h) hf j a.val=x at ha
    rw [←ha]
    have hm := homogeneous_mem_smul I h (j*d) a.val (congrArg Subtype.val a.property)
    have hp := Submodule.mem_map_of_mem (f:=Homogeneous.fraction (grade (R:=R) h) hf j) hm
    rw [Submodule.map_smul'',Submodule.map_top] at hp
    exact Submodule.smul_mono le_rfl le_top hp
  · apply Submodule.smul_le.mpr
    intro r hr x _
    rw [LinearMap.mem_ker,map_smul]
    exact target_scalar_zero I h r hr _

 
def chartQuotientEquiv :
    (Away (grade (R:=R) h) f ⧸ I • (⊤ : Submodule R (Away (grade (R:=R) h) f))) ≃ₗ[R]
      Away (SourceGraded.sourceGrade I h) (graded I h f) :=
  (Submodule.quotEquivOfEq _ _ (chartMap_kernel I h hf).symm).trans
    (LinearMap.quotKerEquivOfSurjective (chartMap I h f) (chartMap_surjective I h hf))
end Lech.CoefficientReduction

end

end OAI
