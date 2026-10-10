import Mathlib
import OAI.RingTheory.Multiplicity.ScalarChartComparison

namespace OAI

noncomputable section
namespace Lech.FilteredCech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)

lemma positiveXIso_d (t n : ℕ) (hn : 0<n) :
    (positive I z hz t).d (n:ℤ) ((n+1:ℕ):ℤ) ≫ (positiveXIso I z hz t (n+1) (by omega)).hom=
      (positiveXIso I z hz t n hn).hom ≫ (complex I z hz t).d n (n+1) := by
  let κ := kernel.ι (FiniteComplex.bottomProjection (augmented I z hz t) 0 (augmented_boundedBelow I z hz t))
  change (positive I z hz t).d (n:ℤ) ((n+1:ℕ):ℤ) ≫ (κ.f _ ≫ _)=κ.f _ ≫ _ ≫ _
  dsimp only [positive,FiniteComplex.dropBottom]
  rw [←Category.assoc,←κ.comm,Category.assoc]
  change κ.f _ ≫ ((complex I z hz t).extend ComplexShape.embeddingUpNat).d _ _ ≫ _=_
  dsimp only [augmented] at κ ⊢
  rw [(complex I z hz t).extend_d_eq ComplexShape.embeddingUpNat
    (i:=n) (j:=n+1) (i':=(n:ℤ)) (j':=((n+1:ℕ):ℤ)) rfl rfl]
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

lemma complex_d (t n : ℕ) :
    (complex I z hz t).d n (n+1)=ModuleCat.ofHom
      (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) n) := by
  exact CochainComplex.of_d (fun q => ModuleCat.of R (LocalizationCech.cochains z (term I z t) q))
    (fun q => ModuleCat.ofHom (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) q)) n

abbrev shiftedPositive (t : ℕ) := (positive I z hz t)⟦(1:ℤ)⟧
abbrev ordinaryPositive (t : ℕ) := CechNormalization.fullPositive (diagram I z hz t)

def shiftXIso (t p : ℕ) :
    ((shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat).X p ≅ (ordinaryPositive I z hz t).X p where
  hom := (p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom
  inv := (p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv
  hom_inv_id := by
    change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom) ≫
      ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv) =
        𝟙 ((positive I z hz t).X ((p+1:ℕ):ℤ))
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,Int.units_mul_self,one_smul,Iso.hom_inv_id]
  inv_hom_id := by
    change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).inv) ≫
      ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) (by omega)).hom) =
        𝟙 ((complex I z hz t).X (p+1))
    simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul,Int.units_mul_self,one_smul,Iso.inv_hom_id]

lemma shiftXIso_d (t p : ℕ) :
    (shiftXIso I z hz t p).hom ≫ (ordinaryPositive I z hz t).d p (p+1)=
    ((shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat).d p (p+1) ≫
      (shiftXIso I z hz t (p+1)).hom := by
  rw [CechNormalization.fullPositive_d]
  dsimp only [shiftXIso, restriction, shiftedPositive]
  rw [CochainComplex.shiftFunctor_obj_d']
  rw [diagram_fullD]
  change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) _).hom) ≫
      ModuleCat.ofHom (LocalizationCech.d z (term I z t) (restriction_mem I z hz t) (p+1)) =
    ((1:ℤ).negOnePow • (positive I z hz t).d ((p+1:ℕ):ℤ) ((p+1+1:ℕ):ℤ)) ≫
      (((p+1:ℕ):ℤ).negOnePow • (positiveXIso I z hz t (p+1+1) _).hom)
  rw [←complex_d I z hz t (p+1)]
  change ((p:ℤ).negOnePow • (positiveXIso I z hz t (p+1) _).hom) ≫ (complex I z hz t).d (p+1) (p+1+1)=
    ((1:ℤ).negOnePow • (positive I z hz t).d ((p+1:ℕ):ℤ) ((p+1+1:ℕ):ℤ)) ≫
      (((p+1:ℕ):ℤ).negOnePow • (positiveXIso I z hz t (p+1+1) _).hom)
  simp only [Linear.units_smul_comp,Linear.comp_units_smul,smul_smul]
  rw [positiveXIso_d]
  have he : ((p+1:ℕ):ℤ).negOnePow*(1:ℤ).negOnePow=(p:ℤ).negOnePow := by
    rw [Nat.cast_add,Nat.cast_one,Int.negOnePow_add,mul_assoc,Int.units_mul_self,mul_one]
  rw [he]

def shiftRestrictionIso (t : ℕ) :
    (shiftedPositive I z hz t).restriction ComplexShape.embeddingUpNat ≅ ordinaryPositive I z hz t :=
  Hom.isoOfComponents (shiftXIso I z hz t) (fun p q hpq => by
    obtain rfl : p+1=q := hpq
    exact shiftXIso_d I z hz t p)

lemma shiftRestriction_hasLift (t : ℕ) :
    ComplexShape.embeddingUpNat.HasLift (shiftRestrictionIso I z hz t).hom := by
  intro j hj i hi
  have hneg : i < 0 := by
    by_contra h
    have hnonneg : 0 ≤ i := by omega
    exact hj.notMem hi i.toNat (by change (i.toNat:ℤ)=i; exact Int.toNat_of_nonneg hnonneg)
  have hzero : IsZero ((shiftedPositive I z hz t).X i) :=
    positive_boundedBelow I z hz t (i+1) (by omega)
  exact hzero.eq_of_src _ _

def shiftToOrdinary (t : ℕ) : shiftedPositive I z hz t ⟶
    (ordinaryPositive I z hz t).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (shiftRestrictionIso I z hz t).hom (shiftRestriction_hasLift I z hz t)

instance shiftToOrdinary_isIso (t : ℕ) : IsIso (shiftToOrdinary I z hz t) := by
  have hf (i : ℤ) : IsIso ((shiftToOrdinary I z hz t).f i) := by
    by_cases hi : 0 ≤ i
    · exact (ComplexShape.embeddingUpNat.isIso_liftExtend_f_iff _ _
        (i:=i.toNat) (i':=i) (by change (i.toNat:ℤ)=i; exact Int.toNat_of_nonneg hi)).mpr inferInstance
    · apply (positive_boundedBelow I z hz t (i+1) (by omega)).isIso
      exact (ordinaryPositive I z hz t).isZero_extend_X ComplexShape.embeddingUpNat i
        (fun p hp => by change (p:ℤ)=i at hp; omega)
  exact Hom.isIso_of_components (shiftToOrdinary I z hz t)

def shiftOrdinaryIso (t : ℕ) : shiftedPositive I z hz t ≅
    (ordinaryPositive I z hz t).extend ComplexShape.embeddingUpNat := asIso (shiftToOrdinary I z hz t)
end Lech.FilteredCech

end

end OAI
