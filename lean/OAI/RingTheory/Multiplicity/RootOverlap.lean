import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousEval
import OAI.RingTheory.Multiplicity.RootChartAtlasGlobalCoefficient

namespace OAI

noncomputable section

namespace Lech.ProjectiveRoot

open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

 
def product (s : Finset (Fin (n+1))) : MvPolynomial (Fin (n+1)) R :=
  ∏ j ∈ s, X j
lemma product_homogeneous (s : Finset (Fin (n+1))) :
    product R n s ∈ ProjectiveCoefficientChart.grading R n s.card := by
  simpa [product] using IsHomogeneous.prod s (fun j => X (R:=R) j)
    (fun _ => 1) (fun j _ => isHomogeneous_X R j)

abbrev Ring (s : Finset (Fin (n+1))) :=
  Away (ProjectiveCoefficientChart.grading R n) (product R n s)


def coefficientEvaluation : MvPolynomial (Fin (n+1)) R →ₐ[R] GridAmbient R n :=
  MvPolynomial.aeval (fun j => embed R n (targetCoeff R n j))
lemma coefficientEvaluation_X (j : Fin (n+1)) :
    coefficientEvaluation R n (X j) = (targetUnit R n j : GridAmbient R n) := by
  rw [coefficientEvaluation, MvPolynomial.aeval_X, targetUnit_val]
lemma coefficientEvaluation_product (s : Finset (Fin (n+1))) :
    coefficientEvaluation R n (product R n s) = embed R n (denominator R n s) := by
  simp only [coefficientEvaluation, product, map_prod, MvPolynomial.aeval_X,
    denominator, AwayCover.denominator]
lemma coefficientEvaluation_unit (s : Finset (Fin (n+1))) :
    IsUnit (coefficientEvaluation R n (product R n s)) := by
  rw [coefficientEvaluation_product]
  exact denominator_unit R n s


def scalarAt (f : MvPolynomial (Fin (n+1)) R)
    (hu : IsUnit (coefficientEvaluation R n f)) :
    Away (ProjectiveCoefficientChart.grading R n) f →ₐ[R] GridAmbient R n where
  toRingHom := HomogeneousEval.evaluate (ProjectiveCoefficientChart.grading R n)
    (coefficientEvaluation R n).toRingHom f hu
  commutes' r := by
    change Localization.awayLift (coefficientEvaluation R n).toRingHom f hu
      (algebraMap R (Away (ProjectiveCoefficientChart.grading R n) f) r).val = _
    rw [Homogeneous.val_algebraMap]
    change Localization.awayLift (coefficientEvaluation R n).toRingHom f hu
      (algebraMap (MvPolynomial (Fin (n+1)) R) (Localization.Away f) (C r)) = _
    rw [IsLocalization.Away.lift_eq]
    exact (coefficientEvaluation R n).commutes r

 
def scalarMap (s : Finset (Fin (n+1))) : Ring R n s →ₐ[R] GridAmbient R n :=
  scalarAt R n (product R n s) (coefficientEvaluation_unit R n s)

lemma coefficientEvaluation_X_unit (k : Fin (n+1)) :
    IsUnit (coefficientEvaluation R n (X k)) := by
  rw [coefficientEvaluation_X]
  exact (targetUnit R n k).isUnit

variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s)
include hk in
lemma product_eq : product R n s = X k * projectiveRemainder R n k s :=
  (projectiveRemainder_product R n k s hk).symm

 
def chartMap : ProjectiveCoefficientChart.Chart R n k →+* Ring R n s :=
  awayMap (ProjectiveCoefficientChart.grading R n)
    (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk)
def coefficientMap : UniversalCoefficientChart.Ring R n k →+* Ring R n s :=
  (chartMap R n k s hk).comp (ProjectiveCoefficientChart.equiv R n k).toRingHom

lemma scalarMap_chart (a : ProjectiveCoefficientChart.Chart R n k) :
    scalarMap R n s (chartMap R n k s hk a) =
      scalarAt R n (X k) (coefficientEvaluation_X_unit R n k) a := by
  apply HomogeneousEval.evaluate_awayMap

lemma scalarAt_equiv :
    (scalarAt R n (X k) (coefficientEvaluation_X_unit R n k)).comp
      (ProjectiveCoefficientChart.equiv R n k).toAlgHom = gridTarget R n k := by
  apply UniversalCoefficientChart.ext
  intro j
  change scalarAt R n (X k) (coefficientEvaluation_X_unit R n k)
    (ProjectiveCoefficientChart.forward R n k
      (UniversalCoefficientChart.coefficient R n k j)) = _
  rw [ProjectiveCoefficientChart.forward_coefficient]
  change HomogeneousEval.evaluate _ _ _ _
    (Away.mk _ _ 1 (X j) _) = _
  refine (HomogeneousEval.evaluate_mk (ProjectiveCoefficientChart.grading R n)
    (coefficientEvaluation R n).toRingHom
    (show X k ∈ ProjectiveCoefficientChart.grading R n 1 from isHomogeneous_X R k)
    (coefficientEvaluation_X_unit R n k)
    (↑((targetUnit R n k)⁻¹) : GridAmbient R n)
    (by change coefficientEvaluation R n (X k) * _ = 1
        rw [coefficientEvaluation_X, Units.mul_inv]) 1 (X j)
    (show X j ∈ ProjectiveCoefficientChart.grading R n (1 • 1) from
      isHomogeneous_X R j)).trans ?_
  change coefficientEvaluation R n (X j) * _ ^ 1 = _
  rw [pow_one, coefficientEvaluation_X, gridTarget_coefficient, ←targetUnit_val]
  exact mul_comm _ _


lemma scalarMap_coefficient (a : UniversalCoefficientChart.Ring R n k) :
    scalarMap R n s (coefficientMap R n k s hk a) = gridTarget R n k a := by
  rw [coefficientMap, RingHom.comp_apply, scalarMap_chart]
  exact DFunLike.congr_fun (scalarAt_equiv R n k) a

@[instance_reducible] def chartAlgebra :
    Algebra (ProjectiveCoefficientChart.Chart R n k) (Ring R n s) :=
  (chartMap R n k s hk).toAlgebra
@[instance_reducible] def coefficientAlgebra :
    Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  (coefficientMap R n k s hk).toAlgebra


lemma isLocalization :
    let := coefficientAlgebra R n k s hk
    IsLocalization.Away (targetProduct R n k s) (Ring R n s) := by
  let := coefficientAlgebra R n k s hk
  let := chartAlgebra R n k s hk
  let : IsLocalization.Away
      (Away.isLocalizationElem (isHomogeneous_X R k)
        (projectiveRemainder_homogeneous R n k s)) (Ring R n s) :=
    Away.isLocalization_mul (isHomogeneous_X R k)
      (projectiveRemainder_homogeneous R n k s) (product_eq R n k s hk) (by decide)
  apply IsLocalization.of_ringEquiv_left (ProjectiveCoefficientChart.equiv R n k).toRingEquiv
    (M₁ := Submonoid.powers (Away.isLocalizationElem (isHomogeneous_X R k)
      (projectiveRemainder_homogeneous R n k s)))
  · rw [Submonoid.map_powers]
    congr 1
    rw [←projectiveRemainder_evaluate R n k s hk]
    exact ProjectiveCoefficientChart.equiv_evaluate_localizationElem R n k
      (projectiveRemainder R n k s) (projectiveRemainder_homogeneous R n k s)
  · intro a
    rfl

include hk in
 

lemma scalar_mem (m : Fin n → ℤ) (a : Ring R n s) (x : GridAmbient R n)
    (hx : x ∈ grid R n m s ∅) :
    scalarMap R n s a * x ∈ grid R n m s ∅ := by
  let := coefficientAlgebra R n k s hk
  let := isLocalization R n k s hk
  obtain ⟨⟨b,c⟩,hb⟩ := IsLocalization.surj (Submonoid.powers (targetProduct R n k s)) a
  obtain ⟨N,hN⟩ := c.property
  change a * coefficientMap R n k s hk c = coefficientMap R n k s hk b at hb
  have he := congrArg (scalarMap R n s) hb
  rw [map_mul, scalarMap_coefficient, scalarMap_coefficient, ←hN, map_pow,
    ←targetProductUnit_val] at he
  have hbmem : gridTarget R n k b * x ∈ grid R n m s ∅ :=
    (overlapModule R n k m s hk).smul_mem b hx
  have hmem := inverse_mem_overlap R n k m s hk ⟨_,hbmem⟩ N
  have heq : scalarMap R n s a * x =
      (↑((targetProductUnit R n k s)⁻¹) : GridAmbient R n)^N * (gridTarget R n k b * x) := by
    rw [←he]
    calc
      _ = ((↑((targetProductUnit R n k s)⁻¹) : GridAmbient R n)^N *
          (targetProductUnit R n k s : GridAmbient R n)^N) * (scalarMap R n s a * x) := by
            rw [←mul_pow, Units.inv_mul, one_pow, one_mul]
      _ = _ := by ring
  rw [heq]
  exact hmem

instance ambientAlgebra (t : Finset (Fin (n+1))) : Algebra (Ring R n t) (GridAmbient R n) :=
  (scalarMap R n t).toRingHom.toAlgebra
instance ambientTower (t : Finset (Fin (n+1))) :
    IsScalarTower R (Ring R n t) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq' (scalarMap R n t).comp_algebraMap.symm


def Sections (t : Finset (Fin (n+1))) (ht : t.Nonempty) (m : Fin n → ℤ) :
    Submodule (Ring R n t) (GridAmbient R n) where
  carrier := grid R n m t ∅
  zero_mem' := (grid R n m t ∅).zero_mem
  add_mem' := (grid R n m t ∅).add_mem
  smul_mem' a x hx := by
    obtain ⟨j,hj⟩ := ht
    exact scalar_mem R n j t hj m a x hx

local instance canonicalRing : CommRing (Ring R n s) := inferInstance
variable [hks : Fact (k ∈ s)]
local instance coeffToIntersection : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  coefficientAlgebra R n k s hks.out
local instance coeffToAmbient : Algebra (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) :=
  gridTargetAlgebra R n k
local instance coeffToIntersectionModule : Module (UniversalCoefficientChart.Ring R n k) (Ring R n s) := Algebra.toModule
local instance coeffToAmbientModule : Module (UniversalCoefficientChart.Ring R n k) (GridAmbient R n) := Algebra.toModule
local instance coeffTower : IsScalarTower (UniversalCoefficientChart.Ring R n k)
    (Ring R n s) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => (scalarMap_coefficient R n k s hks.out a).symm
local instance coeffLocalization :
    IsLocalization.Away (targetProduct R n k s) (Ring R n s) :=
  isLocalization R n k s hks.out
variable (hs : s.Nonempty) (m : Fin n → ℤ)
local instance coeffSectionsSMul : SMul (UniversalCoefficientChart.Ring R n k) (Sections R n s hs m) :=
  (Sections R n s hs m).smul
local instance coeffSectionsModule : Module (UniversalCoefficientChart.Ring R n k) (Sections R n s hs m) :=
  (Sections R n s hs m).module'
local instance coeffSectionsTower : IsScalarTower (UniversalCoefficientChart.Ring R n k)
    (Ring R n s) (Sections R n s hs m) := (Sections R n s hs m).isScalarTower
local instance tensorAdd : AddCommGroup (Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
    sectionModule R n k m) := TensorProduct.addCommGroup


def overlapEquiv : overlapModule R n k m s hks.out ≃ₗ[UniversalCoefficientChart.Ring R n k]
    Sections R n s hs m where
  toFun x := ⟨x.val,x.property⟩
  invFun x := ⟨x.val,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 
def chartRestriction : sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
    Sections R n s hs m :=
  (overlapEquiv R n k s hs m).toLinearMap.comp (ProductSourceCover.restriction R n k m s hks.out)

instance chartRestriction_localized :
    IsLocalizedModule (Submonoid.powers (targetProduct R n k s))
      (chartRestriction R n k s hs m) :=
  IsLocalizedModule.of_linearEquiv _ (ProductSourceCover.restriction R n k m s hks.out)
    (overlapEquiv R n k s hs m)


def chartBaseChange : Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
    sectionModule R n k m ≃ₗ[Ring R n s] Sections R n s hs m :=
  (IsLocalizedModule.isBaseChange (Submonoid.powers (targetProduct R n k s))
    (Ring R n s) (chartRestriction R n k s hs m)).equiv

lemma chartBaseChange_one (x : sectionModule R n k m) :
    chartBaseChange R n k s hs m (1 ⊗ₜ[UniversalCoefficientChart.Ring R n k] x) =
      chartRestriction R n k s hs m x := by
  exact (IsBaseChange.equiv_tmul _ _ _).trans (one_smul _ _)

include hks in
 

theorem Sections_properties :
    Module.FinitePresentation (Ring R n s) (Sections R n s hs m) ∧
    Module.Projective (Ring R n s) (Sections R n s hs m) ∧
    ∀ p : PrimeSpectrum (Ring R n s),
      Module.rankAtStalk (Sections R n s hs m) p = n.factorial := by
  obtain ⟨hfp,hpr,hr⟩ := sectionModule_properties R n k m
  let := hfp
  let := hpr
  refine ⟨Module.FinitePresentation.of_equiv (chartBaseChange R n k s hs m),
    Module.Projective.of_equiv (chartBaseChange R n k s hs m),?_⟩
  intro p
  rw [←Module.rankAtStalk_eq_of_equiv (chartBaseChange R n k s hs m), Module.rankAtStalk_baseChange]
  exact hr _


end Lech.ProjectiveRoot

end

end OAI
