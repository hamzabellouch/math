import Mathlib
import OAI.RingTheory.Multiplicity.CechNormalization
import OAI.RingTheory.Multiplicity.ReesExceptionalSquare
import OAI.RingTheory.Multiplicity.ReesUlrichCech

namespace OAI

noncomputable section
namespace Lech.Homogeneous
open HomogeneousLocalization
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (G : ℕ → Submodule R A) [GradedAlgebra G]
attribute [local instance] awayAddCommGroup
lemma awayCongr_restrict {f f' c c' q q' : A} {k : ℕ}
    (hf : f=f') (hc : c=c') (hq : q=q') (hg : c∈G k) (hg' : c'∈G k)
    (he : q=f*c) (he' : q'=f'*c') (x : Away G f) :
    awayCongr G hq (HomogeneousLocalization.awayMap G hg he x)=
      HomogeneousLocalization.awayMap G hg' he' (awayCongr G hf x) := by
  subst f'; subst c'; subst q'; rfl
end Lech.Homogeneous
namespace Lech.FilteredFraction
open HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {w v c : R} {d e k : ℕ} (hw : w∈I^d) (hv : v∈I^e) (hc : c∈I^k)
  (he : w*c=v) (hd : d+k=e)
attribute [local instance] Homogeneous.awayAddCommGroup
lemma chartEquiv_restrict (x : ReesChart I hw) :
    chartEquiv I hv (HomogeneousLocalization.awayMap (reesGrade I)
      (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc he hd).symm x)=
    restrict I hw hc he hd 0 (chartEquiv I hw x) := by
  apply Subtype.ext
  change reesAmbient I hv ((HomogeneousLocalization.awayMap (reesGrade I)
    (reesDenominator_mem I hc) (reesDenominator_mul I hw hv hc he hd).symm x).val)=_
  rw [HomogeneousLocalization.val_awayMap]
  exact AlgHom.congr_fun (reesAmbient_naturality I hw hv hc he hd) x.val
end Lech.FilteredFraction
namespace Lech.FilteredCech
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : ∀ j,z j∈I)
def diagram (t : ℕ) : FiniteModuleCech.Diagram R (Fin h) where
  obj s := ModuleCat.of R (term I z t s)
  res hst := ModuleCat.ofHom (LocalizationCech.restrict z (term I z t) (restriction_mem I z hz t) hst)
  res_self s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact AlgHom.congr_fun (TwistedLocalization.ambientTo_self (R:=R) (GradedChart.denominator z s)) x.val
  res_comp hst htv := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact LocalizationCech.restrict_comp z (term I z t) (restriction_mem I z hz t) hst htv

lemma diagram_fullD (t p : ℕ) :
    CechNormalization.fullD (diagram I z hz t) p=LocalizationCech.d z (term I z t) (restriction_mem I z hz t) p := by
  apply LinearMap.ext
  intro x
  funext a
  change (∑ j : Fin (p+1),(-1:R)^j.val •
    CarrierOperators.toFixed (diagram I z hz t) (CechNormalization.fullCarrier p)
      (FiniteCoverCech.intersection a) x (a ∘ j.succAbove))=_
  apply Finset.sum_congr rfl
  intro j hj
  change (-1:R)^j.val • (if h : _ then _ else _)=_
  have hj' : (CechNormalization.fullCarrier p).support (a ∘ j.succAbove)⊆
      FiniteCoverCech.intersection a := ActualCech.intersection_delete a j
  rw [dite_eq_left hj']
  rfl
end Lech.FilteredCech
namespace Lech.ReesRoot
open CategoryTheory HomogeneousLocalization IdealGraded
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup
private local instance concreteRing (s : Finset (Fin (n+1))) : CommRing (Ring I z hz s) := inferInstance
private local instance baseModule (s : Finset (Fin (n+1))) : Module R (Ring I z hz s) := inferInstance

def scalarChartEquiv (s : Finset (Fin (n+1))) :
    Ring I z hz s ≃ₗ[R] FilteredCech.term I z 0 s :=
  (chartRename I z hz s).toLinearEquiv.trans (FilteredFraction.chartEquiv I (product_mem I z hz s))

lemma scalarChartEquiv_natural {s t : Finset (Fin (n+1))} (hst : s⊆t) (x : Ring I z hz s) :
    scalarChartEquiv I z hz t (restriction I z hz hst x)=
      ((FilteredCech.diagram I z hz 0).res hst).hom (scalarChartEquiv I z hz s x) := by
  have he : (∏ j∈s,z j)*(∏ j∈t\s,z j)=(∏ j∈t,z j) :=
    GradedChart.denominator_mul_sdiff z hst
  have hd : s.card+(t\s).card=t.card := by
    rw [Nat.add_comm,Finset.card_sdiff_add_card_eq_card hst]
  have hr := Homogeneous.awayCongr_restrict (reesGrade I)
    (denominator_eq I z hz s) (denominator_eq I z hz (t\s)) (denominator_eq I z hz t)
    (denominator_mem I z hz (t\s)) (FilteredFraction.reesDenominator_mem I (product_mem I z hz (t\s)))
    (denominator_subsets I z hz hst)
    (FilteredFraction.reesDenominator_mul I (product_mem I z hz s) (product_mem I z hz t)
      (product_mem I z hz (t\s)) he hd).symm x
  change FilteredFraction.chartEquiv I (product_mem I z hz t)
    (chartRename I z hz t (restriction I z hz hst x))=_
  rw [show chartRename I z hz t (restriction I z hz hst x)=_ from hr,
    FilteredFraction.chartEquiv_restrict I (product_mem I z hz s) (product_mem I z hz t)
      (product_mem I z hz (t\s)) he hd]
  rfl

 

def scalarSectionEquiv (s : Finset (Fin (n+1))) (hs : s.Nonempty) :
    ScalarCechSection I z hz s ≃ₗ[R] FilteredCech.term I z 0 s where
  toFun x := scalarChartEquiv I z hz s (x ⟨hs⟩)
  invFun x _ := (scalarChartEquiv I z hz s).symm x
  left_inv x := by funext ht; exact LinearEquiv.symm_apply_apply _ _
  right_inv x := LinearEquiv.apply_symm_apply _ _
  map_add' _ _ := map_add _ _ _
  map_smul' r x := by
    change scalarChartEquiv I z hz s (r • x ⟨hs⟩)=r • scalarChartEquiv I z hz s (x ⟨hs⟩)
    exact map_smul _ _ _

lemma scalarSectionEquiv_natural {s t : Finset (Fin (n+1))} (hst : s⊆t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : ScalarCechSection I z hz s) :
    scalarSectionEquiv I z hz t ht ((scalarCechRes I z hz hst).hom x)=
      ((FilteredCech.diagram I z hz 0).res hst).hom (scalarSectionEquiv I z hz s hs x) := by
  change scalarChartEquiv I z hz t ((scalarCechRes I z hz hst).hom x ⟨ht⟩)=_
  rw [scalarCechRes_apply I z hz hst hs ht]
  exact scalarChartEquiv_natural I z hz hst (x ⟨hs⟩)
end Lech.ReesRoot

end

end OAI
