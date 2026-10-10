import Mathlib
import OAI.RingTheory.Multiplicity.RootOverlap

namespace OAI

noncomputable section
namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v
variable {A : Type u} [CommRing A] {σ : Type v}
  [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
 

lemma awayMap_same {f g h x : A} {e d : ℕ} (hg : g ∈ G e) (hh : h ∈ G d)
    (hx : x = f * g) (hy : x = f * h) (a : Away G f) :
    awayMap G hg hx a = awayMap G hh hy a := by
  apply HomogeneousLocalization.val_injective
  rw [val_awayMap, val_awayMap]
end Lech.HomogeneousEval

namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
open scoped TensorProduct
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma product_sdiff {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    product R n t = product R n s * product R n (t \ s) := by
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

 
def ringRestriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) :
    Ring R n s →+* Ring R n t :=
  awayMap (ProjectiveCoefficientChart.grading R n) (product_homogeneous R n (t \ s))
    (product_sdiff R n hst)

lemma scalarMap_restriction {s t : Finset (Fin (n+1))} (hst : s ⊆ t) (a : Ring R n s) :
    scalarMap R n t (ringRestriction R n hst a) = scalarMap R n s a := by
  exact HomogeneousEval.evaluate_awayMap _ _ (product_homogeneous R n (t \ s))
    (product_sdiff R n hst) (coefficientEvaluation_unit R n s)
    (coefficientEvaluation_unit R n t) a

lemma ringRestriction_comp {s t v : Finset (Fin (n+1))}
    (hst : s ⊆ t) (htv : t ⊆ v) (a : Ring R n s) :
    ringRestriction R n htv (ringRestriction R n hst a) =
      ringRestriction R n (hst.trans htv) a := by
  have h1 := product_sdiff R n hst
  have h2 := product_sdiff R n htv
  have h3 : product R n v = product R n s *
      (product R n (t \ s) * product R n (v \ t)) := by rw [h2,h1,mul_assoc]
  exact (HomogeneousEval.awayMap_comp _ (product_homogeneous R n s)
    (product_homogeneous R n (t \ s)) (product_homogeneous R n (v \ t))
    h1 h2 h3 a).trans (HomogeneousEval.awayMap_same _ _ _ _ _ _)

lemma ringRestriction_self (s : Finset (Fin (n+1))) (a : Ring R n s) :
    ringRestriction R n (Finset.Subset.refl s) a = a := by
  have h1 : product R n s = product R n s * 1 := (mul_one _).symm
  exact (HomogeneousEval.awayMap_same _ _ (SetLike.one_mem_graded
    (ProjectiveCoefficientChart.grading R n)) _ h1 a).trans
      (HomogeneousEval.awayMap_one _ (product_homogeneous R n s) h1 a)

variable {s t v : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty) (hv : v.Nonempty)
variable (m : Fin n → ℤ)

 

def sectionsRestriction (hst : s ⊆ t) :
    Sections R n s hs m →ₛₗ[ringRestriction R n hst] Sections R n t ht m where
  toFun x := ⟨x.val,grid_target_mono R n m ∅ hst x.property⟩
  map_add' _ _ := rfl
  map_smul' a x := by
    apply Subtype.ext
    change scalarMap R n s a * x.val = scalarMap R n t (ringRestriction R n hst a) * x.val
    rw [scalarMap_restriction]

lemma sectionsRestriction_val (hst : s ⊆ t) (x : Sections R n s hs m) :
    (sectionsRestriction R n hs ht m hst x : GridAmbient R n) = x := rfl

lemma sectionsRestriction_comp (hst : s ⊆ t) (htv : t ⊆ v) (x : Sections R n s hs m) :
    sectionsRestriction R n ht hv m htv (sectionsRestriction R n hs ht m hst x) =
      sectionsRestriction R n hs hv m (hst.trans htv) x := rfl

lemma sectionsRestriction_self (x : Sections R n s hs m) :
    sectionsRestriction R n hs hs m (Finset.Subset.refl s) x = x := rfl

 
theorem sections_properties :
    Module.FinitePresentation (Ring R n s) (Sections R n s hs m) ∧
    Module.Projective (Ring R n s) (Sections R n s hs m) ∧
    ∀ p : PrimeSpectrum (Ring R n s),
      Module.rankAtStalk (Sections R n s hs m) p = n.factorial := by
  have hs' := hs
  obtain ⟨k,hk⟩ := hs'
  let : Fact (k ∈ s) := ⟨hk⟩
  exact Sections_properties R n k s hs m

end Lech.ProjectiveRoot

end

end OAI
