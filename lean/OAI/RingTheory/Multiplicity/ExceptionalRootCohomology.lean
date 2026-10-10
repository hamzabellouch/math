import Mathlib
import OAI.RingTheory.Multiplicity.CechIndexing
import OAI.RingTheory.Multiplicity.ReducedRootCohomology
import OAI.RingTheory.Multiplicity.RootFibreCech

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) [LinearOrder (Chart n)]
  (m : Fin n → ℤ) (I : Ideal R)

omit [LinearOrder (Chart n)] in
lemma cech_empty_zero : IsZero ((cechDiagram R n m).obj ∅) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  refine ⟨fun f g => funext fun hs => ?_⟩
  exact (Finset.not_nonempty_empty hs.down).elim

abbrev reducedPositive := FiniteModuleCech.positiveComplex
  (FiniteModuleCech.reduction (cechDiagram R n m) I)

def reducedPositiveHomologyIso (q : ℕ) :
    (reducedPositive R n m I).homology q ≅ (reducedCech R n m I).homology (q+1) :=
  FiniteModuleCech.positiveHomologyIso _
    ((TensorIdeal.quotientFunctor I).map_isZero (cech_empty_zero R n m)) q

variable (ell : TorsionLength I)
omit [LinearOrder (Chart n)] in
lemma reducedPositive_length_eq (q : ℕ) :
    ell.value ((reducedPositive R n m I).homology q) =
      ell.value ((reducedCech R n m I).homology (q+1)) :=
  ell.eq_of_iso (reducedPositiveHomologyIso R n m I q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (FiniteModuleCech.reduction_homology_torsion _ I (q+1))

lemma reducedPositive_length :
    ell.value ((reducedPositive R n m I).homology (negativeCount m)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) := by
  rw [reducedPositive_length_eq,reduced_length]

lemma reducedPositive_length_zero (q : ℕ) (hq : q≠negativeCount m) :
    ell.value ((reducedPositive R n m I).homology q)=0 := by
  rw [reducedPositive_length_eq,reduced_length_zero R n m I ell (q+1) (by omega)]

lemma reducedPositive_length_finite (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤) (q : ℕ) :
    ell.value ((reducedPositive R n m I).homology q)≠⊤ := by
  rw [reducedPositive_length_eq]
  exact reduced_length_finite R n m I ell hmu (q+1)
end Lech.ProjectiveRoot

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

abbrev exceptionalCech := FiniteModuleCech.positiveComplex (exceptionalDiagram I z hz m)

include hgen hds hmu ha in
omit [LinearOrder (Chart n)] in
lemma exceptional_length_eq (q : ℕ) :
    ell.value ((exceptionalCech I z hz m).homology q) =
      ell.value ((ProjectiveRoot.reducedPositive R n m I).homology q) :=
  (ell.eq_of_isoModSerre (homologyMap (fibreCechMap I z hz m).positiveComplex q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (FiniteModuleCech.reduction_positiveHomology_torsion _ I q)
    (fibreCech_homology I z hz m hgen ell hds hmu ha q)).symm

include hgen hds hmu ha in
 
theorem exceptional_length :
    ell.value ((exceptionalCech I z hz m).homology (negativeCount m)) =
      signedRank m • ell.value (ModuleCat.of R (R ⧸ I)) := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha,
    ProjectiveRoot.reducedPositive_length]

include hgen hds hmu ha in
lemma exceptional_length_zero (q : ℕ) (hq : q≠negativeCount m) :
    ell.value ((exceptionalCech I z hz m).homology q)=0 := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha,
    ProjectiveRoot.reducedPositive_length_zero R n m I ell q hq]

include hgen hds hmu ha in
lemma exceptional_length_finite (q : ℕ) :
    ell.value ((exceptionalCech I z hz m).homology q)≠⊤ := by
  rw [exceptional_length_eq I z hz m hgen ell hds hmu ha]
  exact ProjectiveRoot.reducedPositive_length_finite R n m I ell hmu q

omit [LinearOrder (Chart n)] in
lemma exceptional_torsion (q : ℕ) : powerTorsion I ((exceptionalCech I z hz m).homology q) :=
  FiniteModuleCech.reduction_positiveHomology_torsion _ I q

include hgen hds hmu ha in
 
theorem exceptional_root_euler (r : Fin n → ℤ) (a : ℤ) :
    ∑ q ∈ Finset.range (n+1), (-1:ℝ)^q *
      (ell.value ((exceptionalCech I z hz (fun j => a-1-r j)).homology q)).toReal =
        (ell.value (ModuleCat.of R (R ⧸ I))).toReal * ∏ j,((a-r j:ℤ):ℝ) := by
  let m : Fin n → ℤ := fun j => a-1-r j
  have hn : negativeCount m ≤ n := negativeCount_le m
  rw [Finset.sum_eq_single (negativeCount m)]
  · rw [exceptional_length I z hz m hgen ell hds hmu ha,ENNReal.toReal_nsmul]
    simp only [nsmul_eq_mul]
    have he := root_signedRank_real (n:=n) r a
    rw [rootDegree,←negativeCount_root] at he
    change (-1:ℝ)^negativeCount m * ((signedRank m:ℝ) * _) = _
    rw [←mul_assoc,he,mul_comm]
  · intro q hq hneq
    rw [exceptional_length_zero I z hz m hgen ell hds hmu ha q hneq,ENNReal.toReal_zero,mul_zero]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

end Lech.ReesRoot

end

end OAI
