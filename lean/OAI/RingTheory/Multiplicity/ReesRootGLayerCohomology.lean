import Mathlib
import OAI.RingTheory.Multiplicity.FiniteFreeTensorCohomology
import OAI.RingTheory.Multiplicity.ReesRootGLayer

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

abbrev exceptionalZ := (exceptionalCech I z hz m).extend ComplexShape.embeddingUpNat

omit [LinearOrder (Chart n)] in
lemma exceptionalZ_negative (q : ℤ) (hq : q<0) : IsZero ((exceptionalZ I z hz m).homology q) := by
  apply HomologicalComplex.ExactAt.isZero_homology
  apply HomologicalComplex.extend_exactAt
  intro p hp
  change (p:ℤ)=q at hp
  omega

omit [LinearOrder (Chart n)] in
lemma exceptionalZ_torsion (q : ℤ) : powerTorsion I ((exceptionalZ I z hz m).homology q) := by
  cases q with
  | ofNat q =>
      exact (powerTorsion I).prop_of_iso
        ((exceptionalCech I z hz m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm
        (exceptional_torsion I z hz m q)
  | negSucc q => exact powerTorsion_zero I (exceptionalZ_negative I z hz m _ (by omega))

include hgen hds hmu ha in
lemma exceptionalZ_finite (q : ℤ) : ell.finiteClass ((exceptionalZ I z hz m).homology q) := by
  cases q with
  | ofNat q =>
      apply ell.finiteClass.prop_of_iso
        ((exceptionalCech I z hz m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm
      exact ⟨exceptional_torsion I z hz m q,exceptional_length_finite I z hz m hgen ell hds hmu ha q⟩
  | negSucc q => exact ell.finiteClass.prop_of_isZero (exceptionalZ_negative I z hz m _ (by omega))

include hgen hds hmu ha in
lemma exceptionalZ_zero (q : ℤ) (hq : q≠(negativeCount m:ℤ)) :
    ell.zeroClass ((exceptionalZ I z hz m).homology q) := by
  cases q with
  | ofNat q =>
      apply ell.zeroClass.prop_of_iso
        ((exceptionalCech I z hz m).extendHomologyIso ComplexShape.embeddingUpNat (j:=q) rfl).symm
      exact ⟨exceptional_torsion I z hz m q,
        exceptional_length_zero I z hz m hgen ell hds hmu ha q (by
          intro he
          apply hq
          exact congrArg (fun v : ℕ => (v : ℤ)) he)⟩
  | negSucc q => exact ell.zeroClass.prop_of_isZero (exceptionalZ_negative I z hz m _ (by omega))

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (p : ℤ) [Module.Flat R (F.X p)] (b : ℕ) (B : Module.Basis (Fin b) R (F.X p))

omit [LinearOrder (Chart n)] in
def layerAtRowHomologyBasisIso (q : ℤ) :
    ((layerAt I z hz F h s hd m).X p).homology q ≅
      ModuleCat.of R (Fin b → (exceptionalZ I z hz (raise m (IdealFiltered.order h s p))).homology q) :=
  (homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso (layerAtRowIso I z hz F h s hd m hgen p).symm ≪≫
    TensorIdeal.tensorHomologyBasisIso (F.X p) b B _ q

omit [LinearOrder (Chart n)] in
include B hgen in
lemma layerAtRow_torsion (q : ℤ) : powerTorsion I (((layerAt I z hz F h s hd m).X p).homology q) :=
  (powerTorsion I).prop_of_iso (layerAtRowHomologyBasisIso I z hz m hgen F h s hd p b B q).symm
    (powerTorsion_fin b (exceptionalZ_torsion I z hz _ q))

omit [LinearOrder (Chart n)] in
include B hgen in
lemma layerAtRow_length (q : ℤ) :
    ell.value (((layerAt I z hz F h s hd m).X p).homology q) =
      b • ell.value ((exceptionalZ I z hz (raise m (IdealFiltered.order h s p))).homology q) :=
  (ell.eq_of_iso (layerAtRowHomologyBasisIso I z hz m hgen F h s hd p b B q)
    (layerAtRow_torsion I z hz m hgen F h s hd p b B q)
    (powerTorsion_fin b (exceptionalZ_torsion I z hz _ q))).trans
      (ell.value_fin (exceptionalZ_torsion I z hz _ q) b)

include B hgen hds hmu ha in
lemma layerAtRow_finite (q : ℤ) : ell.finiteClass (((layerAt I z hz F h s hd m).X p).homology q) := by
  refine ⟨layerAtRow_torsion I z hz m hgen F h s hd p b B q,?_⟩
  rw [layerAtRow_length I z hz m hgen ell F h s hd p b B q,nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) (exceptionalZ_finite I z hz _ hgen ell hds hmu ha q).2

include B hgen hds hmu ha in
lemma layerAtRow_zero (q : ℤ) (hq : q≠(negativeCount (raise m (IdealFiltered.order h s p)):ℤ)) :
    ell.zeroClass (((layerAt I z hz F h s hd m).X p).homology q) := by
  refine ⟨layerAtRow_torsion I z hz m hgen F h s hd p b B q,?_⟩
  rw [layerAtRow_length I z hz m hgen ell F h s hd p b B q,
    (exceptionalZ_zero I z hz _ hgen ell hds hmu ha q hq).2,smul_zero]
end Lech.ReesRoot

end

end OAI
