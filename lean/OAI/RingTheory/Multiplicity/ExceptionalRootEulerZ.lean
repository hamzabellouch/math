import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootThickeningEuler
import OAI.RingTheory.Multiplicity.RootStripComplement

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))

include hgen hds hmu ha in
lemma exceptionalZ_root_euler (r : Fin n → ℤ) (a : ℤ) :
    finiteHomologyEuler ell (exceptionalZ I z hz (fun j=>a-1-r j)) 0 n=
      ell.realValue (ModuleCat.of R (R ⧸ I))*∏ j,((a-r j:ℤ):ℝ) := by
  unfold TorsionLength.realValue
  rw [←exceptional_root_euler I z hz hgen ell hds hmu ha r a]
  unfold finiteHomologyEuler
  apply Finset.sum_congr rfl
  intro q hq
  congr 1
  change (ell.value _).toReal=(ell.value _).toReal
  congr 1
  have he := (exceptionalCech I z hz (fun j=>a-1-r j)).extendHomologyIso
    ComplexShape.embeddingUpNat (j:=q) (j':=(0:ℤ)+q) (by simp)
  exact ell.eq_of_iso he (exceptionalZ_torsion I z hz _ _) (exceptional_torsion I z hz _ q)

omit [LinearOrder (Chart n)] in
lemma raise_rootAmbient (s : ℕ) (r : Fin n → ℤ) (j : ℕ) :
    raise (rootAmbient s r 0) j=fun v => (-((n+1)*s:ℕ):ℤ)+j-1-r v := by
  funext v
  simp only [rootAmbient,baseTwist,raise_apply]
  ring

include hgen hds hmu ha in
lemma ambientStrip_euler (s : ℕ) (r : Fin n → ℤ) (N : ℕ) :
    (∑ j∈Finset.range N,finiteHomologyEuler ell
      (exceptionalZ I z hz (raise (rootAmbient s r 0) j)) 0 n)=
        ell.realValue (ModuleCat.of R (R ⧸ I))*rootPrefix n r (n+1) s N := by
  unfold rootPrefix
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [raise_rootAmbient,exceptionalZ_root_euler I z hz hgen ell hds hmu ha]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  push_cast
  ring
end Lech.ReesRoot

end

end OAI
