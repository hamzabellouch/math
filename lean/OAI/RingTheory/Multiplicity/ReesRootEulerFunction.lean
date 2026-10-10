import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootCechEuler
import OAI.RingTheory.Multiplicity.ReesRootPermutation
import OAI.RingTheory.Multiplicity.TensorCechEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)

 
def unfilteredEuler (m : Fin n → ℤ) : ℝ := tensorEuler ell F h (cechDiagram I z hz m)

variable [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
lemma unfilteredEuler_affine_step (m : Fin n → ℤ) (i : Fin n) :
    unfilteredEuler I z hz ell F h m+unfilteredEuler I z hz ell F h (Pi.single i 1+(Pi.single i 1+m))=
      2*unfilteredEuler I z hz ell F h (Pi.single i 1+m) := by
  have hf (m : Fin n → ℤ) (q : ℤ) : ell.finiteClass ((tensorCech F (cechDiagram I z hz m)).homology q) :=
    unfilteredTotal_finite I z hz F h m hgen ell hds hmu ha b B hflat hp hfin hb hac q
  have he := tensorEuler_additive (eulerCechLeft I z hz m i) (eulerCechRight I z hz m i)
    (eulerCech_zero I z hz m i) ell F h hb hflat (eulerCech_shortExact I z hz m i) (hf m) (hf _)
  have hg := tensorEuler_prod ell F h hb hflat (cechDiagram I z hz (Pi.single i 1+m))
    (cechDiagram I z hz (Pi.single i 1+m)) (hf _) (hf _)
  change tensorEuler ell F h (prodDiagram _ _)=_ at he
  rw [hg] at he
  change _+_=2*_ 
  dsimp only [unfilteredEuler]
  linarith

include hgen hds hmu ha B hflat hp hfin hb hac in
lemma unfilteredEuler_permute (σ : Equiv.Perm (Fin n)) (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h (permuteWeight n σ m) :=
  tensorEuler_iso ell F h (permuteCechIso I z hz σ m)
    (unfilteredTotal_finite I z hz F h m hgen ell hds hmu ha b B hflat hp hfin hb hac)
end Lech.ReesRoot

end

end OAI
