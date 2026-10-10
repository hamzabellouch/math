import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootPositivity

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {I : Ideal R} (ell : TorsionLength I)

lemma finiteHomologyEuler_pure_zero (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : ∀ i : ℤ,i≠0 → ell.zeroClass (K.homology i)) (h N : ℕ) (hN : h≤N) :
    (-1:ℝ)^h * finiteHomologyEuler ell K (-(h:ℤ)) N=ell.realValue (K.homology 0) := by
  classical
  unfold finiteHomologyEuler
  rw [Finset.sum_eq_single h]
  · simp only [neg_add_cancel]
    rw [←mul_assoc,←pow_add,show h+h=2*h by omega,pow_mul]
    norm_num
  · intro j hj hjh
    have hz := (hK (-(h:ℤ)+j) (by omega)).2
    change ell.value (K.homology (-(h:ℤ)+j))=0 at hz
    simp only [TorsionLength.realValue,hz,ENNReal.toReal_zero,mul_zero]
  · intro hh
    exact (hh (Finset.mem_range.mpr (by omega))).elim

namespace ReesRoot
open ProductSourceCover
variable (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
 
theorem rootTotal_pure (r : Fin n → ℤ) (hr : RootPositions n s r) (i : ℤ) (hi : i≠0) :
    ell.zeroClass (((enlargedAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ)).homology i) := by
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact rootTotal_negative_degree I z hz F s hd hgen hflat ell hds hmu ha b B hp hfin hac r hr hb i hi
  · exact rootTotal_positive_degree I z hz F s hd hgen hflat ell hds hmu ha b B hp hfin hac r hr hb i hi

include hgen hds hmu ha B hflat hp hfin hb hac in
 

theorem rootTotal_euler_nonnegative (r : Fin n → ℤ) (hr : RootPositions n s r)
    (N : ℕ) (hN : n+1≤N) :
    let D := (enlargedAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ)
    (∀ i,ell.finiteClass (D.homology i)) ∧
      (-1:ℝ)^(n+1)*finiteHomologyEuler ell D (-(n+1:ℤ)) N=ell.realValue (D.homology 0) ∧
      0≤(-1:ℝ)^(n+1)*finiteHomologyEuler ell D (-(n+1:ℤ)) N := by
  dsimp only
  have he := finiteHomologyEuler_pure_zero ell _
    (rootTotal_pure I z hz hgen ell hds hmu ha F s hd b B hflat hp hfin hb hac r hr) (n+1) N hN
  simp only [Nat.cast_add,Nat.cast_one] at he
  refine ⟨?_,he,?_⟩
  · intro i
    exact enlargedAtTotal_finite I z hz F (n+1) s hd _ hgen hflat ell hds hmu ha b B hp hfin hb hac i
  · rw [he]
    exact ENNReal.toReal_nonneg
end ReesRoot
end Lech

end

end OAI
