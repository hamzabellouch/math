import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootGLayerCohomology

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
open ProductSourceCover
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ} [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (m : Fin n → ℤ)
  (hgen : Ideal.span (Set.range z)=I) (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p))

omit [LinearOrder (Chart n)] in
lemma layerAt_isZero (p : ℤ) (hp : IsZero (F.X p)) :
    IsZero ((layerAt I z hz F h s hd m).X p) := by
  apply FiniteComplex.isZero_of_X
  intro q
  exact (TensorIdeal.quotientFunctor I).map_isZero (enlargedAt_isZero I z hz F h s hd m p q hp)

include hgen hds hmu ha B hflat in
lemma layerAtTotal_finite (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p)) (k : ℤ) :
    ell.finiteClass (((layerAt I z hz F h s hd m).total (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage ell.finiteClass (-(h:ℤ)) (h+1) _ k
  · intro p hp
    exact layerAt_isZero I z hz m F h s hd p (hb p (by omega))
  intro p
  apply ell.finiteClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p k).symm
  let := hflat p
  exact layerAtRow_finite I z hz m hgen ell hds hmu ha F h s hd p (b p) (B p) (-p+k)

 
def rootLayerAt (r : Fin n → ℤ) (l : ℤ) : TotalGhost.Bic (R:=R) :=
  layerAt I z hz F (n+1) s hd (baseTwist (n+1) s (fun j => l-1-r j))

omit [LinearOrder (Chart n)] in
lemma rootLayerAt_twist (r : Fin n → ℤ) (l p : ℤ) (hp : -(n+1:ℤ)≤p ∧ p≤0) :
    raise (baseTwist (n+1) s (fun j => l-1-r j)) (IdealFiltered.order (n+1) s p)=
      fun j => (l-((-p).toNat:ℤ)*(s:ℤ))-1-r j := by
  have hi : ((-p).toNat:ℤ) = -p := Int.toNat_of_nonneg (by omega)
  have he : p = -((-p).toNat:ℤ) := by omega
  conv_lhs => rw [he,enlarged_twist (n+1) s _ (-p).toNat (by omega)]
  funext j
  simp only [Nat.cast_mul]
  ring

include hgen hds hmu ha B hflat in
 
theorem rootLayerAtTotal_nonnegative (r : Fin n → ℤ) (hr : RootPositions n s r)
    (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
    (l : ℤ) (hl : 0≤l) (k : ℤ) (hk : 0<k) :
    ell.zeroClass (((rootLayerAt I z hz F s hd r l).total (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage ell.zeroClass (-(n+1:ℤ)) (n+2) _ k
  · intro p hp
    exact layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))
  intro p
  apply ell.zeroClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p k).symm
  by_cases hp : -(n+1:ℤ)≤p ∧ p≤0
  · let := hflat p
    apply layerAtRow_zero I z hz _ hgen ell hds hmu ha F (n+1) s hd p (b p) (B p)
    rw [rootLayerAt_twist s r l p hp,negativeCount_root]
    have hi : ((-p).toNat:ℤ) = -p := Int.toNat_of_nonneg (by omega)
    have hc := rootDegree_nonnegative_layer n hr (-p).toNat l hl
    change (Finset.univ.filter (fun j => l-((-p).toNat:ℤ)*(s:ℤ)<r j)).card≤(-p).toNat at hc
    omega
  · exact ell.zeroClass.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-p+k)).map_isZero
      (layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))))

include hgen hds hmu ha B hflat in
 
theorem rootLayerAtTotal_negative (r : Fin n → ℤ) (hr : RootPositions n s r)
    (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
    (l : ℤ) (hl : l<0) (k : ℤ) (hk : k < -1) :
    ell.zeroClass (((rootLayerAt I z hz F s hd r l).total (.up ℤ)).homology k) := by
  apply BicomplexTotal.devissage ell.zeroClass (-(n+1:ℤ)) (n+2) _ k
  · intro p hp
    exact layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))
  intro p
  apply ell.zeroClass.prop_of_iso (BicomplexTotal.singleHomologyIso _ p k).symm
  by_cases hp : -(n+1:ℤ)≤p ∧ p≤0
  · let := hflat p
    apply layerAtRow_zero I z hz _ hgen ell hds hmu ha F (n+1) s hd p (b p) (B p)
    rw [rootLayerAt_twist s r l p hp,negativeCount_root]
    have hi : ((-p).toNat:ℤ) = -p := Int.toNat_of_nonneg (by omega)
    have hc := rootDegree_negative_layer n hr (-p).toNat (by omega) l hl
    change (-p).toNat-1≤(Finset.univ.filter (fun j => l-((-p).toNat:ℤ)*(s:ℤ)<r j)).card at hc
    omega
  · exact ell.zeroClass.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) (-p+k)).map_isZero
      (layerAt_isZero I z hz _ F (n+1) s hd p (hb p (by omega))))
end Lech.ReesRoot

end

end OAI
