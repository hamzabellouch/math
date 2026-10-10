import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootEulerPositivity

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)

lemma zero_order_bound (p : ℤ) :
    (F.d p (p+1)).hom.range ≤ I^0 • (⊤ : Submodule R (F.X (p+1))) := by simp

lemma zero_term_top (Q : ModuleCat.{u} R) (p : ℤ) : term I F h 0 Q p=⊤ := by
  simp [term,order]

def zeroTermEquiv (Q : ModuleCat.{u} R) (p : ℤ) :
    (complex I F h 0 (zero_order_bound I F) Q).X p ≃ₗ[R] (tensorComplex F Q).X p :=
  LinearEquiv.ofBijective (term I F h 0 Q p).subtype ⟨Subtype.val_injective,by
    intro x
    exact ⟨⟨x,by rw [zero_term_top]; trivial⟩,rfl⟩⟩

@[simp] lemma zeroTermEquiv_apply (Q : ModuleCat.{u} R) (p : ℤ)
    (x : (complex I F h 0 (zero_order_bound I F) Q).X p) :
    zeroTermEquiv I F h Q p x=x.val := rfl
end Lech.IdealFiltered

namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂ MonoidalCategory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ) (m : Fin n → ℤ)

 
def unfilteredAt : TotalGhost.Bic (R:=R) :=
  (((curriedTensor (ModuleCat.{u} R)).mapBifunctorHomologicalComplex (.up ℤ) (.up ℤ)).obj F).obj
    (cechZ I z hz m)

 

def zeroOrderIso :
    enlargedAt I z hz F h 0 (IdealFiltered.zero_order_bound I F) m ≅ unfilteredAt I z hz F m :=
  Hom.isoOfComponents (fun p => Hom.isoOfComponents
    (fun q => (IdealFiltered.zeroTermEquiv I F h ((cechZ I z hz m).X q) p).toModuleIso)
    (by intro q r hqr; rfl)) (by
      intro p r hpr
      apply Hom.ext
      funext q
      rfl)

 
def zeroOrderTotalIso :
    (enlargedAt I z hz F h 0 (IdealFiltered.zero_order_bound I F) m).total (.up ℤ) ≅
      (TensorTotal.Right.functor F).obj (cechZ I z hz m) :=
  BicomplexTotal.functor.mapIso (zeroOrderIso I z hz F h m)

variable [LinearOrder (ProductSourceCover.Chart n)]
  (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)

include hgen hds hmu ha B hflat hp hfin hb hac in
 

lemma unfilteredTotal_finite (i : ℤ) :
    ell.finiteClass (((TensorTotal.Right.functor F).obj (cechZ I z hz m)).homology i) := by
  have hf := enlargedAtTotal_finite I z hz F h 0 (IdealFiltered.zero_order_bound I F) m
    hgen hflat ell hds hmu ha b B hp hfin hb hac i
  exact (ell.finiteClass).prop_of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
    (zeroOrderTotalIso I z hz F h m)) hf
end Lech.ReesRoot

end

end OAI
