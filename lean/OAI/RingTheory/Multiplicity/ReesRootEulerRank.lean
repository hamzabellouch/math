import Mathlib
import OAI.RingTheory.Multiplicity.CechCopies
import OAI.RingTheory.Multiplicity.ReesRootEulerConstant

namespace OAI

noncomputable section
namespace Lech.UniversalSplitting
lemma powerIndex_card (n : ℕ) : Fintype.card (PowerIndex n)=n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change Fintype.card (Fin (n+1) × PowerIndex n)=(n+1).factorial
      rw [Fintype.card_prod,Fintype.card_fin,ih,Nat.factorial_succ]
end Lech.UniversalSplitting
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover UniversalSplitting
universe u
variable {R : Type u} [CommRing R] (I : Ideal R) {n : ℕ}
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ) (h : ℕ)
  [LinearOrder (Chart n)]
  (hgen : Ideal.span (Set.range z)=I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun i => z i^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hflat : ∀ p,Module.Flat R (F.X p)) (hp : ∀ p,Module.Projective R (F.X p))
  (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(h:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0)

include hgen hds hmu ha B hflat hp hfin hb hac hbr in
 

theorem unfilteredEuler_rank (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=
      (n.factorial:ℝ)*tensorEuler ell F h (scalarCechDiagram I z hz) := by
  have he : positiveComplex (cechDiagram I z hz (fun i => (powerWeight n i:ℤ))) ≅
      positiveComplex (copiesDiagram (scalarCechDiagram I z hz) (PowerIndex n)) :=
    (ulrichCechIso I z hz).trans (positiveIso (fun _ => LinearEquiv.refl R _) (fun _ _ => rfl))
  have hf (q : ℤ) := unfilteredTotal_finite I z hz F h
    (fun i => (powerWeight n i:ℤ)) hgen ell hds hmu ha b B hflat hp hfin hb hac q
  have hC (q : ℤ) : ell.finiteClass
      ((tensorCech F (copiesDiagram (scalarCechDiagram I z hz) (PowerIndex n))).homology q) :=
    ell.finiteClass.prop_of_iso ((HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).mapIso
      ((TensorTotal.Right.functor F).mapIso
        ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat.{u} R)).mapIso he))) (hf q)
  have hk : Nonempty (PowerIndex n) := Fintype.card_pos_iff.mp (by rw [powerIndex_card]; exact Nat.factorial_pos n)
  rw [unfilteredEuler_constant I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac hbr
    m (fun i => (powerWeight n i:ℤ))]
  unfold unfilteredEuler
  rw [tensorEuler_iso ell F h he hf,
    tensorEuler_copies (scalarCechDiagram I z hz) ell F h hb hflat hk.some hC,powerIndex_card]
end Lech.ReesRoot

end

end OAI
