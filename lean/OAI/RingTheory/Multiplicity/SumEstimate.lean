import Mathlib
import OAI.RingTheory.Multiplicity.ExceptionalRootEulerZ
import OAI.RingTheory.Multiplicity.ReesRootEulerRank
import OAI.RingTheory.Multiplicity.ReesRootQuotientEuler
import OAI.RingTheory.Multiplicity.ScalarCechEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover FiniteModuleCech
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {n : ℕ}
  [LinearOrder (Chart n)]
  (z : Fin (n+1) → R) (hz : ∀ j,z j∈I) (hgen : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (hds : ell.DirectSumZero)
  (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
  (ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
    (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
  (hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
    ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
  (F : CochainComplex (ModuleCat.{u} R) ℤ) (s : ℕ)
  (hd : ∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (b : ℤ → ℕ) (B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
  (hf : ∀ p,Module.Free R (F.X p)) (hfin : ∀ p,Module.Finite R (F.X p))
  (hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
  (hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic)
  (hbr : ∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)=0)

omit [Nontrivial R] in
include hgen hds hmu ha B hf hb hbr in
lemma quotient_root_euler (r : Fin n → ℤ) :
    (-1:ℝ)^(n+1)*finiteHomologyEuler ell
      ((quotientAt I z hz F (n+1) s hd (rootAmbient s r 0)).total (.up ℤ))
        (-(n+1:ℤ)) ((n+1)+(n+1))=
      -(ell.realValue (ModuleCat.of R (R ⧸ I)))*
        ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s := by
  have hflat : ∀ p,Module.Flat R (F.X p) := fun p => by have := hf p; infer_instance
  have he := quotientAtTotal_euler I z hz F (n+1) s hd (rootAmbient s r 0)
    hb hgen ell hds hmu ha b B hflat ((n+1)+(n+1)) (by omega)
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hrw : (∑ k∈Finset.range (n+1+1),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*
      ∑ j∈Finset.range (IdealFiltered.order (n+1) s (-(n+1:ℤ)+k)),
        finiteHomologyEuler ell (exceptionalZ I z hz (raise (rootAmbient s r 0) j)) 0 n)=
      ell.realValue (ModuleCat.of R (R ⧸ I))*
        ∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*rootPrefix n r (n+1) s (k*s) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have ho : IdealFiltered.order (n+1) s (-(n+1:ℤ)+k)=k*s := by
      unfold IdealFiltered.order
      congr 1
      omega
    rw [ho,ambientStrip_euler I z hz hgen ell hds hmu ha]
    ring
  rw [he,hrw]
  calc
    _=ell.realValue (ModuleCat.of R (R ⧸ I))*
        ((-1:ℝ)^(n+1)*(∑ k∈Finset.range (n+2),(-1:ℝ)^k*(b (-(n+1:ℤ)+k):ℝ)*
          rootPrefix n r (n+1) s (k*s))) := by ring
    _=_ := by
      have hc := complement_euler n r (n+1) s (fun p => (b p:ℝ)) hbr
      simp only [Nat.cast_add,Nat.cast_one] at hc
      rw [hc]
      ring

include hz hgen hds hmu ha hK hd B hf hfin hb hac hbr in
 

theorem sum_estimate (r : Fin n → ℤ) (hr : RootPositions n s r) :
    0≤(n.factorial:ℝ)*ell.realValue (F.homology 0)+
      ell.realValue (ModuleCat.of R (R ⧸ I))*
        ∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*rootStripPolynomial n r i s := by
  have hflat : ∀ p,Module.Flat R (F.X p) := fun p => by have := hf p; infer_instance
  have hp : ∀ p,Module.Projective R (F.X p) := fun p => by have := hf p; infer_instance
  have hpos := (rootTotal_euler_nonnegative I z hz hgen ell hds hmu ha F s hd b B hflat hp hfin hb hac
    r hr ((n+1)+(n+1)) (by omega)).2.2
  have he := ambient_euler_additive I z hz F (n+1) s hd (rootAmbient s r 0)
    hb hgen ell hds hmu ha b B hflat hp hfin hac ((n+1)+(n+1)) (by omega)
  have hu : (-1:ℝ)^(n+1)*finiteHomologyEuler ell
      ((unfilteredAt I z hz F (rootAmbient s r 0)).total (.up ℤ))
        (-(n+1:ℤ)) ((n+1)+(n+1))=(n.factorial:ℝ)*ell.realValue (F.homology 0) := by
    rw [←(show tensorCech F (cechDiagram I z hz (rootAmbient s r 0))=
      (unfilteredAt I z hz F (rootAmbient s r 0)).total (.up ℤ) from rfl)]
    have huv := unfilteredEuler_rank I z hz ell F (n+1) hgen hds hmu ha b B hflat hp hfin hb hac hbr
      (rootAmbient s r 0)
    rw [scalarEuler_value I z hz F hgen ell hds hmu ha hK hf hfin hb hac] at huv
    simpa only [unfilteredEuler,tensorEuler,Fintype.card_fin,Nat.cast_add,Nat.cast_one] using huv
  have hq := quotient_root_euler I z hz hgen ell hds hmu ha F s hd b B hf hb hbr r
  simp only [Nat.cast_add,Nat.cast_one] at he
  have hh := congrArg (fun x : ℝ => (-1:ℝ)^(n+1)*x) he
  rw [mul_add,hu,hq] at hh
  linarith only [hh,hpos]
end Lech.ReesRoot

end

end OAI
