import Mathlib
import OAI.RingTheory.Multiplicity.ReesRootEulerFunction
import OAI.RingTheory.Multiplicity.ReesRootLayerCech
import OAI.RingTheory.Multiplicity.SymmetricAffine
import OAI.RingTheory.Multiplicity.TensorCechRankEuler

namespace OAI

noncomputable section
namespace Lech.ReesRoot
open CategoryTheory CategoryTheory.Limits FiniteModuleCech ProductSourceCover
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
lemma unfilteredEuler_diagonal (m : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h (fun i => m i+1)=unfilteredEuler I z hz ell F h m := by
  have hE (q : ℤ) : ell.finiteClass ((positiveZ (exceptionalDiagram I z hz m)).homology q) :=
    exceptionalZ_finite I z hz m hgen ell hds hmu ha q
  have he := tensorEuler_additive (cechInclusionDiagram I z hz m) (layerProjection I z hz m)
    (layerDiagram_zero I z hz m hgen) ell F h hb hflat
    (layerDiagram_shortExact I z hz m hgen)
    (unfilteredTotal_finite I z hz F h _ hgen ell hds hmu ha b B hflat hp hfin hb hac)
    (tensorCech_finite_of_positive ell F h b B hflat hb (exceptionalDiagram I z hz m) hE)
  have hzE := tensor_euler_rank_zero ell F h b B hflat hb (exceptionalDiagram I z hz m) hE hbr
  change unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h (fun i => m i+1)+
    tensorEuler ell F h (exceptionalDiagram I z hz m) at he
  rw [hzE,add_zero] at he
  exact he.symm

include hgen hds hmu ha B hflat hp hfin hb hac hbr in
 
theorem unfilteredEuler_constant (m m' : Fin n → ℤ) :
    unfilteredEuler I z hz ell F h m=unfilteredEuler I z hz ell F h m' := by
  have hc := IntegerWeights.symmetric_affine_diagonal_constant n (unfilteredEuler I z hz ell F h)
    (IntegerWeights.separatelyAffine_of_step _
      (unfilteredEuler_affine_step I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac))
    (by
      intro σ w
      have he := unfilteredEuler_permute I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac σ.symm w
      exact he.symm)
    (unfilteredEuler_diagonal I z hz ell F h hgen hds hmu ha b B hflat hp hfin hb hac hbr)
  exact (hc m).trans (hc m').symm
end Lech.ReesRoot

end

end OAI
