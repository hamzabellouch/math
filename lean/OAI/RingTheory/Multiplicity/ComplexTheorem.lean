import Mathlib
import OAI.RingTheory.Multiplicity.ComplexEstimate
import OAI.RingTheory.Multiplicity.LocalContractibility

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u
variable {R : Type u} [CommRing R] {I : Ideal R}

 

def TorsionLength.FilteredColimitZero (ell : TorsionLength I) : Prop :=
  ∀ {J : Type u} [SmallCategory J] [IsFiltered J] (D : J ⥤ ModuleCat.{u} R)
    (a : ℕ), (∀ j,I^a ≤ Module.annihilator R (D.obj j)) →
      (∀ j,ell.value (D.obj j)=0) → ell.value (colimit D)=0

def TorsionLength.ZeroStability (ell : TorsionLength I) : Prop :=
  ell.DirectSumZero ∧ ell.FilteredColimitZero


 

theorem complex_theorem (n : ℕ) :
    ∃ A : ℝ,0≤A ∧ ∀ {R : Type u} [CommRing R]
      (I : Ideal R) (z : Fin (n+1) → R)
      (_hgen : Ideal.span (Set.range z)=I)
      (ell : TorsionLength I) (_hst : ell.ZeroStability)
      (_hmupos : 0<ell.value (ModuleCat.of R (R ⧸ I)))
      (_hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
      (_ha : ∀ a : ℕ,1≤a → ell.value (ModuleCat.of R
        (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=
          a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} R) ℤ)
      (_hf : ∀ p,Module.Free R (F.X p)) (_hfin : ∀ p,Module.Finite R (F.X p))
      (_hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
      (_hloc : LocallyContractibleOff I F),
        (∀ i,powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
        (∀ i : ℤ,i≠0 → ell.value (F.homology i)=0) ∧
        ∀ s : ℕ, 1 ≤ s →
          (∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1)))) →
          (∑ i∈Finset.range (n+2),(-1:ℝ)^i*(Module.finrank R (F.X (-(i:ℤ))):ℝ)=0) →
          ell.realValue (ModuleCat.of R (R ⧸ I))*(s:ℝ)^(n+1)*
            ((Module.finrank R (F.X 0):ℝ)-A/s*
              ∑ i∈Finset.range (n+2),(Module.finrank R (F.X (-(i:ℤ))):ℝ))≤
              ell.realValue (F.homology 0) := by
  classical
  let : LinearOrder (Chart n) := LinearOrder.lift' (Fintype.equivFin (Chart n))
    (Fintype.equivFin (Chart n)).injective
  obtain ⟨A,hA,H⟩ := complex_estimate_basis n
  refine ⟨A,hA,?_⟩
  intro R _ I z hgen ell hst hmupos hmu ha hK F hf hfin hb hloc
  rcases subsingleton_or_nontrivial R with hr|hr
  · let := hr
    have he : ell.value (ModuleCat.of R (R ⧸ I))=0 :=
      ell.zero (ModuleCat.isZero_iff_subsingleton.mpr inferInstance)
    exact False.elim ((ne_of_gt hmupos) he)
  · let := hr
    let b : ℤ → ℕ := fun p => Module.finrank R (F.X p)
    let B : ∀ p,Module.Basis (Fin (b p)) R (F.X p) := fun p => by
      letI := hf p
      letI := hfin p
      exact Module.finBasis R (F.X p)
    have hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic :=
      fun k => hloc.acyclicAway (z k) (hgen ▸ Ideal.subset_span ⟨k,rfl⟩)
    obtain ⟨ht,hzero,hest⟩ := H I z hgen ell hst.1 hmu (fun a ha0 => ha a (by omega)) hK F b B hb hac
    exact ⟨ht,hzero,fun s hs hd halt => hest s (by omega) hd halt⟩
end Lech

end

end OAI
