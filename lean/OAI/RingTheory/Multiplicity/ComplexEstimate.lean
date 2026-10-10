import Mathlib
import OAI.RingTheory.Multiplicity.NumericalSupport
import OAI.RingTheory.Multiplicity.SumEstimate

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex ProductSourceCover
universe u


lemma rank_zero_reverse (h : ℕ) (b : ℤ → ℕ)
    (hb : ∑ i∈Finset.range (h+1),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)=0) :
    ∑ k∈Finset.range (h+1),(-1:ℝ)^k*(b (-(h:ℤ)+k):ℝ)=0 := by
  have he := signed_reverse h (fun p => (b p:ℝ)) (fun _=>1)
  simp only [mul_one,hb] at he
  exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (by norm_num))

 

theorem complex_estimate_basis (n : ℕ) [LinearOrder (Chart n)] :
    ∃ A : ℝ,0≤A ∧ ∀ {R : Type u} [CommRing R] [Nontrivial R]
      (I : Ideal R) (z : Fin (n+1) → R)
      (_hgen : Ideal.span (Set.range z)=I)
      (ell : TorsionLength I) (_hds : ell.DirectSumZero)
      (_hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
      (_ha : ∀ a : ℕ,0<a → ell.value (ModuleCat.of R
        (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=
          a^(n+1) • ell.value (ModuleCat.of R (R ⧸ I)))
      (_hK : ∀ a : ℕ,1≤a → ∀ i : ℤ,i<0 →
        ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
      (F : CochainComplex (ModuleCat.{u} R) ℤ)
      (b : ℤ → ℕ) (_B : ∀ p,Module.Basis (Fin (b p)) R (F.X p))
      (_hb : ∀ p,p < -(n+1:ℤ) ∨ 0<p → IsZero (F.X p))
      (_hac : ∀ k,((baseChangeFunctor R (Localization.Away (z k))).mapHomologicalComplex _ |>.obj F).Acyclic),
        (∀ i,powerTorsion I (F.homology i) ∧ ell.value (F.homology i)≠⊤) ∧
        (∀ i : ℤ,i≠0 → ell.value (F.homology i)=0) ∧
        ∀ s : ℕ,0<s →
          (∀ p : ℤ,(F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1)))) →
          (∑ i∈Finset.range (n+2),(-1:ℝ)^i*(b (-(i:ℤ)):ℝ)=0) →
          ell.realValue (ModuleCat.of R (R ⧸ I))*(s:ℝ)^(n+1)*
            ((b 0:ℝ)-A/s*∑ i∈Finset.range (n+2),(b (-(i:ℤ)):ℝ))≤
              ell.realValue (F.homology 0) := by
  obtain ⟨A,hA,hest⟩ := Numerical.uniform_from_sum_estimate n
  refine ⟨A,hA,?_⟩
  intro R _ _ I z hgen ell hds hmu ha hK F b B hb hac
  have hf : ∀ p,Module.Free R (F.X p) := fun p => Module.Free.of_basis (B p)
  have hfin : ∀ p,Module.Finite R (F.X p) := fun p => Module.Finite.of_basis (B p)
  have hz : ∀ j,z j∈I := fun j => hgen ▸ Ideal.subset_span ⟨j,rfl⟩
  have hbf : ∀ p,p < -((n+1:ℕ):ℤ) ∨ 0<p → IsZero (F.X p) := by
    simpa only [Nat.cast_add,Nat.cast_one] using hb
  have hpure := SourceGraded.acyclicity_finite_torsion I z hgen ell F hmu ha hK hf hfin hbf hac
  refine ⟨hpure.1,hpure.2,?_⟩
  intro s hs hd halt
  have hbr := rank_zero_reverse (n+1) b halt
  simp only [Nat.cast_add,Nat.cast_one] at hbr
  have H := hest s hs (fun i => (b (-(i.val:ℤ)):ℝ)) (fun _ => Nat.cast_nonneg _)
    (ell.realValue (ModuleCat.of R (R ⧸ I))) (ell.realValue (F.homology 0))
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have halt' : (∑ i : Fin (n+2),(-1:ℝ)^i.val*(b (-(i.val:ℤ)):ℝ))=0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*(b (-(i:ℤ)):ℝ)) (n+2)]
    exact halt
  have he : (∑ i : Fin (n+2),(b (-(i.val:ℤ)):ℝ))=
      ∑ i∈Finset.range (n+2),(b (-(i:ℤ)):ℝ) :=
    Fin.sum_univ_eq_sum_range (fun i => (b (-(i:ℤ)):ℝ)) (n+2)
  apply (show _ from H halt' ?_) |> fun hh => by simpa only [Fin.val_zero,Nat.cast_zero,neg_zero,he] using hh
  intro hr
  have hr' : RootPositions n s (Numerical.roundedRoot n s) := by
    intro j
    constructor
    · exact_mod_cast (hr j).1
    · exact_mod_cast (hr j).2
  have ht := ReesRoot.sum_estimate I z hz hgen ell hds hmu ha hK F s hd b B hf hfin hb hac hbr
    (Numerical.roundedRoot n s) hr'
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1:ℝ)^i*(b (-(i:ℤ)):ℝ)*Numerical.layer n i s) (n+2)]
  exact ht
end Lech

end

end OAI
