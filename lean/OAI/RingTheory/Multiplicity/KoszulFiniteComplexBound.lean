import Mathlib
import OAI.RingTheory.Multiplicity.AdditiveLength

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R] [Nontrivial R]

lemma length_quotient_tensor_le_sum (I : Ideal R) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hfree : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j)) :
    Module.length R ((tensor zs ((complexQuotient I (.up ℤ)).obj F)).homology i) ≤
      ∑ k∈Finset.range N, Module.finrank R (F.X (m+k)) • Module.length R
        ((tensor zs ((complexQuotient I (.up ℤ)).obj
          ((single (ModuleCat R) (.up ℤ) (m+k)).obj (ModuleCat.of R R)))).homology i) := by
  let T : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _ := complexQuotient I (.up ℤ) ⋙ tensorFunctor zs
  have hT (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
      (σ : ∀ j,(S.map (eval _ (.up ℤ) j)).Splitting) (i : ℤ) :
      ((S.map T).map (eval _ (.up ℤ) i)).Splitting :=
    tensorSplitting zs (S.map (complexQuotient I (.up ℤ)))
      (fun j => (σ j).map (moduleQuotient I)) i
  have hl := FiniteComplex.homology_length_le_sum T hT m N F i hb
  refine hl.trans_eq ?_
  apply Finset.sum_congr rfl
  intro k hk
  have := hfree (m+k)
  have := hfin (m+k)
  exact additive_length_finite_free
    (single (ModuleCat R) (.up ℤ) (m+k) ⋙ T ⋙ homologyFunctor _ (.up ℤ) i) (F.X (m+k))

 

theorem length_quotient_le_koszul_powers (I : Ideal R) (zs : List R) (q : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) (N : ℕ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m+N ≤ j → IsZero (F.X j))
    (hfree : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (H : ∀ r∈zs, Homotopy
      (r^q • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0) :
    Module.length R (((complexQuotient I (.up ℤ)).obj F).homology i) ≤
      (q^zs.length) • ∑ k∈Finset.range N,
        Module.finrank R (F.X (m+k)) • Module.length R
          ((tensor zs ((complexQuotient I (.up ℤ)).obj
            ((single (ModuleCat R) (.up ℤ) (m+k)).obj (ModuleCat.of R R)))).homology i) := by
  let G := (complexQuotient I (.up ℤ)).obj F
  have H' (r : R) (hr : r∈zs.map (fun x => x^q)) : Homotopy (r • 𝟙 G) 0 := by
    apply Classical.choice
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hr
    exact ⟨H x hx⟩
  exact (Module.length_le_of_injective (homologyMap (inclusion G _) i).hom
    (inclusion_homology_injective G _ H' i)).trans
      ((length_tensor_powers_le zs q G i).trans
        (nsmul_le_nsmul_right (length_quotient_tensor_le_sum I zs F m N i hb hfree hfin) _))
end Lech.Koszul

end

end OAI
