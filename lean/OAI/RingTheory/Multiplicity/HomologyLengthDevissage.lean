import Mathlib
import OAI.RingTheory.Multiplicity.KoszulPowerGrowth

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Lech.FiniteComplex
universe u
variable {R : Type u} [CommRing R]

lemma homology_length_iso (F G : CochainComplex (ModuleCat.{u} R) ℤ)
    (e : F ≅ G) (i : ℤ) : Module.length R (F.homology i) = Module.length R (G.homology i) :=
  ((homologyFunctor _ _ i).mapIso e).toLinearEquiv.length_eq

 

theorem homology_length_le_sum
    (T : CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ)
    [T.Additive]
    (hT : ∀ (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)),
      (∀ j, (S.map (eval (ModuleCat R) (.up ℤ) j)).Splitting) →
      ∀ j, ((S.map T).map (eval (ModuleCat R) (.up ℤ) j)).Splitting)
    (m : ℤ) (N : ℕ) (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hb : ∀ j, j < m ∨ m + N ≤ j → IsZero (F.X j)) :
    Module.length R ((T.obj F).homology i) ≤
      ∑ k∈Finset.range N, Module.length R
        ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (F.X (m+k)))).homology i) := by
  induction N generalizing F with
  | zero =>
    have hz := (homologyFunctor (ModuleCat R) (.up ℤ) i).map_isZero
      (T.map_isZero (isZero_of_X F (fun j => hb j (by omega))))
    have : Subsingleton ((T.obj F).homology i) := ModuleCat.isZero_iff_subsingleton.mp hz
    simp only [Finset.range_zero,Finset.sum_empty,le_zero_iff,Module.length_eq_zero]
  | succ N ih =>
    let n : ℤ := m+N
    have hn : ∀ j, n < j → IsZero (F.X j) := fun j hj => hb j (by
      right
      dsimp [n] at hj
      omega)
    let D := dropTop F n hn
    have hbD : ∀ j, j < m ∨ m + N ≤ j → IsZero (D.X j) := by
      intro j hj
      by_cases hjn : j=n
      · subst j
        exact dropTop_X_top F n hn
      · exact (hb j (by dsimp [n] at hjn; omega)).of_iso
          (dropTopXIso F n hn j hjn).symm
    have hD := ih D hbD
    have he (k : ℕ) (hk : k∈Finset.range N) :
        Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (D.X (m+k)))).homology i) =
        Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) (m+k)).obj (F.X (m+k)))).homology i) :=
      (homology_length_iso _ _
        (T.mapIso ((single (ModuleCat R) (.up ℤ) (m+k)).mapIso
          (dropTopXIso F n hn (m+k) (by dsimp [n]; simp only [Finset.mem_range] at hk; omega)))) i).symm
    have hs : ((topShortComplex F n hn).map T).ShortExact :=
      shortExact_of_degreewise_shortExact _ (fun j =>
        (hT _ (topSplitting F n hn) j).shortExact)
    have hl := Koszul.length_le_sum_of_exact _ (hs.homology_exact₂ i)
    change Module.length R ((T.obj F).homology i) ≤
      Module.length R ((T.obj ((single (ModuleCat R) (.up ℤ) n).obj (F.X n))).homology i)+
      Module.length R ((T.obj D).homology i) at hl
    rw [Finset.sum_congr rfl he] at hD
    simpa only [Finset.sum_range_succ,add_comm,n] using
      hl.trans (add_le_add le_rfl hD)
end Lech.FiniteComplex

end

end OAI
