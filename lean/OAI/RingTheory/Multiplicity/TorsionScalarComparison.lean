import Mathlib
import OAI.RingTheory.Multiplicity.LechHomologyProp
import OAI.RingTheory.Multiplicity.TorsionThickening

namespace OAI

noncomputable section
namespace Lech.SourceGraded
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] [Nontrivial R] (I : Ideal R) {h : ℕ}
  (z : Fin h → R) (hz : Ideal.span (Set.range z)=I)
  (ell : TorsionLength I) (F : CochainComplex (ModuleCat.{u} R) ℤ)
theorem cech_homology_value_torsion
    (hds : ell.DirectSumZero)
    (hh : 0<h) (hmu : ell.value (ModuleCat.of R (R ⧸ I))≠⊤)
    (ha : ∀ a : ℕ, 0<a → ell.value (ModuleCat.of R
      (R ⧸ Ideal.span (Set.range (fun j => z j^a))))=a^h • ell.value (ModuleCat.of R (R ⧸ I)))
    (hK : ∀ a : ℕ, 1≤a → ∀ i : ℤ, i<0 →
      ell.value ((Koszul.unit (List.ofFn (fun j => z j^a))).homology i)=0)
    (hf : ∀ j, Module.Free R (F.X j)) (hfin : ∀ j, Module.Finite R (F.X j))
    (n : ℤ) (d : ℕ) (hb : ∀ j, j<n ∨ n+d≤j → IsZero (F.X j))
    (hacyc : ∀ j, ((baseChangeFunctor R (Localization.Away (z j))).mapHomologicalComplex _ |>.obj F).Acyclic)
    (i : ℤ) :
    ell.value (F.homology i)=ell.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive I z (coordinate_mem I z hz) 0)).homology (i+1)) := by
  classical
  subst I
  let : ∀ j, Module.Free R (F.X j) := hf
  let : ∀ j, Module.Finite R (F.X j) := hfin
  have hp : ∀ j, Module.Projective R (F.X j) := fun j => by have := hf j; infer_instance
  have hbound : ∀ j, j<n ∨ n+d-1<j → IsZero (F.X j) := by
    intro j hj
    apply hb
    omega
  obtain ⟨m,hm⟩ := uniform_nullhomotopy_of_projective_acyclic_away z F n (n+d-1) hp hfin hbound hacyc
  let t := m+1
  have ht : 1≤t := by dsimp [t]; omega
  have H : ∀ j, Homotopy (z j^t • 𝟙 F) 0 := fun j =>
    Koszul.scalarPowerHomotopy F (z j) m t (by dsimp [t]; omega) (hm j).some
  let ℓ := ell
  let P := ℓ.zeroClass
  have hfg : (Ideal.span (Set.range z)).FG := ⟨Finset.univ.image z,by simp⟩
  have hrad (a : ℕ) : Ideal.span (Set.range z) ≤
      (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical := by
    rw [entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨a,Ideal.subset_span ⟨j,rfl⟩⟩
  have hTF : powerTorsion (Ideal.span (Set.range z)) (F.homology i) := by
    apply powerTorsion_of_le_radical hfg (hrad t)
    refine ⟨1,?_⟩
    rw [pow_one,entryIdeal_ofFn]
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Koszul.scalar_annihilates_homology F (z j^t) (H j) i
  have hKos : ∀ a : ℕ, 1≤a → ∀ k : ℤ, k<0 → P ((Koszul.unit (List.ofFn fun j => z j^a)).homology k) := by
    intro a ha k hk
    exact ⟨powerTorsion_of_le_radical hfg (hrad a)
      (Koszul.tensor_homology_torsion _ _ k),hK a ha k hk⟩
  obtain ⟨M₀,hM₀⟩ := ordinaryPower_stableImage_isoMod P F n d hb h z t ht H hKos
  obtain ⟨MD,hMD⟩ := exists_uniform_geometric_stableImage (Ideal.span (Set.range z)) z rfl F
    n (n+d-1) hp hfin hbound hacyc
  let M := max M₀ MD
  obtain ⟨N₀,hMN₀,hN₀⟩ := hM₀ M (le_max_left _ _)
  let N := max N₀ (M+MD)
  have hNN : N₀≤N := le_max_left _ _
  have hMN : M≤N := hMN₀.trans hNN
  have hgap : MD≤N-M := by have := le_max_right N₀ (M+MD); dsimp [N]; omega
  let f := homologyMap ((complexQuotientMap (show Ideal.span (Set.range z)^N ≤ Ideal.span (Set.range z)^M from Ideal.pow_le_pow_right hMN) (.up ℤ)).app F) i
  let g := homologyMap ((TensorTotal.Right.functor F).map
    (thickeningCechTransition (Ideal.span (Set.range z)) z rfl hMN)) (i+1)
  let s : Arrow.mk f ⟶ Arrow.mk g := Arrow.homMk
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F N i)
    (thickeningComparison (Ideal.span (Set.range z)) z rfl F M i)
    (thickeningComparison_transition (Ideal.span (Set.range z)) z rfl F hMN i).symm
  have hs₁ : P.isoModSerre s.left :=
    thickeningComparison_isoModSerre_torsion (Ideal.span (Set.range z)) z rfl ell hds hh hmu ha F hf hfin n d hb N i
  have hs₂ : P.isoModSerre s.right :=
    thickeningComparison_isoModSerre_torsion (Ideal.span (Set.range z)) z rfl ell hds hh hmu ha F hf hfin n d hb M i
  have hTQ (c : ℕ) : powerTorsion (Ideal.span (Set.range z))
      (((complexQuotient (Ideal.span (Set.range z)^c) (.up ℤ)).obj F).homology i) := by
    refine ⟨c,?_⟩
    intro r hr
    exact Koszul.scalar_annihilates_homology _ r
      (Homotopy.ofEq (complexQuotient_annihilated _ r hr F)) i
  have hTG : powerTorsion (Ideal.span (Set.range z)) (Arrow.mk g).right := by
    apply (powerTorsion (Ideal.span (Set.range z))).prop_X₂_of_exact
      ((ShortComplex.mk _ _ (cokernel.condition s.right)).exact_of_g_is_cokernel
        (cokernelIsCokernel s.right)) (hTQ M) hs₂.2.1
  have hTFimage := powerTorsion_mono (Ideal.span (Set.range z)) (Limits.image.ι f) (hTQ M)
  have hTGimage := powerTorsion_mono (Ideal.span (Set.range z)) (Limits.image.ι g) hTG
  have hab : ℓ.value (F.homology i)=ℓ.value (Limits.image f) :=
    ℓ.eq_of_isoModSerre _ hTF hTFimage (hN₀ N hNN i)
  have hbc : ℓ.value (Limits.image f)=ℓ.value (Limits.image g) :=
    ℓ.image_value_eq s hs₁ hs₂ (hTQ M) hTG
  have hg := hMD M N hMN (le_max_right _ _) hgap (i+1)
  have hdc : ℓ.value (((TensorTotal.Right.functor F).obj
      (FilteredCech.positive (Ideal.span (Set.range z)) z (coordinate_mem _ z rfl) 0)).homology (i+1))=
      ℓ.value (Limits.image g) :=
    ℓ.eq_of_iso (asIso (homologyMap (geometricStructureMap (Ideal.span (Set.range z)) z rfl F N) (i+1) ≫
      factorThruImage g))
      (FilteredCech.positive_homology_powerTorsion (Ideal.span (Set.range z)) z
        (coordinate_mem _ z rfl) F n (n+d-1) hp hfin hbound hacyc 0 (i+1)) hTGimage
  exact hab.trans (hbc.trans hdc.symm)
end Lech.SourceGraded

end

end OAI
