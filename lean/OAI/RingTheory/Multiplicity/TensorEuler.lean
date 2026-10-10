import Mathlib
import OAI.RingTheory.Multiplicity.ComplexTensorComparison
import OAI.RingTheory.Multiplicity.PrimeFiltrationSupport

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma ordinaryLength_real [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{u} R) :
    (ordinaryLength (⊥:Ideal R)).realValue M=((Module.length R M).toNat:ℝ) := by
  change (Module.length R M).toENNReal.toReal=_
  rcases eq_or_ne (Module.length R M) ⊤ with h|h
  · simp [h]
  · obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp h
    rw [← hn]
    simp

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma ordinaryLength_finite [IsNoetherianRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    (ordinaryLength (⊥:Ideal R)).finiteClass M := by
  refine ⟨⟨1,by simp⟩,?_⟩
  change (Module.length R M).toENNReal ≠ ⊤
  simpa using Module.length_ne_top_iff.mpr hM

lemma shortEuler_additive
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (h₁ : ∀ i,IsFiniteLength R (S.X₁.homology i))
    (h₂ : ∀ i,IsFiniteLength R (S.X₂.homology i))
    (h₃ : ∀ i,IsFiniteLength R (S.X₃.homology i))
    (hl : IsZero (S.X₃.homology (-(dimension R:ℤ)-1)))
    (hr : IsZero (S.X₁.homology 1)) :
    shortEuler R S.X₂=shortEuler R S.X₁+shortEuler R S.X₃ := by
  let ell := ordinaryLength (⊥:Ideal R)
  let a (i : ℕ) := ell.realValue (image (hS.δ (-(i:ℤ)) (-(i:ℤ)+1) rfl))
  have hi (i : ℕ) :
      ell.realValue (S.X₁.homology (-(i:ℤ)))-ell.realValue (S.X₂.homology (-(i:ℤ)))+
        ell.realValue (S.X₃.homology (-(i:ℤ)))=a i+a (i+1) := by
    rw [homology_length_defect ell S hS (-(i:ℤ))
      (ordinaryLength_finite _ (h₁ _)) (ordinaryLength_finite _ (h₂ _))
      (ordinaryLength_finite _ (h₃ _))]
    change _+a i=_
    rw [add_comm (a i)]
    congr 1
    have hδ (j j' k k' : ℤ) (hjk : j+1=k) (hjk' : j'+1=k')
        (hj : j=j') (hk : k=k') :
        ell.realValue (image (hS.δ j k hjk))=ell.realValue (image (hS.δ j' k' hjk')) := by
      subst j';subst k';rfl
    exact hδ _ _ _ _ _ _ (by push_cast;omega) (by push_cast;omega)
  have ha₀ : a 0=0 := by
    apply ell.realValue_zero
    apply IsZero.of_mono (image.ι (hS.δ 0 1 rfl))
    exact hr
  have ha₁ : a (dimension R+1)=0 := by
    apply ell.realValue_zero
    apply IsZero.of_epi (factorThruImage (hS.δ (-((dimension R+1:ℕ):ℤ))
      (-((dimension R+1:ℕ):ℤ)+1) rfl))
    convert hl using 1
    congr 1
    push_cast
    omega
  have he : shortEuler R S.X₁-shortEuler R S.X₂+shortEuler R S.X₃=0 := by
    calc
      _=∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
          (ell.realValue (S.X₁.homology (-(i:ℤ)))-ell.realValue (S.X₂.homology (-(i:ℤ)))+
            ell.realValue (S.X₃.homology (-(i:ℤ)))) := by
        simp only [ell,ordinaryLength_real,shortEuler,mul_add,mul_sub,
          Finset.sum_add_distrib,Finset.sum_sub_distrib]
      _=a 0+(-1:ℝ)^dimension R*a (dimension R+1) := by
        simp_rw [hi]
        exact alternating_sum_pairs a (dimension R)
      _=0 := by rw [ha₀,ha₁,mul_zero,add_zero]
  linarith

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma tensorModule_shortExact [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hflat : ∀ i,Module.Flat R (F.X i))
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) :
    (S.map (tensorModuleFunctor F)).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro i
  let := hflat i
  let := hS.mono_f
  let := hS.epi_g
  exact hS.map (tensorLeft (F.X i))

lemma tensorModule_homology_finite (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℤ) :
    IsFiniteLength R (((tensorModuleFunctor F).obj M).homology i) := by
  let G := (tensorModuleFunctor F).obj M
  have : Module.Finite R (G.X i) := by
    have := hF.term_finite i
    change Module.Finite R ((F.X i) ⊗[R] M)
    infer_instance
  have := finite_cochain_homology G i
  apply finiteLength_of_maximal_le_radical_annihilator
  intro x hx
  obtain ⟨a,ha⟩ := shortComplex_nullScalar_radical F hF hx
  refine ⟨a,?_⟩
  apply Koszul.scalar_annihilates_homology G (x^a) _ i
  have H := (((curriedTensor (ModuleCat.{u} R)).flip.obj M).mapHomotopy ha.some)
  have he : (TensorTotal.termTensor M).map (x^a • 𝟙 F)=x^a • 𝟙 G := by
    ext j : 1
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext y z
    rfl
  rw [he, CategoryTheory.Functor.map_zero] at H
  exact H

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma tensorModule_homology_bounded [IsNoetherianRing R] [IsLocalRing R]
    (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (hF : IsFiniteHomologyComplex R F) (M : ModuleCat.{u} R) (i : ℤ)
    (hi : i < -(dimension R:ℤ) ∨ 0 < i) :
    IsZero (((tensorModuleFunctor F).obj M).homology i) :=
  (ExactAt.of_isZero (((curriedTensor (ModuleCat.{u} R)).flip.obj M).map_isZero
    (hF.bounded i hi))).isZero_homology

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma shortEuler_eq_of_iso [IsNoetherianRing R] [IsLocalRing R]
    {F G : CochainComplex (ModuleCat.{u} R) ℤ} (e : F ≅ G) :
    shortEuler R F=shortEuler R G := by
  unfold shortEuler
  apply Finset.sum_congr rfl
  intro i hi
  rw [(homologyMapIso e (-(i:ℤ))).toLinearEquiv.length_eq]

lemma tensorEuler_equiv (F : CochainComplex (ModuleCat.{u} R) ℤ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R M))=
      shortEuler R ((tensorModuleFunctor F).obj (ModuleCat.of R N)) :=
  shortEuler_eq_of_iso ((tensorModuleFunctor F).mapIso e.toModuleIso)

end Lech

end

end OAI
