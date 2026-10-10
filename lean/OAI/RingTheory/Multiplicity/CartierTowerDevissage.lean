import Mathlib
import OAI.RingTheory.Multiplicity.BicomplexImageLift
import OAI.RingTheory.Multiplicity.TotalExact

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R]

lemma mono_cokernel_shortExact {C : Type*} [Category C] [Abelian C]
    {K L : C} (f : K ⟶ L) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel f)

lemma total_map_mono {K L : BicomplexTotal.Double (R:=R)} (f : K ⟶ L) [Mono f] :
    Mono (HomologicalComplex₂.total.map f (.up ℤ)) :=
  (BicomplexTotal.total_shortExact _ (mono_cokernel_shortExact f)).mono_f

lemma homology_target_property_of_zero (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [Mono f] (i : ℤ)
    (hzero : homologyMap f i=0) (hquot : P ((cokernel f).homology i)) : P (L.homology i) := by
  have hs := mono_cokernel_shortExact f
  have : Mono (homologyMap (cokernel.π f) i) := (hs.homology_exact₂ i).mono_g hzero
  exact P.prop_of_mono (homologyMap (cokernel.π f) i) hquot

lemma homology_source_property_of_zero (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) [Mono f] (i : ℤ)
    (hzero : homologyMap f i=0) (hquot : P ((cokernel f).homology (i-1))) : P (K.homology i) := by
  have hs := mono_cokernel_shortExact f
  have hij : (ComplexShape.up ℤ).Rel (i-1) i := by simp
  have : Epi (hs.δ (i-1) i hij) := (hs.homology_exact₁ (i-1) i hij).epi_f hzero
  exact P.prop_of_epi (hs.δ (i-1) i hij) hquot

namespace TotalGhost
variable {X : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (f : ∀ n,X (n+1) ⟶ X n)
  (hf : ∀ n,Mono (f n))
include hf in
lemma towerPath_mono (N : ℕ) : Mono (towerPath f N) := by
  induction N with
  | zero => exact inferInstanceAs (Mono (𝟙 _))
  | succ N ih =>
      have := hf N
      have := ih
      exact inferInstanceAs (Mono (f N ≫ towerPath f N))

include hf in
lemma towerPath_cokernel_property (P : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (N : ℕ) (i : ℤ) (hl : ∀ n,n<N → P ((cokernel (f n)).homology i)) :
    P ((cokernel (towerPath f N)).homology i) := by
  induction N with
  | zero =>
      exact P.prop_of_isZero ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).map_isZero
        (isZero_cokernel_of_epi (𝟙 (X 0))))
  | succ N ih =>
      have := towerPath_mono f hf N
      exact cokernel_comp_homology_property P (f N) (towerPath f N) i (hl N (by omega))
        (ih (fun n hn => hl n (by omega)))
end TotalGhost
end Lech

end

end OAI
