import Mathlib
import OAI.RingTheory.Multiplicity.ScalarCartierLift

namespace OAI

noncomputable section
namespace Lech.ComplexLift
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {C : Type*} [Category C] [HasZeroMorphisms C]
  {ι : Type*} {c : ComplexShape ι} {K L M : HomologicalComplex C c}
def factor (f : K ⟶ L) (g : M ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i,M.X i ⟶ K.X i) (hr : ∀ i,r i ≫ f.f i=g.f i) : M ⟶ K where
  f := r
  comm' i j _ := by
    apply (cancel_mono (f.f j)).mp
    rw [Category.assoc,←f.comm i j,←Category.assoc,hr,g.comm,Category.assoc,hr]
lemma factor_comp (f : K ⟶ L) (g : M ⟶ L) [∀ i, Mono (f.f i)]
    (r : ∀ i,M.X i ⟶ K.X i) (hr : ∀ i,r i ≫ f.f i=g.f i) : factor f g r hr ≫ f=g := by
  apply Hom.ext
  funext i
  exact hr i
end Lech.ComplexLift

namespace Lech.TensorIdeal
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {M N T : ModuleCat.{u} R}
  (f : M ⟶ N) (hf : Function.Injective f.hom) (g : T ⟶ N) (hr : g.hom.range≤f.hom.range)
def imageLift : T ⟶ M := ModuleCat.ofHom
  ((LinearEquiv.ofInjective f.hom hf).symm.toLinearMap.comp
    (g.hom.codRestrict f.hom.range (fun x => hr (LinearMap.mem_range_self _ x))))
include hf hr in
lemma imageLift_comp : imageLift f hf g hr ≫ f=g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change f.hom ((LinearEquiv.ofInjective f.hom hf).symm _) = g.hom x
  exact congrArg Subtype.val ((LinearEquiv.ofInjective f.hom hf).apply_symm_apply _)
end Lech.TensorIdeal

namespace Lech.TotalGhost
open CategoryTheory CategoryTheory.Limits HomologicalComplex HomologicalComplex₂
universe u
variable {R : Type u} [CommRing R] {K L M : Bic (R:=R)}
  (f : K ⟶ L) (hf : ∀ p q,Function.Injective ((f.f p).f q).hom) (g : M ⟶ L)
  (hr : ∀ p q,((g.f p).f q).hom.range≤((f.f p).f q).hom.range)
def imageRowLift (p : ℤ) : M.X p ⟶ K.X p := by
  letI : ∀ q, Mono ((f.f p).f q) := fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.factor (f.f p) (g.f p)
    (fun q => TensorIdeal.imageLift ((f.f p).f q) (hf p q) ((g.f p).f q) (hr p q))
    (fun q => TensorIdeal.imageLift_comp ((f.f p).f q) (hf p q) ((g.f p).f q) (hr p q))
include hf hr in
lemma imageRowLift_comp (p : ℤ) : imageRowLift f hf g hr p ≫ f.f p=g.f p := by
  let : ∀ q, Mono ((f.f p).f q) := fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q)
  exact ComplexLift.factor_comp _ _ _ _
def imageLift : M ⟶ K := by
  letI : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.factor f g (imageRowLift f hf g hr) (imageRowLift_comp f hf g hr)
include hf hr in
lemma imageLift_comp : imageLift f hf g hr ≫ f=g := by
  let : ∀ p, Mono (f.f p) := fun p =>
    mono_of_mono_f _ (fun q => (ModuleCat.mono_iff_injective _).mpr (hf p q))
  exact ComplexLift.factor_comp _ _ _ _
include hf hr in
lemma homology_zero_of_range (i : ℤ) (hf0 : homologyMap (total.map f (.up ℤ)) i=0) :
    homologyMap (total.map g (.up ℤ)) i=0 := by
  rw [←imageLift_comp f hf g hr,total.map_comp,homologyMap_comp,hf0,comp_zero]

variable (I : Ideal R) {X : ℕ → Bic (R:=R)} (step : ∀ n,X (n+1) ⟶ X n)
lemma towerPath_injective (hstep : ∀ n p q,Function.Injective (((step n).f p).f q).hom)
    (N : ℕ) (p q : ℤ) : Function.Injective (((towerPath step N).f p).f q).hom := by
  induction N with
  | zero => exact Function.injective_id
  | succ N ih => exact ih.comp (hstep N p q)

lemma towerPath_range (a : ℕ)
    (hstep : ∀ n p q,(((step n).f p).f q).hom.range=I^a • (⊤ : Submodule R (((X n).X p).X q)))
    (N : ℕ) (p q : ℤ) :
    (((towerPath step N).f p).f q).hom.range=I^(a*N) • (⊤ : Submodule R (((X 0).X p).X q)) := by
  induction N with
  | zero => simp [towerPath,LinearMap.range_id]
  | succ N ih =>
      change ((((towerPath step N).f p).f q).hom.comp (((step N).f p).f q).hom).range=_
      rw [LinearMap.range_comp,hstep,Submodule.map_smul'',Submodule.map_top,ih,←Submodule.mul_smul,←pow_add]
      congr 2
      ring
end Lech.TotalGhost

end

end OAI
