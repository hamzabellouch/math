import Mathlib

namespace OAI

noncomputable section
namespace Lech.IdealFiltered
open CategoryTheory CategoryTheory.Limits HomologicalComplex MonoidalCategory
open scoped TensorProduct
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

section Linear
variable {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N) (s : ℕ) (hf : f.range ≤ I^s • (⊤ : Submodule R N))

include hf in
lemma map_power_le (a : ℕ) :
    (I^a • (⊤ : Submodule R M)).map f ≤ I^(a+s) • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'',Submodule.map_top,pow_add,Submodule.mul_smul]
  exact Submodule.smul_mono le_rfl hf

variable (Q : Type u) [AddCommGroup Q] [Module R Q]
include hf in
lemma tensor_range_le :
    (f.rTensor Q).range ≤ I^s • (⊤ : Submodule R (N ⊗[R] Q)) := by
  rintro _ ⟨x,rfl⟩
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
      change f x ⊗ₜ[R] y ∈ _
      have hx := hf (LinearMap.mem_range_self f x)
      refine Submodule.smul_induction_on hx (fun a ha b hb => ?_) (fun x y hx hy => ?_)
      · rw [←TensorProduct.smul_tmul']
        exact Submodule.smul_mem_smul ha Submodule.mem_top
      · rw [TensorProduct.add_tmul]
        exact Submodule.add_mem _ hx hy
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
end Linear

 

def subcomplex {ι : Type*} {c : ComplexShape ι} (K : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom) :
    HomologicalComplex (ModuleCat.{u} R) c where
  X p := ModuleCat.of R (P p)
  d p q := ModuleCat.ofHom (((K.d p q).hom.comp (P p).subtype).codRestrict (P q)
    (fun x => hP p q x.property))
  shape p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (K.d p q).hom x.val=0
    rw [K.shape p q hpq]
    rfl
  d_comp_d' p q r _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (K.d q r).hom ((K.d p q).hom x.val)=0
    exact congrArg (fun f : K.X p ⟶ K.X r => f.hom x.val) (K.d_comp_d p q r)

 
def subcomplexMap {ι : Type*} {c : ComplexShape ι}
    (K L : HomologicalComplex (ModuleCat.{u} R) c)
    (P : ∀ p, Submodule R (K.X p)) (T : ∀ p, Submodule R (L.X p))
    (hP : ∀ p q, P p ≤ (P q).comap (K.d p q).hom)
    (hT : ∀ p q, T p ≤ (T q).comap (L.d p q).hom)
    (f : K ⟶ L) (hf : ∀ p, P p ≤ (T p).comap (f.f p).hom) :
    subcomplex K P hP ⟶ subcomplex L T hT where
  f p := ModuleCat.ofHom (((f.f p).hom.comp (P p).subtype).codRestrict (T p)
    (fun x => hf p x.property))
  comm' p q _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun g : K.X p ⟶ L.X q => g.hom x.val) (f.comm p q)

 

def order (h s : ℕ) (p : ℤ) : ℕ := (p+(h:ℤ)).toNat*s

lemma order_step (h s : ℕ) (p : ℤ) : order h s (p+1) ≤ order h s p+s := by
  have hh : (p+1+(h:ℤ)).toNat ≤ (p+(h:ℤ)).toNat+1 := by omega
  exact (Nat.mul_le_mul_right s hh).trans_eq (by rw [Nat.add_mul,one_mul]; rfl)

lemma order_source (h s : ℕ) (i : ℕ) (hi : i ≤ h) : order h s (-(i:ℤ))=(h-i)*s := by
  unfold order
  congr 1
  omega

variable (F : CochainComplex (ModuleCat.{u} R) ℤ) (h s : ℕ)
  (hd : ∀ p : ℤ, (F.d p (p+1)).hom.range ≤ I^s • (⊤ : Submodule R (F.X (p+1))))
  (Q : ModuleCat.{u} R)

abbrev tensorComplex : CochainComplex (ModuleCat.{u} R) ℤ :=
  (((curriedTensor (ModuleCat.{u} R)).flip.obj Q).mapHomologicalComplex (.up ℤ)).obj F

def term (p : ℤ) : Submodule R ((tensorComplex F Q).X p) :=
  I^(order h s p) • ⊤

include hd in
lemma term_d (p q : ℤ) :
    term I F h s Q p ≤ (term I F h s Q q).comap ((tensorComplex F Q).d p q).hom := by
  by_cases hpq : q=p+1
  · subst q
    rw [←Submodule.map_le_iff_le_comap]
    have hr := tensor_range_le I (F.d p (p+1)).hom s (hd p) Q
    have hh := map_power_le I ((F.d p (p+1)).hom.rTensor Q) s hr (order h s p)
    exact hh.trans (Submodule.smul_mono_left (Ideal.pow_le_pow_right (order_step h s p)))
  · have he : ¬(ComplexShape.up ℤ).Rel p q := by simpa only [ComplexShape.up_Rel,eq_comm] using hpq
    rw [(tensorComplex F Q).shape p q he]
    intro x hx
    exact (term I F h s Q q).zero_mem

 

def complex : CochainComplex (ModuleCat.{u} R) ℤ :=
  subcomplex (tensorComplex F Q) (term I F h s Q) (term_d I F h s hd Q)

 

def ambientInclusion : complex I F h s hd Q ⟶ tensorComplex F Q where
  f p := ModuleCat.ofHom (term I F h s Q p).subtype
  comm' _ _ _ := rfl

instance ambientInclusion_mono (p : ℤ) : Mono ((ambientInclusion I F h s hd Q).f p) :=
  (ModuleCat.mono_iff_injective _).mpr (term I F h s Q p).injective_subtype

 
def tensorMap {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') : tensorComplex F Q ⟶ tensorComplex F Q' :=
  ((curriedTensor (ModuleCat.{u} R)).flip.map f).mapHomologicalComplex (.up ℤ) |>.app F

 

def map {Q Q' : ModuleCat.{u} R} (f : Q ⟶ Q') :
    complex I F h s hd Q ⟶ complex I F h s hd Q' :=
  subcomplexMap (tensorComplex F Q) (tensorComplex F Q')
    (term I F h s Q) (term I F h s Q')
    (term_d I F h s hd Q) (term_d I F h s hd Q') (tensorMap F f)
    (fun p => Submodule.smul_top_le_comap_smul_top (I^(order h s p)) ((tensorMap F f).f p).hom)

lemma map_id (Q : ModuleCat.{u} R) : map I F h s hd (𝟙 Q) = 𝟙 (complex I F h s hd Q) := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (F.X p ◁ 𝟙 Q).hom x.val=x.val
  rw [whiskerLeft_id]
  rfl

lemma map_comp {Q Q' Q'' : ModuleCat.{u} R} (f : Q ⟶ Q') (g : Q' ⟶ Q'') :
    map I F h s hd (f ≫ g) = map I F h s hd f ≫ map I F h s hd g := by
  apply Hom.ext
  funext p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (F.X p ◁ (f ≫ g)).hom x.val=(F.X p ◁ g).hom ((F.X p ◁ f).hom x.val)
  rw [whiskerLeft_comp]
  rfl

 
def functor : ModuleCat.{u} R ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj := complex I F h s hd
  map := map I F h s hd
  map_id := map_id I F h s hd
  map_comp := map_comp I F h s hd

 
instance functor_additive : (functor I F h s hd).Additive where
  map_add := by
    intro Q Q' f g
    apply Hom.ext
    funext p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (F.X p ◁ (f+g)).hom x.val = (F.X p ◁ f).hom x.val+(F.X p ◁ g).hom x.val
    rw [show F.X p ◁ (f+g) = F.X p ◁ f + F.X p ◁ g from
      ((curriedTensor (ModuleCat.{u} R)).obj (F.X p)).map_add]
    rfl

end Lech.IdealFiltered

end

end OAI
