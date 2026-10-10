import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Support Transport. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def SupportLE {G X Y : Type*} [Group G]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) : Prop :=
  ∀ x : X, x ≠ 0 → ∃ f : Representation.IntertwiningMap ρ σ, f x ≠ 0

namespace SupportLE
variable {G H X Y Z : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}

lemma refl (ρ : Representation ℂ G X) : SupportLE ρ ρ := by
  intro x hx
  exact ⟨Representation.IntertwiningMap.id ρ, hx⟩

lemma trans (h₁ : SupportLE ρ σ) (h₂ : SupportLE σ τ) : SupportLE ρ τ := by
  intro x hx
  obtain ⟨f,hf⟩ := h₁ x hx
  obtain ⟨g,hg⟩ := h₂ (f x) hf
  exact ⟨g.comp f,hg⟩

lemma of_injective (f : Representation.IntertwiningMap ρ σ) (hf : Function.Injective f) :
    SupportLE ρ σ := by
  intro x hx
  exact ⟨f,fun he => hx (hf (he.trans (map_zero f).symm))⟩

lemma detects_map {W : Type*} [AddCommMonoid W] [Module ℂ W]
    {υ : Representation ℂ G W} (h : SupportLE ρ σ)
    (f : Representation.IntertwiningMap υ ρ) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap υ σ, g ≠ 0 := by
  have hn : ∃ x, f x ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hf (Representation.IntertwiningMap.ext (LinearMap.ext hh))
  obtain ⟨x,hx⟩ := hn
  obtain ⟨g,hg⟩ := h (f x) hx
  exact ⟨g.comp f,fun hz => hg (congrArg (fun F : Representation.IntertwiningMap υ σ => F x) hz)⟩

lemma restrict (h : SupportLE ρ σ) (φ : H →* G) : SupportLE (ρ.comp φ) (σ.comp φ) := by
  intro x hx
  obtain ⟨f,hf⟩ := h x hx
  exact ⟨⟨f.toLinearMap,fun g => f.isIntertwining' (φ g)⟩,hf⟩

lemma coind (φ : G →* H) (h : SupportLE ρ σ) :
    SupportLE (Representation.coind φ ρ) (Representation.coind φ σ) := by
  intro x hx
  have hn : ∃ g, x.val g ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hx (Subtype.ext (funext hh))
  obtain ⟨g,hg⟩ := hn
  obtain ⟨f,hf⟩ := h (x.val g) hg
  refine ⟨Representation.coindMap φ f,?_⟩
  intro hz
  exact hf (congrArg (fun y : Representation.coindV φ σ => y.val g) hz)

end SupportLE

def outer {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ H Y) :
    Representation ℂ (G × H) (X ⊗[ℂ] Y) where
  toFun g := TensorProduct.map (ρ g.1) (σ g.2)
  map_one' := by ext x y; simp
  map_mul' g h := by ext x y; simp

def outerMap {G H X Y U V : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    {τ : Representation ℂ G U} {υ : Representation ℂ H V}
    (f : Representation.IntertwiningMap ρ τ) (g : Representation.IntertwiningMap σ υ) :
    Representation.IntertwiningMap (outer ρ σ) (outer τ υ) where
  toLinearMap := TensorProduct.map f.toLinearMap g.toLinearMap
  isIntertwining' h := by
    ext x y
    change f (ρ h.1 x) ⊗ₜ[ℂ] g (σ h.2 y) = τ h.1 (f x) ⊗ₜ[ℂ] υ h.2 (g y)
    rw [f.isIntertwining,g.isIntertwining]

def rightSlice {X Y : Type*} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y] (l : Module.Dual ℂ Y) : X ⊗[ℂ] Y →ₗ[ℂ] X :=
  (TensorProduct.rid ℂ X).toLinearMap.comp (TensorProduct.map LinearMap.id l)

@[simp] lemma rightSlice_tmul {X Y : Type*} [AddCommMonoid X] [Module ℂ X]
    [AddCommMonoid Y] [Module ℂ Y] (l : Module.Dual ℂ Y) (x : X) (y : Y) :
    rightSlice l (x ⊗ₜ[ℂ] y) = l y • x := rfl

lemma rightSlice_map {X Y U V : Type*}
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    [AddCommMonoid U] [Module ℂ U] [AddCommMonoid V] [Module ℂ V]
    (f : X →ₗ[ℂ] U) (g : Y →ₗ[ℂ] V) (l : Module.Dual ℂ V)
    (z : X ⊗[ℂ] Y) :
    rightSlice l (TensorProduct.map f g z) = f (rightSlice (l.comp g) z) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y => simp

lemma exists_rightSlice {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]
    (z : X ⊗[ℂ] Y) (hz : z ≠ 0) :
    ∃ l : Module.Dual ℂ Y, rightSlice l z ≠ 0 := by
  let E := (TensorProduct.comm ℂ X Y).trans
    ((TensorProduct.congr (Module.evalEquiv ℂ Y) (LinearEquiv.refl ℂ X)).trans
      (dualTensorHomEquiv ℂ (Module.Dual ℂ Y) X))
  have he (z : X ⊗[ℂ] Y) (l : Module.Dual ℂ Y) : E z l = rightSlice l z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add,LinearMap.add_apply,hx,hy]
    | tmul x y => rfl
  by_contra hh
  push Not at hh
  have hez : E z = 0 := LinearMap.ext (fun l => (he z l).trans (hh l))
  exact hz (E.injective (hez.trans (map_zero E).symm))

theorem SupportLE.outer {G H X Y U V : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ Y] [FiniteDimensional ℂ U]
    {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    {τ : Representation ℂ G U} {υ : Representation ℂ H V}
    (h₁ : SupportLE ρ τ) (h₂ : SupportLE σ υ) :
    SupportLE (outer ρ σ) (outer τ υ) := by
  intro z hz
  obtain ⟨l,hl⟩ := exists_rightSlice z hz
  obtain ⟨f,hf⟩ := h₁ (rightSlice l z) hl
  let w := TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) z
  have hw : w ≠ 0 := by
    intro hh
    have he := rightSlice_map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) l z
    rw [show TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y) z = w from rfl,
      hh,map_zero] at he
    exact hf he.symm
  obtain ⟨k,hk⟩ := exists_rightSlice ((TensorProduct.comm ℂ U Y) w)
    (fun he => hw ((TensorProduct.comm ℂ U Y).injective (he.trans (map_zero _).symm)))
  obtain ⟨g,hg⟩ := h₂ (rightSlice k ((TensorProduct.comm ℂ U Y) w)) hk
  refine ⟨outerMap f g,?_⟩
  intro hh
  have he : rightSlice k ((TensorProduct.comm ℂ U V) (outerMap f g z)) =
      g (rightSlice k ((TensorProduct.comm ℂ U Y) w)) := by
    have ht : (rightSlice k).comp ((TensorProduct.comm ℂ U V).toLinearMap.comp
        (outerMap f g).toLinearMap) = g.toLinearMap.comp ((rightSlice k).comp
          ((TensorProduct.comm ℂ U Y).toLinearMap.comp
            (TensorProduct.map f.toLinearMap (LinearMap.id : Y →ₗ[ℂ] Y)))) := by
      ext x y
      change k (f x) • g y = g (k (f x) • y)
      rw [map_smul]
    exact LinearMap.congr_fun ht z
  rw [hh,map_zero,map_zero] at he
  exact hg he.symm

end Saxl

namespace Saxl

def coindLift {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) :
    Representation.IntertwiningMap ρ (Representation.coind φ σ) where
  toLinearMap := {
    toFun x := ⟨fun g => f (ρ g x), fun h g => by
      change f (ρ (φ h*g) x) = σ h (f (ρ g x))
      rw [map_mul,Module.End.mul_apply]
      exact LinearMap.congr_fun (f.isIntertwining' h) (ρ g x)⟩
    map_add' x y := by ext g; simp
    map_smul' a x := by ext g; simp }
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    funext h
    change f (ρ h (ρ g x)) = f (ρ (h*g) x)
    rw [map_mul,Module.End.mul_apply]

def coindEval {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) :
    Representation.IntertwiningMap (ρ.comp φ) σ where
  toLinearMap := {
    toFun x := (f x).val 1
    map_add' x y := by simp
    map_smul' a x := by simp }
  isIntertwining' h := by
    apply LinearMap.ext
    intro x
    change (f (ρ (φ h) x)).val 1 = σ h ((f x).val 1)
    rw [f.isIntertwining]
    change (f x).val (1*φ h) = σ h ((f x).val 1)
    simpa only [one_mul,mul_one] using (f x).property h 1

@[simp] lemma coindEval_lift {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) :
    coindEval φ (coindLift φ f) = f := by
  ext x
  change f (ρ 1 x) = f x
  rw [map_one]
  rfl

@[simp] lemma coindLift_eval {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) :
    coindLift φ (coindEval φ f) = f := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext g
  change (f (ρ g x)).val 1 = (f x).val g
  rw [f.isIntertwining]
  change (f x).val (1*g) = (f x).val g
  rw [one_mul]

lemma coindLift_ne_zero {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap (ρ.comp φ) σ) (hf : f ≠ 0) :
    coindLift φ f ≠ 0 := by
  intro hz
  apply hf
  rw [← coindEval_lift φ f,hz]
  rfl

lemma coindEval_ne_zero {G H X Y : Type*} [Group G] [Group H]
    [AddCommMonoid X] [Module ℂ X] [AddCommMonoid Y] [Module ℂ Y]
    (φ : H →* G) {ρ : Representation ℂ G X} {σ : Representation ℂ H Y}
    (f : Representation.IntertwiningMap ρ (Representation.coind φ σ)) (hf : f ≠ 0) :
    coindEval φ f ≠ 0 := by
  intro hz
  apply hf
  rw [← coindLift_eval φ f,hz]
  ext x g
  rfl

theorem word_supportLE {n d : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0) :
    SupportLE (wordRep n d) σ := word_support_separates σ h

theorem word_coind_supportLE {n d : ℕ} {H V : Type*} [Group H]
    [AddCommGroup V] [Module ℂ V] (φ : H →* Equiv.Perm (Fin n))
    (σ : Representation ℂ H V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), μ.colLen 0 ≤ d →
      ∃ f : Representation.IntertwiningMap ((spechtRep t).comp φ) σ, f ≠ 0) :
    SupportLE (wordRep n d) (Representation.coind φ σ) := by
  apply word_supportLE
  intro μ t ht
  obtain ⟨f,hf⟩ := h μ t ht
  exact ⟨coindLift φ f,coindLift_ne_zero φ f hf⟩

end Saxl
end
end

end OAI
