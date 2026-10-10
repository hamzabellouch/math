import Mathlib

namespace OAI


namespace Tachikawa

noncomputable section

abbrev k := FractionRing (MvPolynomial (Fin 3) (ZMod 2))

def SymmetricOver (K A : Type) [Field K] [Ring A] [Algebra K A] : Prop :=
  ∃ e : A ≃ₗ[K] Module.Dual K A,
    (∀ a b c : A, e (a * b) c = e b (c * a)) ∧
    (∀ a b c : A, e (a * b) c = e a (b * c))

def Counterexample : Prop :=
  ∃ (A : Type) (rA : Ring A),
    letI := rA
    ∃ (aA : Algebra k A),
      letI := aA
      Module.Finite k A ∧ SymmetricOver k A ∧
      ∃ (M : Type) (gM : AddCommGroup M),
        letI := gM
        ∃ (mA : Module A M) (mk : Module k M),
          letI := mA
          letI := mk
          IsScalarTower k A M ∧ Module.Finite k M ∧
          ¬ Module.Projective A M ∧
          ∀ n : ℕ, 0 < n →
            Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of A M) (ModuleCat.of A M) n)

end
end Tachikawa



noncomputable section
namespace Tachikawa

def DualBimodule (k R : Type*) [Field k] [Ring R] [Algebra k R] := Module.Dual k R

namespace DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance : FunLike (DualBimodule k R) R k := inferInstanceAs (FunLike (Module.Dual k R) R k)
instance : LinearMapClass (DualBimodule k R) k R k :=
  inferInstanceAs (LinearMapClass (Module.Dual k R) k R k)

instance : AddCommGroup (DualBimodule k R) := inferInstanceAs (AddCommGroup (Module.Dual k R))
instance : Module k (DualBimodule k R) := inferInstanceAs (Module k (Module.Dual k R))

@[ext] lemma ext {φ ψ : DualBimodule k R} (h : ∀ x, φ x = ψ x) : φ = ψ := LinearMap.ext h

@[simp] lemma add_apply (φ ψ : DualBimodule k R) (x : R) : (φ + ψ) x = φ x + ψ x := rfl
@[simp] lemma zero_apply (x : R) : (0 : DualBimodule k R) x = 0 := rfl
@[simp] lemma smul_apply (c : k) (φ : DualBimodule k R) (x : R) : (c • φ) x = c * φ x := rfl

instance leftModule : Module R (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulRight k a)
  one_smul φ := by ext x; change φ (x * 1) = φ x; simp
  mul_smul a b φ := by ext x; change φ (x * (a * b)) = φ ((x * a) * b); simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by ext x; change φ (x * (a + b)) = φ (x * a) + φ (x * b); simp [mul_add]
  zero_smul φ := by ext x; change φ (x * 0) = 0; simp

@[simp] lemma left_apply (a : R) (φ : DualBimodule k R) (x : R) : (a • φ) x = φ (x * a) := rfl

instance rightModule : Module Rᵐᵒᵖ (DualBimodule k R) where
  smul a φ := φ.comp (LinearMap.mulLeft k a.unop)
  one_smul φ := by ext x; change φ (1 * x) = φ x; simp
  mul_smul a b φ := by
    ext x
    change φ ((b.unop * a.unop) * x) = φ (b.unop * (a.unop * x))
    simp [mul_assoc]
  smul_zero a := by ext x; rfl
  smul_add a φ ψ := by ext x; rfl
  add_smul a b φ := by
    ext x
    change φ ((a.unop + b.unop) * x) = φ (a.unop * x) + φ (b.unop * x)
    simp [add_mul]
  zero_smul φ := by ext x; change φ (0 * x) = 0; simp

@[simp] lemma right_apply (a : Rᵐᵒᵖ) (φ : DualBimodule k R) (x : R) :
    (a • φ) x = φ (a.unop * x) := rfl

instance : SMulCommClass R Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp [mul_assoc]

instance : IsScalarTower k R (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.mul_smul_comm]

instance : IsScalarTower k Rᵐᵒᵖ (DualBimodule k R) where
  smul_assoc a b φ := by
    ext x
    simp [Algebra.smul_mul_assoc]

instance : SMulCommClass k R (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp

instance : SMulCommClass k Rᵐᵒᵖ (DualBimodule k R) where
  smul_comm a b φ := by ext x; simp

instance [FiniteDimensional k R] : FiniteDimensional k (DualBimodule k R) :=
  inferInstanceAs (FiniteDimensional k (Module.Dual k R))

end DualBimodule
end Tachikawa



namespace Tachikawa.DualBimodule
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

def coinduce {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) : Y →ₗ[R] DualBimodule k R where
  toFun y :=
    { toFun := fun r => g (r • y)
      map_add' := fun a b => by simp [add_smul]
      map_smul' := fun c r => by simp [smul_assoc] }
  map_add' a b := by
    ext r
    change g (r • (a + b)) = g (r • a) + g (r • b)
    simp [smul_add]
  map_smul' a y := by
    ext r
    change g (r • (a • y)) = g ((r * a) • y)
    rw [mul_smul]

@[simp] lemma coinduce_apply {Y : Type*} [AddCommGroup Y] [Module R Y] [Module k Y]
    [IsScalarTower k R Y] (g : Y →ₗ[k] k) (y : Y) (r : R) :
    coinduce g y r = g (r • y) := rfl

instance injective : Module.Injective R (DualBimodule k R) where
  out {X Y} _ _ _ _ f hf g := by
    let : Module k X := Module.compHom X (algebraMap k R)
    let : Module k Y := Module.compHom Y (algebraMap k R)
    let : IsScalarTower k R X := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let : IsScalarTower k R Y := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
    let g₀ : X →ₗ[k] k :=
      { toFun := fun x => g x 1
        map_add' := fun x y => by simp
        map_smul' := fun c x => by
          change g (algebraMap k R c • x) 1 = c • g x 1
          rw [map_smul]
          simp [Algebra.algebraMap_eq_smul_one] }
    obtain ⟨s, hs⟩ := (f.restrictScalars k).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr hf)
    refine ⟨coinduce (g₀.comp s), ?_⟩
    intro x
    ext r
    change g₀ (s (r • f x)) = g x r
    rw [← f.map_smul]
    have hs' : s (f (r • x)) = r • x := LinearMap.congr_fun hs (r • x)
    rw [hs']
    change g (r • x) 1 = g x r
    rw [map_smul]
    simp

end Tachikawa.DualBimodule



namespace Tachikawa

abbrev TrivialExtension (k R : Type*) [Field k] [Ring R] [Algebra k R] :=
  TrivSqZeroExt R (DualBimodule k R)

namespace TrivialExtension
variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

instance [FiniteDimensional k R] : FiniteDimensional k (TrivialExtension k R) :=
  inferInstanceAs (FiniteDimensional k (R × DualBimodule k R))

def trace : TrivialExtension k R →ₗ[k] k where
  toFun a := a.snd 1
  map_add' a b := by simp
  map_smul' c a := by simp

@[simp] lemma trace_apply (a : TrivialExtension k R) : trace a = a.snd 1 := rfl

lemma trace_mul (a b : TrivialExtension k R) :
    trace (a * b) = b.snd a.fst + a.snd b.fst := by
  change (a.fst • b.snd + MulOpposite.op b.fst • a.snd) 1 = _
  simp

lemma trace_comm (a b : TrivialExtension k R) : trace (a * b) = trace (b * a) := by
  rw [trace_mul, trace_mul, add_comm]

lemma trace_nondegenerate (a : TrivialExtension k R)
    (h : ∀ b : TrivialExtension k R, trace (a * b) = 0) : a = 0 := by
  have hfst : a.fst = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff k a.fst).mp
    intro φ
    have := h (TrivSqZeroExt.inr (φ : DualBimodule k R))
    rw [trace_mul] at this
    change φ a.fst + a.snd 0 = 0 at this
    simpa using this
  have hsnd : a.snd = 0 := by
    ext r
    have := h (TrivSqZeroExt.inl r)
    rw [trace_mul] at this
    change (0 : DualBimodule k R) a.fst + a.snd r = 0 at this
    simpa using this
  exact TrivSqZeroExt.ext hfst hsnd

end TrivialExtension



variable {k R : Type*} [Field k] [Ring R] [Algebra k R]

structure SymmetrizingForm where
  linear : R →ₗ[k] k
  comm : ∀ a b, linear (a * b) = linear (b * a)
  nondegenerate : ∀ a, (∀ b, linear (a * b) = 0) → a = 0

namespace SymmetrizingForm
variable (t : SymmetrizingForm (k := k) (R := R))

def toDual : R →ₗ[R] DualBimodule k R := DualBimodule.coinduce t.linear

@[simp] lemma toDual_apply (a x : R) : t.toDual a x = t.linear (x * a) := rfl

lemma toDual_injective : Function.Injective t.toDual := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  apply t.nondegenerate a
  intro b
  rw [t.comm]
  exact congrArg (fun f : DualBimodule k R => f b) ha

def dualEquiv [FiniteDimensional k R] : R ≃ₗ[R] DualBimodule k R :=
  LinearEquiv.ofBijective t.toDual ⟨t.toDual_injective,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank k R = Module.finrank k (DualBimodule k R) from
        (Subspace.dual_finrank_eq).symm) (f := t.toDual.restrictScalars k)).mp
          t.toDual_injective⟩

include t in
lemma injective [FiniteDimensional k R] : Module.Injective R R := by
  constructor
  intro X Y _ _ _ _ f hf g
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R (DualBimodule k R) X Y f hf
    (t.dualEquiv.toLinearMap.comp g)
  refine ⟨t.dualEquiv.symm.toLinearMap.comp h, ?_⟩
  intro x
  change t.dualEquiv.symm (h (f x)) = g x
  have hhx := LinearMap.congr_fun hh x
  change h (f x) = t.dualEquiv (g x) at hhx
  rw [hhx]
  exact t.dualEquiv.symm_apply_apply (g x)

end SymmetrizingForm

namespace TrivialExtension

def symmetrizingForm : SymmetrizingForm (k := k) (R := TrivialExtension k R) where
  linear := trace
  comm := trace_comm
  nondegenerate := trace_nondegenerate

instance [FiniteDimensional k R] : Module.Injective (TrivialExtension k R) (TrivialExtension k R) :=
  symmetrizingForm.injective

end TrivialExtension
end Tachikawa



namespace Tachikawa
variable {K A : Type} [Field K] [Ring A] [Algebra K A]
lemma SymmetrizingForm.symmetricOver (t : SymmetrizingForm (k := K) (R := A))
    [FiniteDimensional K A] : SymmetricOver K A := by
  refine ⟨t.dualEquiv.restrictScalars K, ?_, ?_⟩
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((c*a)*b)
    rw [mul_assoc]
  · intro a b c
    change t.linear (c * (a*b)) = t.linear ((b*c)*a)
    calc
      t.linear (c * (a*b)) = t.linear ((c*a)*b) := by rw [mul_assoc]
      _ = t.linear (b*(c*a)) := t.comm _ _
      _ = t.linear ((b*c)*a) := by rw [mul_assoc]
lemma TrivialExtension.symmetricOver [FiniteDimensional K A] :
    SymmetricOver K (TrivialExtension K A) :=
  (TrivialExtension.symmetrizingForm (k := K) (R := A)).symmetricOver
end Tachikawa



namespace Tachikawa
lemma counterexampleOf (A M : Type) [Ring A] [Algebra k A]
    [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
    [Module.Finite k A] [Module.Finite k M]
    (sym : SymmetricOver k A) (nonproj : ¬ Module.Projective A M)
    (van : ∀ n : ℕ, Subsingleton (CategoryTheory.Abelian.Ext
      (ModuleCat.of A M) (ModuleCat.of A M) (n+1))) : Counterexample := by
  refine ⟨A, inferInstance, inferInstance, inferInstance, sym, M, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, nonproj, ?_⟩
  intro n hn
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact van m
end Tachikawa

end

end OAI
