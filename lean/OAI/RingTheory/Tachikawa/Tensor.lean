import OAI.RingTheory.Tachikawa.CompleteResolution

namespace OAI


noncomputable section
open scoped TensorProduct
open TensorProduct
namespace Tachikawa

namespace BalancedTensor
variable {k R S M N P : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N]

def relations : Submodule S (M ⊗[k] N) :=
  Submodule.span S {x | ∃ r : R, ∃ m : M, ∃ n : N,
    x = (MulOpposite.op r • m) ⊗ₜ[k] n - m ⊗ₜ[k] (r • n)}

abbrev T := (M ⊗[k] N) ⧸ relations (k := k) (R := R) (S := S)

def mk : M →ₗ[S] N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N) :=
  TensorProduct.AlgebraTensorModule.curry
    (relations (k := k) (R := R) (S := S) (M := M) (N := N)).mkQ

lemma balance (r : R) (m : M) (n : N) :
    mk (k := k) (R := R) (S := S) (MulOpposite.op r • m) n = mk m (r • n) := by
  apply sub_eq_zero.mp
  change (relations (k := k) (R := R) (S := S)).mkQ _ -
    (relations (k := k) (R := R) (S := S)).mkQ _ = 0
  rw [← map_sub]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.subset_span ⟨r,m,n,rfl⟩)

variable [AddCommGroup P] [Module k P] [Module S P] [IsScalarTower k S P]

def lift (f : M →ₗ[S] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S] P :=
  (relations (k := k) (R := R) (S := S)).liftQ
    (TensorProduct.AlgebraTensorModule.lift f) (by
      apply Submodule.span_le.mpr
      rintro x ⟨r,m,n,rfl⟩
      change TensorProduct.AlgebraTensorModule.lift f _ = 0
      simp only [map_sub, TensorProduct.AlgebraTensorModule.lift_tmul]
      exact sub_eq_zero.mpr (hf r m n))

@[simp] lemma lift_mk (f : M →ₗ[S] N →ₗ[k] P)
    (hf : ∀ (r : R) (m : M) (n : N), f (MulOpposite.op r • m) n = f m (r • n)) (m : M) (n : N) :
    lift f hf (mk m n) = f m n := rfl

@[elab_as_elim] theorem induction_on
    {p : T (k := k) (R := R) (S := S) (M := M) (N := N) → Prop}
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N))
    (h0 : p 0) (ht : ∀ m n, p (mk m n))
    (ha : ∀ x y, p x → p y → p (x+y)) : p x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact h0
  clear hx
  obtain ⟨z, rfl⟩ := (relations (k := k) (R := R) (S := S)).mkQ_surjective x
  induction z using TensorProduct.inductionOn with
  | tmul m n => exact ht m n
  | add z z' hz hz' => exact ha _ _ hz hz'

omit [Module k P] [IsScalarTower k S P] in
@[ext] theorem hom_ext {f g : T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S] P}
    (h : ∀ m n, f (mk m n) = g (mk m n)) : f = g := by
  apply LinearMap.ext
  intro x
  induction x using induction_on with
  | h0 => simp
  | ht m n => exact h m n
  | ha x y hx hy => simp only [map_add, hx, hy]

instance [FiniteDimensional k M] [FiniteDimensional k N] :
    FiniteDimensional k (T (k := k) (R := R) (S := S) (M := M) (N := N)) := by
  change FiniteDimensional k
    ((M ⊗[k] N) ⧸ relations (k := k) (R := R) (S := S))
  exact Module.Finite.quotient k (relations (k := k) (R := R) (S := S))

end BalancedTensor
end Tachikawa

end


noncomputable section
open scoped TensorProduct
namespace Tachikawa.BalancedTensor
variable {k R S M N N' N'' : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

def mapRightBilinear (f : N →ₗ[R] N') :
    M →ₗ[S] N →ₗ[k] T (k := k) (R := R) (S := S) (M := M) (N := N') :=
  (mk (k := k) (R := R) (S := S)).compl₂ (f.restrictScalars k)

lemma mapRightBilinear_balanced (f : N →ₗ[R] N') (r : R) (m : M) (n : N) :
    mapRightBilinear (k := k) (S := S) f (MulOpposite.op r • m) n = mapRightBilinear (k := k) (S := S) f m (r • n) := by
  change mk (MulOpposite.op r • m) (f n) = mk m (f (r • n))
  rw [f.map_smul]
  exact balance r m (f n)

def mapRight (f : N →ₗ[R] N') :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S]
      T (k := k) (R := R) (S := S) (M := M) (N := N') :=
  lift (mapRightBilinear (k := k) (S := S) f) (mapRightBilinear_balanced f)

@[simp] lemma mapRight_mk (f : N →ₗ[R] N') (m : M) (n : N) :
    mapRight (k := k) (S := S) (M := M) f (mk m n) = mk (k := k) (R := R) (S := S) m (f n) := rfl

lemma mapRight_id : mapRight (k := k) (S := S) (M := M) (LinearMap.id : N →ₗ[R] N) =
    LinearMap.id := by
  apply hom_ext
  intro m n
  rfl

lemma mapRight_comp (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') :
    mapRight (k := k) (S := S) (M := M) (g.comp f) =
      (mapRight (k := k) (S := S) g).comp (mapRight (k := k) (S := S) f) := by
  apply hom_ext
  intro m n
  rfl

lemma mapRight_add (f g : N →ₗ[R] N') :
    mapRight (k := k) (S := S) (M := M) (f+g) = mapRight (k := k) (S := S) f + mapRight (k := k) (S := S) g := by
  apply hom_ext
  intro m n
  simp

lemma mapRight_zero : mapRight (k := k) (S := S) (M := M) (0 : N →ₗ[R] N') = 0 := by
  apply hom_ext
  intro m n
  simp

lemma mapRight_surjective (f : N →ₗ[R] N') (hf : Function.Surjective f) :
    Function.Surjective (mapRight (k := k) (S := S) (M := M) f) := by
  intro x
  induction x using induction_on with
  | h0 => exact ⟨0, map_zero _⟩
  | ht m n =>
    obtain ⟨n', rfl⟩ := hf n
    exact ⟨mk m n', rfl⟩
  | ha x y hx hy =>
    obtain ⟨a,rfl⟩ := hx
    obtain ⟨b,rfl⟩ := hy
    exact ⟨a+b, map_add _ _ _⟩

lemma mapRight_split (f : N →ₗ[R] N') (g : N' →ₗ[R] N) (h : g.comp f = LinearMap.id) :
    (mapRight (k := k) (S := S) (M := M) g).comp (mapRight (k := k) (S := S) f) = LinearMap.id := by
  rw [← mapRight_comp, h, mapRight_id]

variable [SMulCommClass S Rᵐᵒᵖ M] [IsScalarTower k Rᵐᵒᵖ M]

def rightUnit : T (k := k) (R := R) (S := S) (M := M) (N := R) →ₗ[S] M :=
  lift
    { toFun := fun m =>
        { toFun := fun r => MulOpposite.op r • m
          map_add' := by intro a b; rw [MulOpposite.op_add, add_smul]
          map_smul' := by
            intro c r
            rw [MulOpposite.op_smul, smul_assoc]
            rfl }
      map_add' := by intro m n; ext r; exact smul_add _ _ _
      map_smul' := by intro s m; ext r; exact (smul_comm s (MulOpposite.op r) m).symm }
    (fun r m a => by
      change MulOpposite.op a • MulOpposite.op r • m = MulOpposite.op (r*a) • m
      rw [← mul_smul, ← MulOpposite.op_mul])

@[simp] lemma rightUnit_mk (m : M) (r : R) : rightUnit (k := k) (S := S) (mk m r) =
    MulOpposite.op r • m := rfl

def rightUnitInv : M →ₗ[S] T (k := k) (R := R) (S := S) (M := M) (N := R) where
  toFun m := mk m 1
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

def rightUnitEquiv : T (k := k) (R := R) (S := S) (M := M) (N := R) ≃ₗ[S] M :=
  LinearEquiv.ofLinearMap rightUnit rightUnitInv
    (by ext m; change MulOpposite.op (1:R) • m = m; simp)
    (by
      apply hom_ext
      intro m r
      change mk (MulOpposite.op r • m) 1 = mk m r
      rw [balance]
      simp)

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M M' M'' N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M] [IsScalarTower k S M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M'] [IsScalarTower k S M']
  [AddCommGroup M''] [Module k M''] [Module S M''] [Module Rᵐᵒᵖ M''] [IsScalarTower k S M'']
  [AddCommGroup N] [Module k N] [Module R N]

def mapLeft (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) :
    T (k := k) (R := R) (S := S) (M := M) (N := N) →ₗ[S]
      T (k := k) (R := R) (S := S) (M := M') (N := N) :=
  lift ((mk (k := k) (R := R) (S := S)).comp f) (fun r m n => by
    change mk (f (MulOpposite.op r • m)) n = mk (f m) (r • n)
    rw [hf]
    exact balance r (f m) n)

@[simp] lemma mapLeft_mk (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (m : M) (n : N) :
    mapLeft (k := k) (N := N) f hf (mk m n) = mk (f m) n := rfl

lemma mapLeft_id : mapLeft (k := k) (R := R) (S := S) (N := N)
    (LinearMap.id : M →ₗ[S] M) (fun _ _ => rfl) = LinearMap.id := by
  apply hom_ext
  intro m n
  rfl

lemma mapLeft_comp (f : M →ₗ[S] M') (g : M' →ₗ[S] M'')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (hg : ∀ (r : Rᵐᵒᵖ) m, g (r • m) = r • g m) :
    (mapLeft (k := k) (N := N) g hg).comp (mapLeft f hf) =
      mapLeft (g.comp f) (fun r m => by simp only [LinearMap.comp_apply, hf, hg]) := by
  apply hom_ext
  intro m n
  rfl

lemma mapLeft_add (f g : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m)
    (hg : ∀ (r : Rᵐᵒᵖ) m, g (r • m) = r • g m) :
    mapLeft (k := k) (N := N) (f+g)
      (fun r m => by simp only [LinearMap.add_apply, hf, hg, smul_add]) =
      mapLeft f hf + mapLeft g hg := by
  apply hom_ext
  intro m n
  simp

lemma mapLeft_zero : mapLeft (k := k) (R := R) (S := S) (N := N)
    (0 : M →ₗ[S] M') (fun _ _ => by simp) = 0 := by
  apply hom_ext
  intro m n
  simp

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M N : Type*} [Field k] [Ring R] [Ring S]
  [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [SMulCommClass S Rᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module R N]

lemma fieldRelations_smul_mem (s : S) {x : M ⊗[k] N}
    (hx : x ∈ relations (k := k) (R := R) (S := k)) :
    s • x ∈ relations (k := k) (R := R) (S := k) := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r,m,n,rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨r,s • m,n,?_⟩
    simp only [smul_sub, TensorProduct.smul_tmul', smul_comm s (MulOpposite.op r)]
  | zero => exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    rw [smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih =>
    rw [smul_comm s c]
    exact Submodule.smul_mem _ c ih

lemma relations_restrictScalars :
    (relations (k := k) (R := R) (S := S) (M := M) (N := N)).restrictScalars k =
      relations (k := k) (R := R) (S := k) := by
  apply le_antisymm
  · let V : Submodule S (M ⊗[k] N) :=
      { (relations (k := k) (R := R) (S := k)).toAddSubmonoid with
        smul_mem' := fun s x hx => fieldRelations_smul_mem s hx }
    have h : relations (k := k) (R := R) (S := S) ≤ V := by
      apply Submodule.span_le.mpr
      intro x hx
      exact Submodule.subset_span hx
    exact h
  · apply Submodule.span_le.mpr
    intro x hx
    exact Submodule.subset_span hx

def restrictEquiv :
    T (k := k) (R := R) (S := S) (M := M) (N := N) ≃ₗ[k]
      T (k := k) (R := R) (S := k) (M := M) (N := N) :=
  (Submodule.Quotient.restrictScalarsEquiv k (relations (k := k) (R := R)
    (S := S) (M := M) (N := N))).symm.trans
      (Submodule.quotEquivOfEq _ _ relations_restrictScalars)

@[simp] lemma restrictEquiv_mk (m : M) (n : N) :
    restrictEquiv (mk (k := k) (R := R) (S := S) m n) =
      mk (k := k) (R := R) (S := k) m n := rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R N N' : Type*} [Field k] [Ring R] [Algebra k R]
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']

def leftUnit : T (k := k) (R := R) (S := k) (M := R) (N := N) →ₗ[k] N :=
  lift (Algebra.lsmul k k N).toLinearMap
    (fun r m n => by
      change (m*r) • n = m • r • n
      exact mul_smul m r n)

@[simp] lemma leftUnit_mk (r : R) (n : N) : leftUnit (k := k) (mk (k := k) (R := R) (S := k) r n) = r • n := rfl

def leftUnitEquiv : T (k := k) (R := R) (S := k) (M := R) (N := N) ≃ₗ[k] N :=
  LinearEquiv.ofLinearMap leftUnit (mk (k := k) (R := R) (S := k) 1)
    (by ext n; exact one_smul R n)
    (by
      apply hom_ext
      intro r n
      change mk (k := k) (R := R) (S := k) 1 (r • n) = mk r n
      rw [← balance]
      change mk (k := k) (R := R) (S := k) (1*r) n = mk r n
      rw [one_mul])

variable (ι : Type*) [Fintype ι]

def freeEval : T (k := k) (R := R) (S := k) (M := ι → R) (N := N) →ₗ[k] (ι → N) :=
  lift
    { toFun m :=
        { toFun n i := m i • n
          map_add' n n' := by ext i; exact smul_add _ _ _
          map_smul' a n := by ext i; exact smul_comm _ _ _ }
      map_add' m m' := by ext n i; exact add_smul _ _ _
      map_smul' a m := by ext n i; exact smul_assoc a (m i) n }
    (fun r m n => by ext i; exact mul_smul (m i) r n)

omit [Fintype ι] in
@[simp] lemma freeEval_mk (m : ι → R) (n : N) (i : ι) :
    freeEval (k := k) (R := R) ι (mk (k := k) (R := R) (S := k) m n) i = m i • n := rfl

def freeInv : (ι → N) →ₗ[k] T (k := k) (R := R) (S := k) (M := ι → R) (N := N) := by
  classical
  exact ∑ i, (mk (k := k) (R := R) (S := k) (Pi.single i (1:R))).comp (LinearMap.proj i)

lemma freeEval_freeInv (x : ι → N) : freeEval (k := k) (R := R) ι (freeInv (k := k) (R := R) ι x) = x := by
  classical
  ext i
  simp [freeInv, freeEval_mk, Pi.single_apply]

lemma freeInv_freeEval (x : T (k := k) (R := R) (S := k) (M := ι → R) (N := N)) :
    freeInv ι (freeEval ι x) = x := by
  classical
  induction x using induction_on with
  | h0 => simp
  | ht m n =>
    simp only [freeInv, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply, freeEval_mk]
    change (∑ i, (mk (k := k) (R := R) (S := k) (Pi.single i (1:R))) (m i • n)) = mk m n
    simp_rw [← balance]
    have hm : (∑ i, (MulOpposite.op (m i)) • (Pi.single i (1:R))) = m := by
      ext j
      simp [Pi.single_apply, apply_ite]
    rw [← LinearMap.sum_apply, ← map_sum, hm]
  | ha x y hx hy => simp only [map_add, hx, hy]

def freeEquiv : T (k := k) (R := R) (S := k) (M := ι → R) (N := N) ≃ₗ[k] (ι → N) :=
  LinearEquiv.ofLinearMap (freeEval ι) (freeInv ι)
    (by apply LinearMap.ext; exact freeEval_freeInv (k := k) (R := R) ι)
    (by apply LinearMap.ext; exact freeInv_freeEval ι)

lemma freeEquiv_mapRight (f : N →ₗ[R] N')
    (x : T (k := k) (R := R) (S := k) (M := ι → R) (N := N)) (i : ι) :
    freeEquiv ι (mapRight (k := k) (S := k) f x) i = f (freeEquiv ι x i) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => exact (f.map_smul (m i) n).symm
  | ha x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Tachikawa.BalancedTensor

end


noncomputable section
namespace Tachikawa.BalancedTensor
variable {k R S M M' N N' N'' : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M]
  [AddCommGroup M'] [Module k M'] [Module S M'] [Module Rᵐᵒᵖ M']
  [IsScalarTower k S M']
  [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
  [AddCommGroup N'] [Module k N'] [Module R N'] [IsScalarTower k R N']
  [AddCommGroup N''] [Module k N''] [Module R N''] [IsScalarTower k R N'']

omit [IsScalarTower k Rᵐᵒᵖ M] in
lemma mapLeft_mapRight (f : M →ₗ[S] M')
    (hf : ∀ (r : Rᵐᵒᵖ) m, f (r • m) = r • f m) (g : N →ₗ[R] N') :
    (mapLeft (k := k) f hf).comp (mapRight (k := k) (S := S) g) =
      (mapRight (k := k) (S := S) g).comp (mapLeft (k := k) f hf) := by
  apply hom_ext
  intro m n
  rfl

omit [IsScalarTower k Rᵐᵒᵖ M] in
lemma restrictEquiv_mapRight [SMulCommClass S Rᵐᵒᵖ M] (g : N →ₗ[R] N')
    (x : T (k := k) (R := R) (S := S) (M := M) (N := N)) :
    restrictEquiv (mapRight (k := k) (S := S) g x) =
      mapRight (k := k) (S := k) g (restrictEquiv x) := by
  induction x using induction_on with
  | h0 => simp
  | ht m n => rfl
  | ha x y hx hy => simp only [map_add, hx, hy]

def oppositeFree (ι : Type) : (ι → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (ι → R) where
  toFun x i := (x i).unop
  invFun x i := MulOpposite.op (x i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma free_mapRight_exact (ι : Type) [Fintype ι]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := k) (M := ι → R) f)
      (mapRight (k := k) (S := k) (M := ι → R) g) := by
  intro x
  constructor
  · intro hx
    have hz : ∀ i, g (freeEquiv ι x i) = 0 := by
      intro i
      rw [← freeEquiv_mapRight, hx, map_zero]
      rfl
    choose y hy using fun i => (he (freeEquiv ι x i)).mp (hz i)
    refine ⟨(freeEquiv (k := k) (R := R) ι).symm y, ?_⟩
    apply (freeEquiv (k := k) (R := R) ι).injective
    ext i
    rw [freeEquiv_mapRight, LinearEquiv.apply_symm_apply]
    exact hy i
  · rintro ⟨y,rfl⟩
    apply (freeEquiv (k := k) (R := R) ι).injective
    ext i
    rw [freeEquiv_mapRight, freeEquiv_mapRight, map_zero]
    exact (he _).mpr ⟨_,rfl⟩

lemma field_mapRight_exact [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := k) (M := M) f)
      (mapRight (k := k) (S := k) (M := M) g) := by
  let c := finiteFreeCover (R := Rᵐᵒᵖ) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let e := oppositeFree (R := R) (Fin c.rank)
  let u := e.toLinearMap.comp i
  let p := c.map.comp e.symm.toLinearMap
  have hp : p.comp u = LinearMap.id := by
    ext x
    exact LinearMap.congr_fun hi x
  let U {L : Type} [AddCommGroup L] [Module k L] [Module R L] :=
    mapLeft (k := k) (R := R) (S := k) (N := L) (u.restrictScalars k) u.map_smul
  let P {L : Type} [AddCommGroup L] [Module k L] [Module R L] :=
    mapLeft (k := k) (R := R) (S := k) (N := L) (p.restrictScalars k) p.map_smul
  have hPU {L : Type} [AddCommGroup L] [Module k L] [Module R L] :
      (P (L := L)).comp (U (L := L)) = LinearMap.id := by
    apply hom_ext
    intro m n
    change mk (k := k) (R := R) (S := k) (p (u m)) n = mk m n
    exact congrArg (fun z => mk (k := k) (R := R) (S := k) z n) (LinearMap.congr_fun hp m)
  intro x
  constructor
  · intro hx
    have hUx : mapRight (k := k) (S := k) g (U x) = 0 := by
      dsimp only [U]
      rw [← LinearMap.comp_apply, ← mapLeft_mapRight (u.restrictScalars k) u.map_smul g]
      change U (mapRight (k := k) (S := k) g x) = 0
      rw [hx,map_zero]
    obtain ⟨y,hy⟩ := (free_mapRight_exact (k := k) (Fin c.rank) f g he (U x)).mp hUx
    refine ⟨P y, ?_⟩
    dsimp only [P]
    rw [← LinearMap.comp_apply, ← mapLeft_mapRight (p.restrictScalars k) p.map_smul f]
    change P (mapRight (k := k) (S := k) f y) = x
    rw [hy]
    exact LinearMap.congr_fun hPU x
  · rintro ⟨y,rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, he.linearMap_comp_eq_zero, mapRight_zero]
    rfl

lemma mapRight_exact [SMulCommClass S Rᵐᵒᵖ M]
    [Module.Finite Rᵐᵒᵖ M] [Module.Projective Rᵐᵒᵖ M]
    (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (he : Function.Exact f g) :
    Function.Exact (mapRight (k := k) (S := S) (M := M) f)
      (mapRight (k := k) (S := S) (M := M) g) := by
  intro x
  constructor
  · intro hx
    have hz : mapRight (k := k) (S := k) (M := M) g (restrictEquiv x) = 0 := by
      rw [← restrictEquiv_mapRight, hx,map_zero]
    obtain ⟨y,hy⟩ := (field_mapRight_exact (k := k) f g he (restrictEquiv x)).mp hz
    refine ⟨restrictEquiv.symm y, ?_⟩
    apply restrictEquiv.injective
    rw [restrictEquiv_mapRight, LinearEquiv.apply_symm_apply, hy]
  · rintro ⟨y,rfl⟩
    rw [← LinearMap.comp_apply, ← mapRight_comp, he.linearMap_comp_eq_zero, mapRight_zero]
    rfl

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
variable {k R S M : Type} [Field k] [Ring R] [Ring S]
  [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M]
  [IsScalarTower k S M] [IsScalarTower k Rᵐᵒᵖ M] [SMulCommClass S Rᵐᵒᵖ M]
  (ι : Type) [Fintype ι]

def rightFreeEval : T (k := k) (R := R) (S := S) (M := M) (N := ι → R) →ₗ[S] (ι → M) :=
  LinearMap.pi fun i => (rightUnit (k := k) (R := R) (S := S)).comp
    (mapRight (k := k) (S := S) (LinearMap.proj i))

omit [Fintype ι] in
@[simp] lemma rightFreeEval_mk (m : M) (x : ι → R) (i : ι) :
    rightFreeEval ι (mk (k := k) (R := R) (S := S) m x) i = MulOpposite.op (x i) • m := rfl

def rightFreeInv : (ι → M) →ₗ[S] T (k := k) (R := R) (S := S) (M := M) (N := ι → R) := by
  classical
  exact ∑ i, ((mk (k := k) (R := R) (S := S)).flip (Pi.single i (1:R))).comp (LinearMap.proj i)

lemma rightFreeEval_inv (x : ι → M) : rightFreeEval (k := k) (R := R) (S := S) ι (rightFreeInv (k := k) (R := R) (S := S) ι x) = x := by
  classical
  ext i
  simp only [rightFreeInv, map_sum, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.flip_apply, LinearMap.proj_apply, rightFreeEval_mk, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ h
    simp [Ne.symm h]
  · simp

lemma rightFreeInv_eval (x : T (k := k) (R := R) (S := S) (M := M) (N := ι → R)) :
    rightFreeInv ι (rightFreeEval ι x) = x := by
  classical
  induction x using induction_on with
  | h0 => simp
  | ht m n =>
    simp only [rightFreeInv, LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.proj_apply, rightFreeEval_mk, LinearMap.flip_apply]
    simp_rw [balance]
    have hn : (∑ i, n i • Pi.single i (1:R)) = n := by
      ext j
      simp [Pi.single_apply, apply_ite]
    rw [← map_sum, hn]
  | ha x y hx hy => simp only [map_add, hx, hy]

def rightFreeEquiv : T (k := k) (R := R) (S := S) (M := M) (N := ι → R) ≃ₗ[S] (ι → M) :=
  { rightFreeEval (k := k) (R := R) (S := S) (M := M) ι with
    invFun := rightFreeInv (k := k) (R := R) (S := S) (M := M) ι
    left_inv := rightFreeInv_eval ι
    right_inv := rightFreeEval_inv ι }

variable {N : Type} [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]

lemma map_projective [Module.Projective S M] [Module.Finite R N] [Module.Projective R N] :
    Module.Projective S (T (k := k) (R := R) (S := S) (M := M) (N := N)) := by
  let c := finiteFreeCover (R := R) (M := N)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let : Module.Projective S (Fin c.rank → M) :=
    Module.Projective.of_equiv' DFinsupp.linearEquivFunOnFintype
  let : Module.Projective S (T (k := k) (R := R) (S := S) (M := M) (N := Fin c.rank → R)) :=
    Module.Projective.of_equiv' (rightFreeEquiv (k := k) (R := R) (S := S) (M := M) (Fin c.rank)).symm
  exact Module.Projective.of_split (mapRight (k := k) (S := S) i)
    (mapRight (k := k) (S := S) c.map) (mapRight_split i c.map hi)

end Tachikawa.BalancedTensor



namespace Tachikawa.BalancedTensor
open CategoryTheory
open scoped ModuleCat.Algebra
variable {k R S M : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  [AddCommGroup M] [Module k M] [Module S M] [Module Rᵐᵒᵖ M] [IsScalarTower k S M]

def functor : ModuleCat R ⥤ ModuleCat S where
  obj N := ModuleCat.of S (T (k := k) (R := R) (S := S) (M := M) (N := N))
  map f := ModuleCat.ofHom (mapRight f.hom)
  map_id _ := ModuleCat.hom_ext mapRight_id
  map_comp _ _ := ModuleCat.hom_ext (mapRight_comp _ _)

instance : (functor (k := k) (R := R) (S := S) (M := M)).Additive where
  map_add {_X _Y f g} := ModuleCat.hom_ext (mapRight_add f.hom g.hom)




instance : (functor (k := k) (R := R) (S := S) (M := M)).Linear k where
  map_smul {X Y} f c := by
    apply ModuleCat.hom_ext
    apply hom_ext
    intro m x
    change mk (k := k) (R := R) (S := S) m ((algebraMap k R c) • f x) =
      (algebraMap k S c) • mk m (f x)
    rw [IsScalarTower.algebraMap_smul R,IsScalarTower.algebraMap_smul S]
    exact (mk m).map_smul c (f x)
end Tachikawa.BalancedTensor



namespace Tachikawa.OuterTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [CommRing k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]

def Obj (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) := M ⊗[k] N

instance (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : AddCommGroup (Obj k A B M N) :=
  inferInstanceAs (AddCommGroup (M ⊗[k] N))
instance (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : Module k (Obj k A B M N) :=
  inferInstanceAs (Module k (M ⊗[k] N))

def action (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    A ⊗[k] B →ₐ[k] Module.End k (M ⊗[k] N) :=
  Algebra.TensorProduct.lift
    ((Module.End.rTensorAlgHom k M N).comp (Algebra.lsmul k k M))
    ((Module.End.lTensorAlgHom k N M).comp (Algebra.lsmul k k N)) (by
      intro a b
      change ((Algebra.lsmul k k M a).rTensor N).comp ((Algebra.lsmul k k N b).lTensor M) =
        ((Algebra.lsmul k k N b).lTensor M).comp ((Algebra.lsmul k k M a).rTensor N)
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor])

instance (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) : Module (A ⊗[k] B) (Obj k A B M N) :=
  show Module (A ⊗[k] B) (M ⊗[k] N) from
  Module.compHom _ (action k A B M N).toRingHom
instance (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    IsScalarTower k (A ⊗[k] B) (Obj k A B M N) :=
  IsScalarTower.of_algebraMap_smul fun r x => by
    change (action k A B M N (algebraMap k (A ⊗[k] B) r)) x = r • x
    rw [AlgHom.commutes]
    rfl

@[simp] lemma tmul_smul_tmul (M : ModuleCat.{u} A) (N : ModuleCat.{u} B)
    (a : A) (b : B) (x : M) (y : N) :
    (a ⊗ₜ[k] b) • (show Obj k A B M N from x ⊗ₜ[k] y) = (a • x) ⊗ₜ[k] (b • y) := rfl

variable {k A B}
lemma map_action {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (r : A ⊗[k] B) :
    (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)).comp
      (action k A B M N r) =
    (action k A B M' N' r).comp
      (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)) := by
  induction r using TensorProduct.inductionOn with
  | tmul a b =>
    apply TensorProduct.ext'
    intro x y
    change (f.hom (a • x)) ⊗ₜ[k] (g.hom (b • y)) = (a • f.hom x) ⊗ₜ[k] (b • g.hom y)
    rw [map_smul, map_smul]
  | add r s hr hs =>
    simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hr, hs]

def map {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B} (f : M ⟶ M') (g : N ⟶ N') :
    Obj k A B M N →ₗ[A ⊗[k] B] Obj k A B M' N' where
  toFun := TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)
  map_add' := map_add _
  map_smul' r z := LinearMap.congr_fun (map_action f g r) z

@[simp] lemma map_tmul {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (x : M) (y : N) :
    map (k := k) f g (x ⊗ₜ[k] y) = f x ⊗ₜ[k] g y := rfl

lemma map_comp {M M' M'' : ModuleCat.{u} A} {N N' N'' : ModuleCat.{u} B}
    (f : M ⟶ M') (f' : M' ⟶ M'') (g : N ⟶ N') (g' : N' ⟶ N'') :
    (map (k := k) f' g').comp (map f g) = map (f ≫ f') (g ≫ g') := by
  apply LinearMap.restrictScalars_injective k
  change (TensorProduct.map (f'.hom.restrictScalars k) (g'.hom.restrictScalars k)).comp
    (TensorProduct.map (f.hom.restrictScalars k) (g.hom.restrictScalars k)) = _
  exact (TensorProduct.map_comp _ _ _ _).symm

lemma map_id (M : ModuleCat.{u} A) (N : ModuleCat.{u} B) :
    map (k := k) (𝟙 M) (𝟙 N) = LinearMap.id := by
  apply LinearMap.restrictScalars_injective k
  change TensorProduct.map (LinearMap.id : M →ₗ[k] M) (LinearMap.id : N →ₗ[k] N) = LinearMap.id
  exact TensorProduct.map_id

variable (k A B)
def bifunctor : ModuleCat.{u} A ⥤ ModuleCat.{u} B ⥤ ModuleCat.{u} (A ⊗[k] B) where
  obj M :=
    { obj := fun N => ModuleCat.of _ (Obj k A B M N)
      map := fun g => ModuleCat.ofHom (map (𝟙 M) g)
      map_id := fun N => ModuleCat.hom_ext (map_id M N)
      map_comp := fun g g' => by
        apply ModuleCat.hom_ext
        simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, Category.id_comp] using
          (map_comp (k := k) (𝟙 M) (𝟙 M) g g').symm }
  map {M M'} f :=
    { app := fun N => ModuleCat.ofHom (map f (𝟙 N))
      naturality := fun N N' g => by
        apply ModuleCat.hom_ext
        simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, map_comp,
          Category.id_comp, Category.comp_id] }
  map_id M := by
    apply NatTrans.ext
    funext N
    exact ModuleCat.hom_ext (map_id (k := k) M N)
  map_comp f f' := by
    apply NatTrans.ext
    funext N
    apply ModuleCat.hom_ext
    change map (f ≫ f') (𝟙 N) = (map f' (𝟙 N)).comp (map f (𝟙 N))
    simpa only [ModuleCat.hom_ofHom, ModuleCat.hom_comp, Category.id_comp] using
      (map_comp (k := k) f f' (𝟙 N) (𝟙 N)).symm

end Tachikawa.OuterTensor



namespace Tachikawa
open scoped TensorProduct
namespace SymmetrizingForm
variable {k R S : Type*} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (t : SymmetrizingForm (k := k) (R := R)) (u : SymmetrizingForm (k := k) (R := S))

def tensorTrace : R ⊗[k] S →ₗ[k] k :=
  (TensorProduct.lid k k).toLinearMap.comp (TensorProduct.map t.linear u.linear)

@[simp] lemma tensorTrace_tmul (r : R) (s : S) :
    tensorTrace t u (r ⊗ₜ[k] s) = t.linear r * u.linear s := rfl

lemma tensorTrace_comm (a b : R ⊗[k] S) :
    tensorTrace t u (a*b) = tensorTrace t u (b*a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r s =>
    induction b using TensorProduct.inductionOn with
    | tmul r' s' => simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul,
        t.comm r r', u.comm s s']
    | add b c hb hc => simp only [mul_add, add_mul, map_add, hb, hc]
  | add a c ha hc => simp only [add_mul, mul_add, map_add, ha, hc]

variable [FiniteDimensional k R] [FiniteDimensional k S]

def tensorDualEquiv : R ⊗[k] S ≃ₗ[k] Module.Dual k (R ⊗[k] S) :=
  (TensorProduct.congr (t.dualEquiv.restrictScalars k) (u.dualEquiv.restrictScalars k)).trans
    (TensorProduct.dualDistribEquiv k R S)

lemma tensorDualEquiv_apply (a b : R ⊗[k] S) :
    tensorDualEquiv t u a b = tensorTrace t u (b*a) := by
  induction a using TensorProduct.inductionOn with
  | tmul r s =>
    induction b using TensorProduct.inductionOn with
    | tmul r' s' =>
      dsimp only [tensorDualEquiv, DualBimodule]
      simp only [Algebra.TensorProduct.tmul_mul_tmul, tensorTrace_tmul]
      change u.linear (s'*s) * t.linear (r'*r) = t.linear (r'*r) * u.linear (s'*s)
      exact mul_comm _ _
    | add b c hb hc => simp only [map_add, add_mul, hb, hc]
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, mul_add, ha, hc]

def tensor : SymmetrizingForm (k := k) (R := R ⊗[k] S) where
  linear := tensorTrace t u
  comm := tensorTrace_comm t u
  nondegenerate a h := by
    apply (tensorDualEquiv t u).injective
    apply LinearMap.ext
    intro b
    rw [tensorDualEquiv_apply, tensorTrace_comm, h]
    simp

end SymmetrizingForm
end Tachikawa



namespace Tachikawa
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace Enveloping
variable (k R S : Type) [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
abbrev Alg := R ⊗[k] Sᵐᵒᵖ

variable {k R S}

def Obj (M : ModuleCat (Alg k R S)) : Type := M
instance (M : ModuleCat (Alg k R S)) : AddCommGroup (Obj M) :=
  inferInstanceAs (AddCommGroup M)
instance (M : ModuleCat (Alg k R S)) : Module (Alg k R S) (Obj M) :=
  inferInstanceAs (Module (Alg k R S) M)
instance (M : ModuleCat (Alg k R S)) : Module k (Obj M) :=
  inferInstanceAs (Module k M)
instance (M : ModuleCat (Alg k R S)) : IsScalarTower k (Alg k R S) (Obj M) :=
  inferInstanceAs (IsScalarTower k (Alg k R S) M)
instance (M : ModuleCat (Alg k R S)) : Module R (Obj M) :=
  Module.compHom (Obj M) (Algebra.TensorProduct.includeLeft : R →ₐ[k] R ⊗[k] Sᵐᵒᵖ).toRingHom
instance (M : ModuleCat (Alg k R S)) : Module Sᵐᵒᵖ (Obj M) :=
  Module.compHom (Obj M) (Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] R ⊗[k] Sᵐᵒᵖ).toRingHom
instance (M : ModuleCat (Alg k R S)) : IsScalarTower k R (Obj M) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := R) (M := Obj M) fun r x => by
    change ((Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S) (algebraMap k R r)) • (show M from x) = r • x
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_smul (Alg k R S) r x
instance (M : ModuleCat (Alg k R S)) : IsScalarTower k Sᵐᵒᵖ (Obj M) :=
  IsScalarTower.of_algebraMap_smul (R := k) (A := Sᵐᵒᵖ) (M := Obj M) fun r x => by
    change ((Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S) (algebraMap k Sᵐᵒᵖ r)) • (show M from x) = r • x
    rw [AlgHom.commutes]
    exact IsScalarTower.algebraMap_smul (Alg k R S) r x
instance (M : ModuleCat (Alg k R S)) : SMulCommClass R Sᵐᵒᵖ (Obj M) where
  smul_comm r s m := by
    change ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) : Alg k R S) • (((1:R) ⊗ₜ[k] s) • m) =
      ((1:R) ⊗ₜ[k] s) • ((r ⊗ₜ[k] (1:Sᵐᵒᵖ)) • m)
    rw [← mul_smul, ← mul_smul]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

def leftMap {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) : Obj M →ₗ[R] Obj N where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' r x := f.hom.map_smul ((Algebra.TensorProduct.includeLeft : R →ₐ[k] Alg k R S) r) x

def rightMap {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) : Obj M →ₗ[Sᵐᵒᵖ] Obj N where
  toFun := f
  map_add' := f.hom.map_add
  map_smul' s x := f.hom.map_smul ((Algebra.TensorProduct.includeRight : Sᵐᵒᵖ →ₐ[k] Alg k R S) s) x

@[simp] lemma leftMap_apply {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) (x : Obj M) :
    leftMap f x = f x := rfl
@[simp] lemma rightMap_apply {M N : ModuleCat (Alg k R S)} (f : M ⟶ N) (x : Obj M) :
    rightMap f x = f x := rfl

lemma tmul_smul (M : ModuleCat (Alg k R S)) (r : R) (s : Sᵐᵒᵖ) (x : Obj M) :
    (r ⊗ₜ[k] s) • x = r • s • x := by
  change _ = (r ⊗ₜ[k] (1:Sᵐᵒᵖ)) • ((1:R) ⊗ₜ[k] s) • x
  rw [← mul_smul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
end Enveloping

namespace SymmetrizingForm
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

def op (t : SymmetrizingForm (k := k) (R := R)) :
    SymmetrizingForm (k := k) (R := Rᵐᵒᵖ) where
  linear := t.linear.comp (MulOpposite.opLinearEquiv k).symm.toLinearMap
  comm a b := t.comm b.unop a.unop
  nondegenerate a ha := by
    apply MulOpposite.unop_injective
    apply t.nondegenerate a.unop
    intro b
    have h := ha (MulOpposite.op b)
    change t.linear (b * a.unop) = 0 at h
    exact (t.comm _ _).trans h

end SymmetrizingForm
end Tachikawa



namespace Tachikawa.Enveloping
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]

instance objFinite (M : ModuleCat (Alg k R S)) [FiniteDimensional k M] :
    FiniteDimensional k (Obj M) := inferInstanceAs (FiniteDimensional k M)

def leftFunctor : ModuleCat (Alg k R S) ⥤ ModuleCat R where
  obj M := ModuleCat.of R (Obj M)
  map f := ModuleCat.ofHom (leftMap f)

def rightFunctor : ModuleCat (Alg k R S) ⥤ ModuleCat Sᵐᵒᵖ where
  obj M := ModuleCat.of Sᵐᵒᵖ (Obj M)
  map f := ModuleCat.ofHom (rightMap f)

instance : (leftFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := rfl
instance : (rightFunctor (k := k) (R := R) (S := S)).Additive where
  map_add := rfl

def freeLeftEquiv (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S)) ≃ₗ[R] (Fin n → (R ⊗[k] Sᵐᵒᵖ)) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    ext i
    change (r ⊗ₜ[k] (1:Sᵐᵒᵖ)) * x i = r • x i
    induction x i using TensorProduct.inductionOn with
    | tmul a b => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [mul_add, smul_add, hx, hy]

def freeRightEquiv (n : ℕ) :
    Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S)) ≃ₗ[Sᵐᵒᵖ]
      (Fin n → (Sᵐᵒᵖ ⊗[k] R)) where
  toFun x i := TensorProduct.comm k R Sᵐᵒᵖ (x i)
  invFun x i := TensorProduct.comm k Sᵐᵒᵖ R (x i)
  left_inv x := by
    apply funext
    intro i
    exact (TensorProduct.comm k R Sᵐᵒᵖ).left_inv (x i)
  right_inv x := by ext i; exact (TensorProduct.comm k R Sᵐᵒᵖ).right_inv (x i)
  map_add' _ _ := by ext i; exact map_add _ _ _
  map_smul' s x := by
    ext i
    change TensorProduct.comm k R Sᵐᵒᵖ (((1:R) ⊗ₜ[k] s) * x i) =
      s • TensorProduct.comm k R Sᵐᵒᵖ (x i)
    induction x i using TensorProduct.inductionOn with
    | tmul a b => simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        TensorProduct.comm_tmul, TensorProduct.smul_tmul', smul_eq_mul]
    | add x y hx hy => simp only [mul_add, map_add, smul_add, hx, hy]

lemma freeLeftProjective (n : ℕ) :
    Module.Projective R (Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S))) :=
  Module.Projective.of_equiv' (freeLeftEquiv (k := k) (R := R) (S := S) n).symm

lemma freeRightProjective (n : ℕ) :
    Module.Projective Sᵐᵒᵖ (Obj (ModuleCat.of (Alg k R S) (Fin n → Alg k R S))) :=
  Module.Projective.of_equiv' (freeRightEquiv (k := k) (R := R) (S := S) n).symm

lemma projective_left (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    Module.Projective R (Obj M) := by
  let c := finiteFreeCover (R := Alg k R S) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let := freeLeftProjective (k := k) (R := R) (S := S) c.rank
  apply Module.Projective.of_split
    (leftMap (ModuleCat.ofHom i)) (leftMap (ModuleCat.ofHom c.map))
  ext x
  exact LinearMap.congr_fun hi x

lemma projective_right (M : ModuleCat (Alg k R S))
    [Module.Finite (Alg k R S) M] [Module.Projective (Alg k R S) M] :
    Module.Projective Sᵐᵒᵖ (Obj M) := by
  let c := finiteFreeCover (R := Alg k R S) (M := M)
  obtain ⟨i,hi⟩ := Module.projective_lifting_property c.map LinearMap.id c.surjective
  let := freeRightProjective (k := k) (R := R) (S := S) c.rank
  apply Module.Projective.of_split
    (rightMap (ModuleCat.ofHom i)) (rightMap (ModuleCat.ofHom c.map))
  ext x
  exact LinearMap.congr_fun hi x

end Tachikawa.Enveloping

end

end OAI
