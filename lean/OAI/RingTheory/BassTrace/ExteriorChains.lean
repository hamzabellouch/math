import OAI.RingTheory.BassTrace.TraceCoefficients

namespace OAI

noncomputable section

namespace BassTrace

namespace Chains

open scoped BigOperators

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

abbrev contraction (α : M →ₗ[R] R) : ExteriorAlgebra R M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) α

lemma contraction_square (α : M →ₗ[R] R) (x : ExteriorAlgebra R M) :
    contraction α (contraction α x) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft α x

@[simp] lemma contraction_one (α : M →ₗ[R] R) :
    contraction α (1 : ExteriorAlgebra R M) = 0 :=
  CliffordAlgebra.contractLeft_one _ α

@[simp] lemma contraction_ι (α : M →ₗ[R] R) (v : M) :
    contraction α (ExteriorAlgebra.ι R v) = algebraMap R _ (α v) :=
  CliffordAlgebra.contractLeft_ι _ α v

lemma contraction_ι_mul (α : M →ₗ[R] R) (v : M) (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) =
      α v • x - ExteriorAlgebra.ι R v * contraction α x :=
  CliffordAlgebra.contractLeft_ι_mul α v x

lemma cone_contraction (α : M →ₗ[R] R) {v : M} (hv : α v = 1)
    (x : ExteriorAlgebra R M) :
    contraction α (ExteriorAlgebra.ι R v * x) +
      ExteriorAlgebra.ι R v * contraction α x = x := by
  rw [contraction_ι_mul, hv, one_smul, sub_add_cancel]

lemma contraction_map (α : M →ₗ[R] R) (β : N →ₗ[R] R) (f : M →ₗ[R] N)
    (hf : ∀ v, β (f v) = α v) (x : ExteriorAlgebra R M) :
    contraction β (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f (contraction α x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contraction, AlgHom.commutes]
  | add x y hx hy => simp only [map_add, hx, hy]
  | ι_mul x v hx =>
    change contraction β (ExteriorAlgebra.map f (ExteriorAlgebra.ι R v * x)) = _
    rw [map_mul, ExteriorAlgebra.map_apply_ι, contraction_ι_mul, contraction_ι_mul,
      hf, hx, map_sub, map_smul, map_mul, ExteriorAlgebra.map_apply_ι]

lemma contraction_ιMulti_succ (α : M →ₗ[R] R) {n : ℕ} (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      α (v 0) • ExteriorAlgebra.ιMulti R n (fun i => v i.succ) -
        ExteriorAlgebra.ι R (v 0) *
          contraction α (ExteriorAlgebra.ιMulti R n (fun i => v i.succ)) := by
  rw [ExteriorAlgebra.ιMulti_succ_apply, contraction_ι_mul]
  rfl

lemma contraction_ιMulti (α : M →ₗ[R] R) (n : ℕ) (v : Fin (n+1) → M) :
    contraction α (ExteriorAlgebra.ιMulti R (n+1) v) =
      ∑ i : Fin (n+1), ((-1 : R)^i.val * α (v i)) •
        ExteriorAlgebra.ιMulti R n (fun j => v (i.succAbove j)) := by
  induction n with
  | zero =>
    rw [contraction_ιMulti_succ]
    simp
  | succ n ih =>
    rw [contraction_ιMulti_succ, ih]
    conv_rhs => rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
    rw [sub_eq_add_neg]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    simp only [Fin.val_succ, pow_succ, Matrix.vecTail, Function.comp_def, Fin.succ_succAbove_succ,
      Fin.succAbove_ne_zero_zero (Fin.succ_ne_zero i), mul_smul_comm,
      mul_neg, mul_one, neg_mul, neg_smul]

lemma contraction_mem_exteriorPower (α : M →ₗ[R] R) (n : ℕ)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n+1) M) :
    contraction α x ∈ ⋀[R]^n M := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree R (n+1)] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    induction n with
    | zero =>
      rw [contraction_ιMulti_succ]
      simp only [ExteriorAlgebra.ιMulti_zero_apply, contraction_one, mul_zero, sub_zero]
      exact Submodule.smul_mem _ _ (by simp [ExteriorAlgebra.exteriorPower])
    | succ n ih =>
      rw [contraction_ιMulti_succ]
      apply Submodule.sub_mem
      · exact Submodule.smul_mem _ _ (ExteriorAlgebra.ιMulti_range R (n+1) ⟨_, rfl⟩)
      · have ht := ih (fun i => v i.succ)
        rw [ExteriorAlgebra.exteriorPower, pow_succ' ]
        exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v 0, rfl⟩) ht
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  | smul a x _ hx => simpa only [map_smul] using Submodule.smul_mem _ a hx

variable (Y : Type*)

abbrev Vectors := Y →₀ ℂ

abbrev Algebra := ExteriorAlgebra ℂ (Vectors Y)

abbrev Degree (n : ℕ) := ⋀[ℂ]^n (Vectors Y)

noncomputable def augmentation : Vectors Y →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun _ : Y => (1 : ℂ))

noncomputable def boundary : Algebra Y →ₗ[ℂ] Algebra Y :=
  contraction (augmentation Y)

@[simp] lemma augmentation_single (y : Y) (c : ℂ) :
    augmentation Y (Finsupp.single y c) = c := by
  simp [augmentation]

lemma boundary_square (x : Algebra Y) : boundary Y (boundary Y x) = 0 :=
  contraction_square _ x

lemma vertex_contraction (y : Y) (x : Algebra Y) :
    boundary Y (ExteriorAlgebra.ι ℂ (Finsupp.single y 1) * x) +
      ExteriorAlgebra.ι ℂ (Finsupp.single y 1) * boundary Y x = x :=
  cone_contraction _ (augmentation_single Y y 1) x

lemma exists_filler [Nonempty Y] (n : ℕ) {x : Algebra Y} (hx : x ∈ Degree Y n)
    (hcycle : boundary Y x = 0) :
    ∃ z ∈ Degree Y (n+1), boundary Y z = x := by
  classical
  let y : Y := Classical.choice inferInstance
  refine ⟨ExteriorAlgebra.ι ℂ (Finsupp.single y 1) * x, ?_, ?_⟩
  · change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨_, rfl⟩) hx
  · have h := vertex_contraction Y y x
    simpa only [hcycle, mul_zero, add_zero] using h

end Chains

/-! Alternating functions on vertex labels extend to genuine linear maps on exterior chains. -/

namespace Oriented

open scoped BigOperators

variable {Y A : Type*} [AddCommGroup A] [Module ℂ A]

abbrev Degree (Y : Type*) (n : ℕ) := ⋀[ℂ]^n (Y →₀ ℂ)

def wedge (n : ℕ) (v : Fin n → Y) : Degree Y n :=
  exteriorPower.ιMulti ℂ n (fun i => Finsupp.single (v i) 1)

lemma wedge_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    wedge n (v ∘ σ) = Equiv.Perm.sign σ • wedge n v :=
  by simpa only [wedge, Function.comp_def] using
    (exteriorPower.ιMulti ℂ n).map_perm (fun i => Finsupp.single (v i) 1) σ

lemma wedge_eq_zero_of_not_injective (n : ℕ) {v : Fin n → Y}
    (hv : ¬ Function.Injective v) : wedge n v = 0 := by
  apply (exteriorPower.ιMulti ℂ n).map_eq_zero_of_not_injective
  intro h
  exact hv fun i j hij => h (by simpa only using congrArg (fun y => Finsupp.single y (1 : ℂ)) hij)

structure AltFunction (Y : Type*) (n : ℕ) (A : Type*) [AddCommGroup A] where
  toFun : (Fin n → Y) → A
  perm : ∀ v (σ : Equiv.Perm (Fin n)), toFun (v ∘ σ) = Equiv.Perm.sign σ • toFun v
  zero : ∀ v, ¬ Function.Injective v → toFun v = 0

instance {n : ℕ} : CoeFun (AltFunction Y n A) (fun _ => (Fin n → Y) → A) :=
  ⟨AltFunction.toFun⟩

variable [LinearOrder Y]

abbrev basis (n : ℕ) : Module.Basis (Set.powersetCard Y n) ℂ (Degree Y n) :=
  (Finsupp.basisSingleOne : Module.Basis Y ℂ (Y →₀ ℂ)).exteriorPower n

lemma basis_eq_wedge (n : ℕ) (s : Set.powersetCard Y n) :
    basis n s = wedge n (Set.powersetCard.ofFinEmbEquiv.symm s) := by
  rw [exteriorPower.basis_apply]
  rfl

lemma exists_sorted_perm {n : ℕ} (v : Fin n → Y) (hv : Function.Injective v) :
    ∃ (s : Set.powersetCard Y n) (σ : Equiv.Perm (Fin n)),
      v = (Set.powersetCard.ofFinEmbEquiv.symm s) ∘ σ := by
  classical
  let s : Set.powersetCard Y n :=
    ⟨Finset.univ.image v, by simpa using Finset.card_image_of_injective Finset.univ hv⟩
  let w : Fin n ↪o Y := Set.powersetCard.ofFinEmbEquiv.symm s
  have hs (i : Fin n) : v i ∈ s := by simp [s]
  have hw (i : Fin n) : ∃ j, w j = v i :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s (v i)).mpr (hs i)
  let f : Fin n → Fin n := fun i => (hw i).choose
  have hf (i : Fin n) : w (f i) = v i := (hw i).choose_spec
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hv
    rw [← hf i, ← hf j, hij]
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hfinj, rfl⟩)
  refine ⟨s, σ, ?_⟩
  funext i
  exact (hf i).symm

def AltFunction.lift {n : ℕ} (f : AltFunction Y n A) : Degree Y n →ₗ[ℂ] A :=
  (basis n).constr ℂ fun s => f (Set.powersetCard.ofFinEmbEquiv.symm s)

@[simp] lemma AltFunction.lift_wedge {n : ℕ} (f : AltFunction Y n A)
    (v : Fin n → Y) : f.lift (wedge n v) = f v := by
  classical
  by_cases hv : Function.Injective v
  · obtain ⟨s, σ, rfl⟩ := exists_sorted_perm v hv
    rw [wedge_perm, f.perm, ← basis_eq_wedge]
    simp only [Units.smul_def, map_zsmul, AltFunction.lift, Module.Basis.constr_basis]
  · rw [wedge_eq_zero_of_not_injective n hv, map_zero, f.zero v hv]

lemma linearMap_ext_wedge {n : ℕ} {f g : Degree Y n →ₗ[ℂ] A}
    (h : ∀ v, f (wedge n v) = g (wedge n v)) : f = g := by
  apply (basis n).ext
  intro s
  rw [basis_eq_wedge]
  exact h _

lemma span_wedges (n : ℕ) :
    Submodule.span ℂ (Set.range (wedge (Y := Y) n)) = ⊤ := by
  apply top_unique
  rw [← (basis n).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨s, rfl⟩
  exact ⟨_, (basis_eq_wedge n s).symm⟩

end Oriented

namespace ChainHomotopy

open scoped BigOperators

open Oriented

variable {Y : Type*}

def average (n : ℕ) (v : Fin n → Y) : Y →₀ ℂ :=
  (n : ℂ)⁻¹ • ∑ i, Finsupp.single (v i) 1

lemma average_perm (n : ℕ) (v : Fin n → Y) (σ : Equiv.Perm (Fin n)) :
    average n (v ∘ σ) = average n v := by
  unfold average
  congr 1
  exact Equiv.sum_comp σ (fun y => Finsupp.single (v y) (1 : ℂ))

lemma average_augmentation {n : ℕ} (hn : n ≠ 0) (v : Fin n → Y) :
    Chains.augmentation Y (average n v) = 1 := by
  simp [average, Nat.cast_ne_zero.mpr hn]

def cone (n : ℕ) (v : Y →₀ ℂ) : Degree Y n →ₗ[ℂ] Degree Y (n+1) where
  toFun x := ⟨ExteriorAlgebra.ι ℂ v * x, by
    change _ ∈ (ExteriorAlgebra.ι ℂ).range ^ (n+1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range.mpr ⟨v, rfl⟩) x.property⟩
  map_add' a b := by ext; exact mul_add _ _ _
  map_smul' a x := by ext; exact mul_smul_comm _ _ _

@[simp] lemma cone_coe (n : ℕ) (v : Y →₀ ℂ) (x : Degree Y n) :
    (cone n v x : Chains.Algebra Y) = ExteriorAlgebra.ι ℂ v * x := rfl

def d (n : ℕ) : Degree Y (n+1) →ₗ[ℂ] Degree Y n :=
  ((Chains.boundary Y).comp (Degree Y (n+1)).subtype).codRestrict _ fun x =>
    Chains.contraction_mem_exteriorPower (Chains.augmentation Y) n x.property

@[simp] lemma d_coe (n : ℕ) (x : Degree Y (n+1)) :
    (d n x : Chains.Algebra Y) = Chains.boundary Y x := rfl

lemma d_square (n : ℕ) (x : Degree Y (n+2)) : d n (d (n+1) x) = 0 := by
  ext
  exact Chains.boundary_square _ _

lemma d_cone_cycle (n : ℕ) (v : Y →₀ ℂ) (hv : Chains.augmentation Y v = 1)
    (x : Degree Y n) (hx : Chains.boundary Y x = 0) :
    d n (cone n v x) = x := by
  ext
  change Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) = _
  have he : Chains.boundary Y (ExteriorAlgebra.ι ℂ v * (x : Chains.Algebra Y)) +
      ExteriorAlgebra.ι ℂ v * Chains.boundary Y x = (x : Chains.Algebra Y) :=
    Chains.cone_contraction (Chains.augmentation Y) hv (x : Chains.Algebra Y)
  simpa only [hx, mul_zero, add_zero] using he

def coneFunction {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    AltFunction Y n (Degree Y (n+1)) where
  toFun v := cone n (average n v) (r (wedge n v))
  perm v σ := by
    rw [average_perm, wedge_perm]
    simp only [Units.smul_def, map_zsmul]
  zero v hv := by
    rw [wedge_eq_zero_of_not_injective n hv, map_zero, map_zero]

variable [LinearOrder Y]

def coneLift {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n) :
    Degree Y n →ₗ[ℂ] Degree Y (n+1) := (coneFunction r).lift

@[simp] lemma coneLift_wedge {n : ℕ} (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (v : Fin n → Y) :
    coneLift r (wedge n v) = cone n (average n v) (r (wedge n v)) :=
  (coneFunction r).lift_wedge v

lemma d_coneLift {n : ℕ} (hn : n ≠ 0) (r : Degree Y n →ₗ[ℂ] Degree Y n)
    (hr : ∀ x, Chains.boundary Y (r x : Chains.Algebra Y) = 0) :
    (d n).comp (coneLift r) = r := by
  apply linearMap_ext_wedge
  intro v
  simp only [LinearMap.comp_apply, coneLift_wedge]
  exact d_cone_cycle n _ (average_augmentation hn v) _ (hr _)

/- The explicit augmented deletion boundary on labelled simplices. -/

omit [LinearOrder Y] in
lemma d_wedge (n : ℕ) (v : Fin (n+1) → Y) :
    d n (wedge (n+1) v) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • wedge n (fun j => v (i.succAbove j)) := by
  apply Subtype.ext
  change Chains.boundary Y (ExteriorAlgebra.ιMulti ℂ (n+1)
      (fun i => Finsupp.single (v i) 1)) = _
  rw [Chains.boundary, Chains.contraction_ιMulti]
  simp only [Chains.augmentation_single, mul_one, Submodule.coe_sum,
    Submodule.coe_smul, wedge, exteriorPower.ιMulti_apply_coe]

end ChainHomotopy

end BassTrace

end

end OAI
