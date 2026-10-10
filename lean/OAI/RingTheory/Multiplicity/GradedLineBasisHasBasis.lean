import Mathlib
import OAI.RingTheory.Multiplicity.LechFactorizationMap

namespace OAI

section
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal ZeroObject
open CategoryTheory
attribute [local instance] Classical.propDecidable
open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows
open HomologicalComplex HomologicalComplex.HomologySequence CategoryTheory.Abelian
open scoped BigOperators
open scoped Classical
namespace Lech.GradedLineBasis
open scoped TensorProduct
universe u v w z
variable {G : Type u} [AddCommGroup G]
variable {R : Type v} [CommRing R] {S : Type w} [CommRing S] [Algebra R S]
variable (M : G → Type z) [∀ g,AddCommGroup (M g)] [∀ g,Module R (M g)]
variable (val : ∀ g,M g →ₗ[R] S)
variable (mul : ∀ g h,M g ⊗[R] M h ≃ₗ[R] M (g+h))
variable (hmul : ∀ g h (x : M g) (y : M h),val (g+h) (mul g h (x ⊗ₜ[R] y))=val g x*val h y)
variable (unit : R ≃ₗ[R] M 0) (hunit : val 0 (unit 1)=1)
variable (u : G → Sˣ) (hu0 : u 0=1) (huadd : ∀ g h,u (g+h)=u g*u h)

def HasBasis (g : G) : Prop := ∃ e : R ≃ₗ[R] M g,val g (e 1)=(u g:S)

include hunit hu0 in
lemma zero : HasBasis M val u 0 := ⟨unit,by rw [hunit,hu0];rfl⟩

include hmul huadd in
lemma add {g h : G} (hg : HasBasis M val u g) (hh : HasBasis M val u h) :
    HasBasis M val u (g+h) := by
  obtain ⟨eg,heg⟩ := hg
  obtain ⟨eh,heh⟩ := hh
  refine ⟨(TensorProduct.lid R R).symm ≪≫ₗ TensorProduct.congr eg eh ≪≫ₗ mul g h,?_⟩
  change val (g+h) (mul g h (eg 1 ⊗ₜ[R] eh 1))=(u (g+h):S)
  rw [hmul,heg,heh,huadd,Units.val_mul]

def cast {g h : G} (e : g=h) : M g ≃ₗ[R] M h := by subst h;exact LinearEquiv.refl R _
omit [AddCommGroup G] in
lemma val_cast {g h : G} (e : g=h) (x : M g) : val h (cast (R := R) M e x)=val g x := by subst h;rfl

include hunit in
lemma val_unit (r : R) : val 0 (unit r)=algebraMap R S r := by
  have h := congrArg (val 0) (unit.map_smul r (1:R))
  rw [smul_eq_mul,mul_one,map_smul,hunit,Algebra.smul_def,mul_one] at h
  exact h

include hmul hunit hu0 huadd in
 

lemma neg {g : G} (hg : HasBasis M val u g) : HasBasis M val u (-g) := by
  obtain ⟨eg,heg⟩ := hg
  let pair : M g ⊗[R] M (-g) ≃ₗ[R] R :=
    mul g (-g) ≪≫ₗ cast (R := R) M (add_neg_cancel g) ≪≫ₗ unit.symm
  let e : M (-g) ≃ₗ[R] R :=
    (TensorProduct.lid R (M (-g))).symm ≪≫ₗ
      (TensorProduct.congr eg (LinearEquiv.refl R (M (-g)))) ≪≫ₗ pair
  refine ⟨e.symm,?_⟩
  have hp : pair (eg 1 ⊗ₜ[R] e.symm 1)=1 := e.apply_symm_apply 1
  have hv : val g (eg 1)*val (-g) (e.symm 1)=1 := by
    rw [←hmul]
    rw [←val_cast (R := R) M val (add_neg_cancel g)]
    have he : cast (R := R) M (add_neg_cancel g) (mul g (-g) (eg 1 ⊗ₜ[R] e.symm 1))=unit 1 := by
      apply unit.symm.injective
      exact hp.trans (unit.symm_apply_apply 1).symm
    rw [he,hunit]
  have hu : (u g:S)*(u (-g):S)=1 := by
    rw [←Units.val_mul,←huadd,add_neg_cancel,hu0,Units.val_one]
  rw [heg] at hv
  exact (u g).isUnit.mul_left_cancel (hv.trans hu.symm)

 
def subgroup : AddSubgroup G where
  carrier := HasBasis M val u
  zero_mem' := zero M val unit hunit u hu0
  add_mem' := add M val mul hmul u huadd
  neg_mem' := neg M val mul hmul unit hunit u hu0 huadd

 

lemma all_weights {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (ι → ℤ) → Type z) [∀ g,AddCommGroup (M g)] [∀ g,Module R (M g)]
    (val : ∀ g,M g →ₗ[R] S)
    (mul : ∀ g h,M g ⊗[R] M h ≃ₗ[R] M (g+h))
    (hmul : ∀ g h (x : M g) (y : M h),val (g+h) (mul g h (x ⊗ₜ[R] y))=val g x*val h y)
    (unit : R ≃ₗ[R] M 0) (hunit : val 0 (unit 1)=1)
    (u : (ι → ℤ) → Sˣ) (hu0 : u 0=1) (huadd : ∀ g h,u (g+h)=u g*u h)
    (hgen : ∀ i,HasBasis M val u (Pi.single i 1)) (g : ι → ℤ) : HasBasis M val u g := by
  let H := subgroup M val mul hmul unit hunit u hu0 huadd
  have h (i : ι) : g i • Pi.single i (1:ℤ) ∈ H := H.zsmul_mem (hgen i) (g i)
  have he : ∑ i : ι,g i • Pi.single i (1:ℤ)=g := by
    ext j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
    simp
  rw [←he]
  exact H.sum_mem (fun i _ => h i)
end Lech.GradedLineBasis


namespace Lech.TensorBilinearValues
open scoped TensorProduct
universe u v w x y z
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type x} [AddCommGroup N] [Module R N]
variable {U : Type y} [AddCommGroup U] [Module L U]
variable {S : Type z} [CommRing S] [Algebra L S]
lemma ext_mul
    (e : (L ⊗[R] M) ⊗[L] (L ⊗[R] N) →ₗ[L] U)
    (val : U →ₗ[L] S) (f : L ⊗[R] M →ₗ[L] S) (g : L ⊗[R] N →ₗ[L] S)
    (h : ∀ r s m n, val (e ((r ⊗ₜ[R] m) ⊗ₜ[L] (s ⊗ₜ[R] n)))=f (r ⊗ₜ[R] m)*g (s ⊗ₜ[R] n))
    (a : L ⊗[R] M) (b : L ⊗[R] N) : val (e (a ⊗ₜ[L] b))=f a*g b := by
  induction a using TensorProduct.inductionOn with
  | tmul r m =>
    induction b using TensorProduct.inductionOn with
    | tmul s n => exact h r s m n
    | add b c hb hc => simpa only [TensorProduct.tmul_add,map_add,mul_add] using congrArg₂ (·+·) hb hc
  | add a c ha hc => simpa only [TensorProduct.add_tmul,map_add,add_mul] using congrArg₂ (·+·) ha hc
lemma ext_mul_equiv
    (e : (L ⊗[R] M) ⊗[L] (L ⊗[R] N) ≃ₗ[L] U)
    (val : U →ₗ[L] S) (f : L ⊗[R] M →ₗ[L] S) (g : L ⊗[R] N →ₗ[L] S)
    (h : ∀ r s m n, val (e ((r ⊗ₜ[R] m) ⊗ₜ[L] (s ⊗ₜ[R] n)))=f (r ⊗ₜ[R] m)*g (s ⊗ₜ[R] n))
    (a : L ⊗[R] M) (b : L ⊗[R] N) : val (e (a ⊗ₜ[L] b))=f a*g b :=
  ext_mul e.toLinearMap val f g h a b
end Lech.TensorBilinearValues


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance gradedLineBasisAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance gradedLineBasisTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable (σ : Fin n → Bool)
abbrev chartExtension := chartRing f n hn t v hv d σ ⊗[algebra f n hn t v hv d] d.S

def chartValue (ms : Fin n → ℤ) : chartModule f n hn t v hv d σ ms →ₗ[chartRing f n hn t v hv d σ]
    chartExtension f n hn t v hv d σ :=
  (overAlgebra f n hn t v hv d ms).subtype.baseChange (chartRing f n hn t v hv d σ)
lemma chartValue_tmul (ms : Fin n → ℤ) (r : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) :
    chartValue f n hn t v hv d σ ms (r ⊗ₜ[algebra f n hn t v hv d] m)=
      r ⊗ₜ[algebra f n hn t v hv d] (m:d.S) := rfl

def zeroLineEquiv : algebra f n hn t v hv d ≃ₗ[algebra f n hn t v hv d]
    overAlgebra f n hn t v hv d (0:Fin n → ℤ) where
  toFun x := ⟨(x:d.S),by
    change (RootCoaction.weight f n hn t v hv d 0:RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S)
    rw [weight_zero,Units.val_one,one_mul]
    exact x.property⟩
  invFun x := ⟨(x:d.S),by
    have h := x.property
    change (RootCoaction.weight f n hn t v hv d 0:RootCoaction.T f n t v d)*
      RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S) at h
    change RootCoaction.hom f n hn t v hv d (x:d.S)=RootCoaction.right f n t v d (x:d.S)
    simpa only [weight_zero,Units.val_one,one_mul] using h⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def chartZeroEquiv : chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ]
    chartModule f n hn t v hv d σ (0:Fin n → ℤ) :=
  (TensorProduct.AlgebraTensorModule.rid (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ) (chartRing f n hn t v hv d σ)).symm ≪≫ₗ
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (chartRing f n hn t v hv d σ) _)
      (zeroLineEquiv f n hn t v hv d)
lemma chartZero_value : chartValue f n hn t v hv d σ 0 (chartZeroEquiv f n hn t v hv d σ 1)=1 := by
  change (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] (1:d.S)=1
  rfl

variable [Module.FaithfullyFlat A B]
def chartMul (ms ns : Fin n → ℤ) :
    chartModule f n hn t v hv d σ ms ⊗[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ ns
      ≃ₗ[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ (ms+ns) :=
  (TensorProduct.AlgebraTensorModule.distribBaseChange (algebra f n hn t v hv d)
    (chartRing f n hn t v hv d σ) (overAlgebra f n hn t v hv d ms) (overAlgebra f n hn t v hv d ns)).symm ≪≫ₗ
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (chartRing f n hn t v hv d σ) _)
        (lineMulEquiv f n hn t v hv d ms ns)
lemma chartMul_tmul (ms ns : Fin n → ℤ) (r s : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) (p : overAlgebra f n hn t v hv d ns) :
    chartMul f n hn t v hv d σ ms ns
      ((r ⊗ₜ[algebra f n hn t v hv d] m) ⊗ₜ[chartRing f n hn t v hv d σ]
        (s ⊗ₜ[algebra f n hn t v hv d] p))=
      (r*s) ⊗ₜ[algebra f n hn t v hv d] (mulLinear f n hn t v hv d ms ns m p) := by
  simp only [chartMul,LinearEquiv.trans_apply,TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply]
  rfl
lemma chartValue_mul_tmul (ms ns : Fin n → ℤ) (r s : chartRing f n hn t v hv d σ)
    (m : overAlgebra f n hn t v hv d ms) (p : overAlgebra f n hn t v hv d ns) :
    chartValue f n hn t v hv d σ (ms+ns)
      (chartMul f n hn t v hv d σ ms ns ((r ⊗ₜ[algebra f n hn t v hv d] m) ⊗ₜ[chartRing f n hn t v hv d σ]
        (s ⊗ₜ[algebra f n hn t v hv d] p)))=
      chartValue f n hn t v hv d σ ms (r ⊗ₜ[algebra f n hn t v hv d] m)*
        chartValue f n hn t v hv d σ ns (s ⊗ₜ[algebra f n hn t v hv d] p) := by
  rw [chartMul_tmul,chartValue_tmul,chartValue_tmul,chartValue_tmul]
  exact (Algebra.TensorProduct.tmul_mul_tmul r s (m:d.S) (p:d.S)).symm
lemma chartValue_mul (ms ns : Fin n → ℤ) (x : chartModule f n hn t v hv d σ ms)
    (y : chartModule f n hn t v hv d σ ns) :
    chartValue f n hn t v hv d σ (ms+ns)
      (chartMul f n hn t v hv d σ ms ns (x ⊗ₜ[chartRing f n hn t v hv d σ] y))=
      chartValue f n hn t v hv d σ ms x*chartValue f n hn t v hv d σ ns y := by
  let : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  induction x using TensorProduct.inductionOn with
  | tmul scalarLeft elementLeft =>
    induction y using TensorProduct.inductionOn with
    | tmul scalarRight elementRight =>
      exact chartValue_mul_tmul f n hn t v hv d σ ms ns
        scalarLeft scalarRight elementLeft elementRight
    | add first second hfirst hsecond =>
      simp only [TensorProduct.tmul_add,map_add]
      exact (congrArg₂ (·+·) hfirst hsecond).trans (mul_add _ _ _).symm
  | add first second hfirst hsecond =>
    simp only [TensorProduct.add_tmul,map_add]
    exact (congrArg₂ (·+·) hfirst hsecond).trans (add_mul _ _ _).symm

omit [Module.FaithfullyFlat A B] in
def chartSelectedUnit (i : Fin n) : (chartExtension f n hn t v hv d σ)ˣ :=
  (selected_tensor_unit f n hn t v hv d σ i).unit
omit [Module.FaithfullyFlat A B] in
lemma chartSelectedUnit_val (i : Fin n) : (chartSelectedUnit f n hn t v hv d σ i: chartExtension f n hn t v hv d σ)=
    (1:chartRing f n hn t v hv d σ) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S) :=
  (selected_tensor_unit f n hn t v hv d σ i).unit_spec

def chartWeight (ms : Fin n → ℤ) : (chartExtension f n hn t v hv d σ)ˣ := by
  letI : CommRing (chartExtension f n hn t v hv d σ) := Algebra.TensorProduct.instCommRing
  exact ∏ i : Fin n,(chartSelectedUnit f n hn t v hv d σ i)^ms i
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_zero : chartWeight f n hn t v hv d σ (0:Fin n → ℤ)=1 := by
  simp only [chartWeight,Pi.zero_apply,zpow_zero,Finset.prod_const_one]
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_add (ms ns : Fin n → ℤ) : chartWeight f n hn t v hv d σ (ms+ns)=
    chartWeight f n hn t v hv d σ ms*chartWeight f n hn t v hv d σ ns := by
  simp only [chartWeight,Pi.add_apply,zpow_add,Finset.prod_mul_distrib]
omit [Module.FaithfullyFlat A B] in
lemma chartWeight_single (i : Fin n) : chartWeight f n hn t v hv d σ (Pi.single i (1:ℤ))=
    chartSelectedUnit f n hn t v hv d σ i := by
  classical
  simp [chartWeight,Pi.single_apply]

 

lemma chart_all_weights (ms : Fin n → ℤ) :
    GradedLineBasis.HasBasis (R := chartRing f n hn t v hv d σ)
      (S := chartExtension f n hn t v hv d σ) (chartModule f n hn t v hv d σ)
      (chartValue f n hn t v hv d σ) (chartWeight f n hn t v hv d σ) ms := by
  apply GradedLineBasis.all_weights _ _ (chartMul f n hn t v hv d σ)
    (chartValue_mul f n hn t v hv d σ) (chartZeroEquiv f n hn t v hv d σ)
    (chartZero_value f n hn t v hv d σ) _ (chartWeight_zero f n hn t v hv d σ)
    (chartWeight_add f n hn t v hv d σ)
  intro i
  refine ⟨chartLineEquiv f n hn t v hv d σ i,?_⟩
  rw [chartWeight_single,chartSelectedUnit_val,chartLineEquiv_apply,chartValue_tmul]

end Lech.RootInvariants


namespace Lech.LineBasisExtension
open scoped TensorProduct
universe u v w x y
variable {R : Type u} [CommRing R] {L : Type v} [CommRing L] [Algebra R L]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable (C : Type x) [CommRing C] [Algebra R C] [Algebra L C] [IsScalarTower R L C]
variable {S : Type y} [CommRing S] [Algebra R S]
 
def extend (e : L ≃ₗ[L] L ⊗[R] M) : C ≃ₗ[C] C ⊗[R] M :=
  (TensorProduct.AlgebraTensorModule.rid L C C).symm ≪≫ₗ TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M

 

def coefficients : L ⊗[R] S →ₐ[R] C ⊗[R] S :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R L C) (AlgHom.id R S)
lemma coefficients_tmul (l : L) (s : S) : coefficients (R := R) (L := L) C (l ⊗ₜ[R] s)=
    algebraMap L C l ⊗ₜ[R] s := rfl

lemma value_extend (f : M →ₗ[R] S) (e : L ≃ₗ[L] L ⊗[R] M) :
    f.baseChange C (extend C e 1)=coefficients C (f.baseChange L (e 1)) := by
  change f.baseChange C (TensorProduct.AlgebraTensorModule.cancelBaseChange R L C C M (1 ⊗ₜ[L] e 1))=_
  generalize e 1=z
  induction z using TensorProduct.inductionOn with
  | tmul l m =>
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,LinearMap.baseChange_tmul,
      coefficients_tmul,Algebra.smul_def,mul_one]
  | add z w hz hw => simpa only [TensorProduct.tmul_add,map_add] using congrArg₂ (·+·) hz hw

variable {N : Type w} [AddCommGroup N] [Module L N]
def transition (e f : L ≃ₗ[L] N) : Lˣ where
  val := e.symm (f 1)
  inv := f.symm (e 1)
  val_inv := by
    have he (r : L) : e r=r • e 1 := by simpa only [smul_eq_mul,mul_one] using e.map_smul r 1
    have hf (r : L) : f r=r • f 1 := by simpa only [smul_eq_mul,mul_one] using f.map_smul r 1
    apply e.injective
    rw [mul_comm,he,mul_smul,←he, e.apply_symm_apply,←hf,f.apply_symm_apply]
  inv_val := by
    have he (r : L) : e r=r • e 1 := by simpa only [smul_eq_mul,mul_one] using e.map_smul r 1
    have hf (r : L) : f r=r • f 1 := by simpa only [smul_eq_mul,mul_one] using f.map_smul r 1
    apply f.injective
    rw [mul_comm,hf,mul_smul,←hf,f.apply_symm_apply,←he,e.apply_symm_apply]
lemma transition_apply (e f : L ≃ₗ[L] N) (r : L) :
    e (r*(transition e f:L))=f r := by
  change e (r*e.symm (f 1))=f r
  rw [←smul_eq_mul,e.map_smul,e.apply_symm_apply,←f.map_smul,smul_eq_mul,mul_one]
lemma transition_self (e : L ≃ₗ[L] N) : transition e e=1 := by
  apply Units.ext
  exact e.symm_apply_apply 1
lemma transition_cocycle (e f g : L ≃ₗ[L] N) : transition e f*transition f g=transition e g := by
  apply Units.ext
  apply e.injective
  change e ((transition e f:L)*(transition f g:L))=e (e.symm (g 1))
  rw [mul_comm,transition_apply]
  change f (f.symm (g 1))=e (e.symm (g 1))
  rw [f.apply_symm_apply,e.apply_symm_apply]
end Lech.LineBasisExtension


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance transitionWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance transitionWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]

def chartBasis (σ : Fin n → Bool) (ms : Fin n → ℤ) :
    chartRing f n hn t v hv d σ ≃ₗ[chartRing f n hn t v hv d σ] chartModule f n hn t v hv d σ ms :=
  (chart_all_weights f n hn t v hv d σ ms).choose
lemma chartBasis_value (σ : Fin n → Bool) (ms : Fin n → ℤ) :
    chartValue f n hn t v hv d σ ms (chartBasis f n hn t v hv d σ ms 1)=
      (chartWeight f n hn t v hv d σ ms:chartExtension f n hn t v hv d σ) :=
  (chart_all_weights f n hn t v hv d σ ms).choose_spec

variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
abbrev commonModule (ms : Fin n → ℤ) := C ⊗[algebra f n hn t v hv d] overAlgebra f n hn t v hv d ms
abbrev commonExtension := C ⊗[algebra f n hn t v hv d] d.S

def commonBasis (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    C ≃ₗ[C] commonModule f n hn t v hv d C ms := by
  letI : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  letI : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq
      (R := algebra f n hn t v hv d) (S := chartRing f n hn t v hv d σ) (A := C)
      fun a => (φ.commutes a).symm
  exact LineBasisExtension.extend C (chartBasis f n hn t v hv d σ ms)

def commonCoefficients (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) :
    chartExtension f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
  Algebra.TensorProduct.map φ (AlgHom.id _ _)
def commonWeight (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    (commonExtension f n hn t v hv d C)ˣ :=
  Units.map (commonCoefficients f n hn t v hv d C σ φ).toMonoidHom (chartWeight f n hn t v hv d σ ms)
def commonValue (ms : Fin n → ℤ) : commonModule f n hn t v hv d C ms →ₗ[C] commonExtension f n hn t v hv d C :=
  (overAlgebra f n hn t v hv d ms).subtype.baseChange C
lemma commonBasis_value (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms 1)=
      (commonWeight f n hn t v hv d C σ φ ms:commonExtension f n hn t v hv d C) := by
  let : Algebra (chartRing f n hn t v hv d σ) C := φ.toRingHom.toAlgebra
  let : IsScalarTower (algebra f n hn t v hv d) (chartRing f n hn t v hv d σ) C :=
    IsScalarTower.of_algebraMap_eq
      (R := algebra f n hn t v hv d) (S := chartRing f n hn t v hv d σ) (A := C)
      fun a => (φ.commutes a).symm
  have h := LineBasisExtension.value_extend C (overAlgebra f n hn t v hv d ms).subtype
    (chartBasis f n hn t v hv d σ ms)
  change commonValue f n hn t v hv d C ms (commonBasis f n hn t v hv d C σ φ ms 1)=
    commonCoefficients f n hn t v hv d C σ φ (chartValue f n hn t v hv d σ ms (chartBasis f n hn t v hv d σ ms 1)) at h
  rw [chartBasis_value] at h
  exact h

 

def chartTransition (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) : Cˣ :=
  LineBasisExtension.transition (commonBasis f n hn t v hv d C τ ψ ms)
    (commonBasis f n hn t v hv d C σ φ ms)
lemma chartTransition_value (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    algebraMap C (commonExtension f n hn t v hv d C) (chartTransition f n hn t v hv d C σ τ φ ψ ms:C)*
      (commonWeight f n hn t v hv d C τ ψ ms:commonExtension f n hn t v hv d C)=
        (commonWeight f n hn t v hv d C σ φ ms:commonExtension f n hn t v hv d C) := by
  have h := LineBasisExtension.transition_apply (commonBasis f n hn t v hv d C τ ψ ms)
    (commonBasis f n hn t v hv d C σ φ ms) (1:C)
  rw [one_mul] at h
  have hh := congrArg (commonValue f n hn t v hv d C ms) h
  have he (r : C) : commonBasis f n hn t v hv d C τ ψ ms r=
    r • commonBasis f n hn t v hv d C τ ψ ms 1 := by
    simpa only [smul_eq_mul,mul_one] using (commonBasis f n hn t v hv d C τ ψ ms).map_smul r 1
  rw [he,(commonValue f n hn t v hv d C ms).map_smul,commonBasis_value,commonBasis_value] at hh
  rw [Algebra.smul_def (R := C) (A := commonExtension f n hn t v hv d C)] at hh
  exact hh

lemma chartTransition_cocycle (σ τ υ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C)
    (χ : chartRing f n hn t v hv d υ →ₐ[algebra f n hn t v hv d] C) (ms : Fin n → ℤ) :
    chartTransition f n hn t v hv d C τ υ ψ χ ms*chartTransition f n hn t v hv d C σ τ φ ψ ms=
      chartTransition f n hn t v hv d C σ υ φ χ ms :=
  LineBasisExtension.transition_cocycle _ _ _
end Lech.RootInvariants


namespace Lech.RootInvariants
open Polynomial
open scoped TensorProduct
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
local instance coordinateWorkAlgebra : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
local instance coordinateWorkTower : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
omit [Module.FaithfullyFlat A B] in
lemma commonWeight_single (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ)):commonExtension f n hn t v hv d C)=
      (1:C) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S) := by
  change commonCoefficients f n hn t v hv d C σ φ
    (chartWeight f n hn t v hv d σ (Pi.single i 1):chartExtension f n hn t v hv d σ)=_
  rw [chartWeight_single,chartSelectedUnit_val]
  exact (Algebra.TensorProduct.map_tmul φ (AlgHom.id _ _) _ _).trans (by rw [map_one];rfl)
lemma commonCoordinate_relation (σ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) (b : Bool) :
    algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i b))*
      (commonWeight f n hn t v hv d C σ φ (Pi.single i (1:ℤ)):commonExtension f n hn t v hv d C)=
        (1:C) ⊗ₜ[algebra f n hn t v hv d]
          ((if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i):d.S) := by
  have h := congrArg (chartValue f n hn t v hv d σ (Pi.single i (1:ℤ)))
    (chart_section_relation f n hn t v hv d σ i b)
  rw [chartLineEquiv_apply,chartValue_tmul,chartValue_tmul] at h
  have hh := congrArg (commonCoefficients f n hn t v hv d C σ φ) h
  simp only [commonCoefficients,Algebra.TensorProduct.map_tmul,map_one,AlgHom.id_apply] at hh
  rw [commonWeight_single]
  change (φ (chartCoordinate f n hn t v hv d σ i b) ⊗ₜ[algebra f n hn t v hv d] (1:d.S))*
    ((1:C) ⊗ₜ[algebra f n hn t v hv d] (selected f n hn t v hv d σ i:d.S))=_
  rw [Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]
  simpa only [apply_ite] using hh
lemma chartTransition_single (σ τ : Fin n → Bool)
    (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)
    (ψ : chartRing f n hn t v hv d τ →ₐ[algebra f n hn t v hv d] C) (i : Fin n) :
    (chartTransition f n hn t v hv d C σ τ φ ψ (Pi.single i (1:ℤ)):C)=
      ψ (chartCoordinate f n hn t v hv d τ i (σ i)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  apply hinj
  apply (commonWeight f n hn t v hv d C τ ψ (Pi.single i (1:ℤ))).mul_left_inj.mp
  rw [chartTransition_value,commonCoordinate_relation,commonWeight_single]
  cases hs : σ i <;> simp only [selected,hs,Bool.false_eq_true,↓reduceIte]
end Lech.RootInvariants
end
end

end OAI
