import Mathlib
import OAI.RingTheory.Multiplicity.RootHomogeneousCoordinates

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.SplitPair
universe u v
variable (B : Type u) [CommRing B] {S : Type v} [CommRing S] [Algebra B S]

def left (x y : S) : S →ₗ[B] S × S where
  toFun c := (y*c,-(x*c))
  map_add' a b := by
    change (y*(a+b),-(x*(a+b)))=(y*a+y*b,-(x*a)+(-(x*b)))
    apply Prod.ext <;> dsimp only <;> ring
  map_smul' b c := by
    change (y*(b • c),-(x*(b • c)))=(b • (y*c),b • (-(x*c)))
    apply Prod.ext <;> dsimp only <;> simp only [Algebra.smul_def] <;> ring

def right (x y : S) : S × S →ₗ[B] S where
  toFun c := x*c.1+y*c.2
  map_add' a b := by simp only [Prod.fst_add,Prod.snd_add]; ring
  map_smul' b c := by
    change x*(b • c.1)+y*(b • c.2)=b • (x*c.1+y*c.2)
    simp only [Algebra.smul_def]
    ring

lemma left_injective (x y t : S) (h : y+t*x=1) : Function.Injective (left B x y) := by
  intro a b he
  have hy : y*a=y*b := congrArg Prod.fst he
  have hx : x*a=x*b := neg_injective (congrArg Prod.snd he)
  calc
    a = (y+t*x)*a := by rw [h,one_mul]
    _ = y*b+t*(x*b) := by rw [add_mul,mul_assoc,hy,hx]
    _ = b := by rw [←mul_assoc,←add_mul,h,one_mul]

lemma right_surjective (x y t : S) (h : y+t*x=1) : Function.Surjective (right B x y) := by
  intro c
  refine ⟨(t*c,c),?_⟩
  change x*(t*c)+y*c=c
  calc
    _ = (y+t*x)*c := by ring
    _ = c := by rw [h,one_mul]

lemma exact (x y t : S) (h : y+t*x=1) : Function.Exact (left B x y) (right B x y) := by
  intro c
  constructor
  · intro hc
    change x*c.1+y*c.2=0 at hc
    refine ⟨c.1-t*c.2,?_⟩
    apply Prod.ext
    · change y*(c.1-t*c.2)=c.1
      calc
        _ = (y+t*x)*c.1-t*(x*c.1+y*c.2) := by ring
        _ = c.1 := by rw [h,hc,one_mul,mul_zero,sub_zero]
    · change -(x*(c.1-t*c.2))=c.2
      calc
        _ = (y+t*x)*c.2-(x*c.1+y*c.2) := by ring
        _ = c.2 := by rw [h,hc,one_mul,sub_zero]
  · rintro ⟨a,rfl⟩
    change x*(y*a)+y*(-(x*a))=0
    ring
end Lech.SplitPair

namespace Lech.RootInvariants
open Polynomial
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
private local instance lineEulerInstance1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
private local instance lineEulerInstance2 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

 
def coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    module f n hn t v hv d m →ₗ[A] module f n hn t v hv d (Pi.single i 1+m) :=
  (overAlgebraEquiv f n hn t v hv d _).toLinearMap.comp
    (((mulLinear f n hn t v hv d (Pi.single i 1) m
      (if b then sectionX f n hn t v hv d i else sectionY f n hn t v hv d i)).restrictScalars A).comp
      (overAlgebraEquiv f n hn t v hv d m).symm.toLinearMap)

lemma coordinateMul_val (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (a : module f n hn t v hv d m) :
    (coordinateMul f n hn t v hv d m i b a : d.S)=
      (if b then -d.roots i else 1+algebraMap B d.S t*d.roots i)*(a:d.S) := by
  cases b <;> rfl

def eulerLeft (m : Fin n → ℤ) (i : Fin n) :
    module f n hn t v hv d m →ₗ[A]
      module f n hn t v hv d (Pi.single i 1+m) × module f n hn t v hv d (Pi.single i 1+m) :=
  (coordinateMul f n hn t v hv d m i false).prod (-coordinateMul f n hn t v hv d m i true)

def eulerRight (m : Fin n → ℤ) (i : Fin n) :
    module f n hn t v hv d (Pi.single i 1+m) × module f n hn t v hv d (Pi.single i 1+m) →ₗ[A]
      module f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul f n hn t v hv d (Pi.single i 1+m) i true).coprod
    (coordinateMul f n hn t v hv d (Pi.single i 1+m) i false)

variable [Module.FaithfullyFlat A B]

def eulerMiddleEquiv (m : Fin n → ℤ) :
    B ⊗[A] (module f n hn t v hv d m × module f n hn t v hv d m) ≃ₗ[B] d.S × d.S :=
  TensorProduct.prodRight A B B _ _ ≪≫ₗ
    (tensorEquiv f n hn t v hv d m).prodCongr (tensorEquiv f n hn t v hv d m)

lemma tensorEquiv_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (a : B ⊗[A] module f n hn t v hv d m) :
    tensorEquiv f n hn t v hv d (Pi.single i 1+m)
      ((coordinateMul f n hn t v hv d m i b).baseChange B a)=
        (if b then -d.roots i else 1+algebraMap B d.S t*d.roots i)*
          tensorEquiv f n hn t v hv d m a := by
  induction a using TensorProduct.inductionOn with
  | tmul a x =>
      rw [LinearMap.baseChange_tmul]
      change a • (coordinateMul f n hn t v hv d m i b x : d.S)=_
      rw [coordinateMul_val]
      change a • (_ * (x:d.S))=_ * (a • (x:d.S))
      simp only [Algebra.smul_def]
      ring
  | add a c ha hc => simp only [map_add,ha,hc,mul_add]

lemma eulerLeft_base_compat (m : Fin n → ℤ) (i : Fin n) :
    (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap.comp
      ((eulerLeft f n hn t v hv d m i).baseChange B)=
      (SplitPair.left B (-d.roots i) (1+algebraMap B d.S t*d.roots i)).comp
        (tensorEquiv f n hn t v hv d m).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  change (b • (coordinateMul f n hn t v hv d m i false x:d.S),
    b • (-(coordinateMul f n hn t v hv d m i true x:d.S)))=_
  simp only [coordinateMul_val,Bool.false_eq_true,↓reduceIte,Algebra.smul_def,
    SplitPair.left,LinearMap.comp_apply]
  change (algebraMap B d.S b*((1+algebraMap B d.S t*d.roots i)*(x:d.S)),
    algebraMap B d.S b*(-(-d.roots i*(x:d.S))))=
    ((1+algebraMap B d.S t*d.roots i)*(b • (x:d.S)),-(-d.roots i*(b • (x:d.S))))
  apply Prod.ext <;> simp only [Algebra.smul_def] <;> ring

lemma eulerRight_base_compat (m : Fin n → ℤ) (i : Fin n) :
    (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m))).toLinearMap.comp
      ((eulerRight f n hn t v hv d m i).baseChange B)=
      (SplitPair.right B (-d.roots i) (1+algebraMap B d.S t*d.roots i)).comp
        (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b x
  change b • ((coordinateMul f n hn t v hv d (Pi.single i 1+m) i true x.1:d.S)+
    (coordinateMul f n hn t v hv d (Pi.single i 1+m) i false x.2:d.S))=_
  simp only [coordinateMul_val,Bool.false_eq_true,↓reduceIte]
  change b • ((-d.roots i)*(x.1:d.S)+(1+algebraMap B d.S t*d.roots i)*(x.2:d.S))=
    (-d.roots i)*(b • (x.1:d.S))+(1+algebraMap B d.S t*d.roots i)*(b • (x.2:d.S))
  simp only [Algebra.smul_def]
  ring
lemma eulerLeft_injective (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective A B _).mp
  have h : Function.Injective ((eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).toLinearMap.comp
      ((eulerLeft f n hn t v hv d m i).baseChange B)) := by
    rw [eulerLeft_base_compat]
    exact (SplitPair.left_injective B (-d.roots i) (1+algebraMap B d.S t*d.roots i)
      (algebraMap B d.S t) (by ring)).comp (tensorEquiv f n hn t v hv d m).injective
  intro a b hab
  exact h (congrArg (eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)) hab)

lemma eulerRight_surjective (m : Fin n → ℤ) (i : Fin n) :
    Function.Surjective (eulerRight f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B _).mp
  intro y
  obtain ⟨x,hx⟩ := SplitPair.right_surjective B (-d.roots i) (1+algebraMap B d.S t*d.roots i)
    (algebraMap B d.S t) (by ring)
    (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)) y)
  refine ⟨(eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).symm x,?_⟩
  apply (tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m))).injective
  have he := DFunLike.congr_fun (eulerRight_base_compat f n hn t v hv d m i)
    ((eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m)).symm x)
  simp only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] at he
  exact he.trans hx

 

lemma euler_exact (m : Fin n → ℤ) (i : Fin n) :
    Function.Exact (eulerLeft f n hn t v hv d m i) (eulerRight f n hn t v hv d m i) := by
  apply (Module.FaithfullyFlat.lTensor_exact_iff_exact A B _ _).mp
  change Function.Exact ((eulerLeft f n hn t v hv d m i).baseChange B)
    ((eulerRight f n hn t v hv d m i).baseChange B)
  exact (Function.Exact.iff_of_ladder_linearEquiv
    (e₁ := tensorEquiv f n hn t v hv d m)
    (e₂ := eulerMiddleEquiv f n hn t v hv d (Pi.single i 1+m))
    (e₃ := tensorEquiv f n hn t v hv d (Pi.single i 1+(Pi.single i 1+m)))
    (eulerLeft_base_compat f n hn t v hv d m i).symm
    (eulerRight_base_compat f n hn t v hv d m i).symm).mp
      (SplitPair.exact B (-d.roots i) (1+algebraMap B d.S t*d.roots i) (algebraMap B d.S t) (by ring))
end Lech.RootInvariants

end

end OAI
