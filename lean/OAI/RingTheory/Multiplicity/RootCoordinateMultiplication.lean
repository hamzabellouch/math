import Mathlib
import OAI.RingTheory.Multiplicity.RootChartAtlasGlobalCoefficient
import OAI.RingTheory.Multiplicity.RootLineEuler

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.RootInvariants
open Polynomial
universe u
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (f : A[X]) (n : ℕ) (hn : f.natDegree≤n) (t : B) (v : Bˣ)
  (hv : (f.map (algebraMap A B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized (f.map (algebraMap A B)) n t v))
private local instance coordinateInstance1 : Algebra A d.S := Algebra.compHom d.S (algebraMap A B)
private local instance coordinateInstance2 : IsScalarTower A B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat A B]
variable (C : Type u) [CommRing C] [Algebra (algebra f n hn t v hv d) C]
  (σ : Fin n → Bool) (φ : chartRing f n hn t v hv d σ →ₐ[algebra f n hn t v hv d] C)

omit [Module.FaithfullyFlat A B] in
lemma commonWeight_add (m l : Fin n → ℤ) :
    commonWeight f n hn t v hv d C σ φ (m+l)=
      commonWeight f n hn t v hv d C σ φ m*commonWeight f n hn t v hv d C σ φ l := by
  simp only [commonWeight,chartWeight_add,map_mul]

lemma commonBasis_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : module f n hn t v hv d m) :
    (commonBasis f n hn t v hv d C σ φ (Pi.single i 1+m)).symm
      (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d _).symm
        (coordinateMul f n hn t v hv d m i b x)))=
      φ (chartCoordinate f n hn t v hv d σ i b)*
        (commonBasis f n hn t v hv d C σ φ m).symm
          (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d m).symm x)) := by
  let := algebra_faithfullyFlat f n hn t v hv d
  let inc : d.S →ₐ[algebra f n hn t v hv d] commonExtension f n hn t v hv d C :=
    Algebra.TensorProduct.includeRight
  have hinj : Function.Injective (algebraMap C (commonExtension f n hn t v hv d C)) :=
    FaithfulSMul.algebraMap_injective C (commonExtension f n hn t v hv d C)
  have hx : inc (x:d.S)=
      algebraMap C (commonExtension f n hn t v hv d C)
        ((commonBasis f n hn t v hv d C σ φ m).symm
          (1 ⊗ₜ[algebra f n hn t v hv d] ((overAlgebraEquiv f n hn t v hv d m).symm x)))*
        (commonWeight f n hn t v hv d C σ φ m:commonExtension f n hn t v hv d C) := by
    rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
    rfl
  apply hinj
  apply (commonWeight f n hn t v hv d C σ φ (Pi.single i 1+m)).mul_left_inj.mp
  rw [←commonBasis_value_apply,LinearEquiv.apply_symm_apply]
  change inc (coordinateMul f n hn t v hv d m i b x:d.S)=_
  rw [coordinateMul_val,map_mul,hx]
  have hc := commonCoordinate_relation f n hn t v hv d C σ φ i b
  change algebraMap C (commonExtension f n hn t v hv d C) (φ (chartCoordinate f n hn t v hv d σ i b))*
    (commonWeight f n hn t v hv d C σ φ (Pi.single i 1):commonExtension f n hn t v hv d C)=
      inc (if b then -d.roots i else 1+algebraMap B d.S t*d.roots i) at hc
  rw [←hc,map_mul,commonWeight_add,Units.val_mul]
  ring
end Lech.RootInvariants

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
private local instance coordinateInstance3 : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
private local instance coordinateInstance4 : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
private local instance coordinateInstance5 : Algebra (A R n k) (GridAmbient R n) := gridTargetAlgebra R n k
private local instance coordinateInstance6 : Module (A R n k) (GridAmbient R n) := Algebra.toModule
variable [Module.FaithfullyFlat (A R n k) B]
private local instance coordinateInstance7 : Algebra (D R n k t v hv d) (GridAmbient R n) := gridRootAlgebra R n k t v hv d
private local instance coordinateInstance8 : IsScalarTower (A R n k) (D R n k t v hv d) (GridAmbient R n) :=
  IsScalarTower.of_algebraMap_eq fun a => ((algebraPoint R n k t v hv d (fun _ => false)).commutes a).symm
private local instance coordinateInstance9 (m : Fin n → ℤ) : Module (D R n k t v hv d)
    (RootInvariants.overAlgebra (f R n k) n (hn R n k) t v hv d m) := Submodule.module _

lemma globalCoefficientA_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : RootInvariants.module (f R n k) n (hn R n k) t v hv d m) :
    globalCoefficientA R n k t v hv d (Pi.single i 1+m)
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)=
      (if b then embed R n (ProductLaurent.variableUnit R n i:ProductLaurent.Ring R n) else 1)*
        globalCoefficientA R n k t v hv d m x := by
  change (RootInvariants.commonBasis (f R n k) n (hn R n k) t v hv d
      (GridAmbient R n) (fun _ => false) (chartToGridD R n k t v hv d (fun _ => false))
      (Pi.single i 1+m)).symm
      (1 ⊗ₜ[D R n k t v hv d]
        ((RootInvariants.overAlgebraEquiv (f R n k) n (hn R n k) t v hv d _).symm
          (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)))= _
  rw [RootInvariants.commonBasis_coordinateMul]
  congr 1
  change chartToGrid R n k t v hv d (fun _ => false)
    (coordinate R n k t v hv d (fun _ => false) i b)=_
  rw [chartToGrid_coordinate]
  cases b <;> simp only [Bool.false_eq_true,↓reduceIte,chartScalar,AlgHom.comp_apply,
    ProductLaurent.chartMap_a,ProductLaurent.chartMap_b,Units.val_one,one_mul,map_one]
end Lech.RootChartAtlas

end

end OAI
