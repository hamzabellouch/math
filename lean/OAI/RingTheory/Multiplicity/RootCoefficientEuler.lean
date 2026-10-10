import Mathlib
import OAI.RingTheory.Multiplicity.ExactSequenceTransport
import OAI.RingTheory.Multiplicity.RootCoordinateMultiplication
import OAI.RingTheory.Multiplicity.RootRestriction

namespace OAI

noncomputable section
open scoped TensorProduct
namespace Lech.ProductSourceCover
open AddMonoidAlgebra
universe u
variable (R : Type u) [CommRing R] (n : ℕ)

def rootCoordinate (i : Fin n) (b : Bool) : GridAmbient R n :=
  if b then embed R n (ProductLaurent.variableUnit R n i:ProductLaurent.Ring R n) else 1

lemma coordinate_ringSections (i : Fin n) (b : Bool) :
    (if b then (ProductLaurent.variableUnit R n i:Ambient R n) else 1)∈
      ringSections R n (Pi.single i 1) ∅ := by
  classical
  cases b
  · simp only [Bool.false_eq_true,ite_false]
    rw [one_def]
    apply single_mem
    rw [allowed_empty]
    intro j
    by_cases h : i=j <;> simp [h,eq_comm]
  · change single (Finsupp.single i 1) 1∈ringSections R n (Pi.single i 1) ∅
    apply single_mem
    rw [allowed_empty]
    intro j
    by_cases h : i=j <;> simp [h,eq_comm]

lemma rootCoordinate_mem (s : Finset (Fin (n+1))) (i : Fin n) (b : Bool) :
    rootCoordinate R n i b∈grid R n (Pi.single i 1) s ∅ := by
  refine ⟨0,(if b then (ProductLaurent.variableUnit R n i:Ambient R n) else 1),?_,?_⟩
  · have ht : levelTwist n (Pi.single i 1) s.card 0=Pi.single i 1 := by
      funext j
      simp only [levelTwist,Nat.cast_zero,zero_mul,add_zero]
    rw [ht]
    exact coordinate_ringSections R n i b
  · cases b <;> simp only [rootCoordinate,Bool.false_eq_true,↓reduceIte,pow_zero,one_mul,map_one]

 
def coordinateMul (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+m) where
  toFun x := ⟨rootCoordinate R n i b*x.val,
    grid_mul_mem R n (Pi.single i 1) m {k} ∅ _ _ (rootCoordinate_mem R n {k} i b) x.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change rootCoordinate R n i b*(gridTarget R n k a*x.val)=
      gridTarget R n k a*(rootCoordinate R n i b*x.val)
    ring)

def eulerLeft (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) :
    sectionModule R n k m →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m) :=
  (coordinateMul R n k m i false).prod (-coordinateMul R n k m i true)
def eulerRight (k : Fin (n+1)) (m : Fin n → ℤ) (i : Fin n) :
    sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m) →ₗ[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul R n k (Pi.single i 1+m) i true).coprod
    (coordinateMul R n k (Pi.single i 1+m) i false)
end Lech.ProductSourceCover

namespace Lech.RootChartAtlas
open Polynomial ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
variable {B : Type u} [CommRing B] [Algebra (A R n k) B]
variable (t : B) (v : Bˣ) (hv : ((f R n k).map (algebraMap (A R n k) B)).eval t=(v:B))
  (d : UniversalSplitting.Data B n (BinaryChange.normalized ((f R n k).map (algebraMap (A R n k) B)) n t v))
private local instance coefficientEulerInstance1 : Algebra (A R n k) d.S := Algebra.compHom d.S (algebraMap (A R n k) B)
private local instance coefficientEulerInstance2 : IsScalarTower (A R n k) B d.S := IsScalarTower.of_algebraMap_eq fun _ => rfl
variable [Module.FaithfullyFlat (A R n k) B]

lemma globalSection_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (x : RootInvariants.module (f R n k) n (hn R n k) t v hv d m) :
    globalSectionEquiv R n k t v hv d (Pi.single i 1+m)
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i b x)=
      coordinateMul R n k m i b (globalSectionEquiv R n k t v hv d m x) := by
  apply Subtype.ext
  exact globalCoefficientA_coordinateMul R n k t v hv d m i b x

include t v hv d in
lemma section_euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n k m i) ∧ Function.Exact (eulerLeft R n k m i) (eulerRight R n k m i) ∧
      Function.Surjective (eulerRight R n k m i) := by
  apply ModuleSequence.transport
    (RootInvariants.eulerLeft (f R n k) n (hn R n k) t v hv d m i)
    (RootInvariants.eulerRight (f R n k) n (hn R n k) t v hv d m i)
    (eulerLeft R n k m i) (eulerRight R n k m i)
    (globalSectionEquiv R n k t v hv d m)
    ((globalSectionEquiv R n k t v hv d (Pi.single i 1+m)).prodCongr
      (globalSectionEquiv R n k t v hv d (Pi.single i 1+m)))
    (globalSectionEquiv R n k t v hv d (Pi.single i 1+(Pi.single i 1+m)))
  · apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact globalSection_coordinateMul R n k t v hv d m i false x
    · change globalSectionEquiv R n k t v hv d (Pi.single i 1+m)
        (-RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d m i true x)=_
      rw [map_neg,globalSection_coordinateMul]
      rfl
  · apply LinearMap.ext
    intro x
    change globalSectionEquiv R n k t v hv d _
      (RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d _ i true x.1+
        RootInvariants.coordinateMul (f R n k) n (hn R n k) t v hv d _ i false x.2)=_
    rw [map_add,globalSection_coordinateMul,globalSection_coordinateMul]
    rfl
  · exact RootInvariants.eulerLeft_injective (f R n k) n (hn R n k) t v hv d m i
  · exact RootInvariants.euler_exact (f R n k) n (hn R n k) t v hv d m i
  · exact RootInvariants.eulerRight_surjective (f R n k) n (hn R n k) t v hv d m i
end Lech.RootChartAtlas

namespace Lech.ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ) (k : Fin (n+1))
theorem euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n k m i) ∧ Function.Exact (eulerLeft R n k m i) (eulerRight R n k m i) ∧
      Function.Surjective (eulerRight R n k m i) := by
  let f := UniversalCoefficientChart.form R n k
  let : Module.FaithfullyFlat (UniversalCoefficientChart.Ring R n k) (PrimitiveRootModule.chart f) :=
    PrimitiveChart.faithfullyFlat_away f (UniversalCoefficientChart.form_primitive R n k)
  exact RootChartAtlas.section_euler_shortExact R n k (PrimitiveRootModule.coordinate f)
    (PrimitiveRootModule.valueUnit f) (PrimitiveRootModule.eval_valueUnit f)
    (PrimitiveRootModule.splitting f n (UniversalCoefficientChart.form_degree R n k)) m i
end Lech.ProductSourceCover

end

end OAI
