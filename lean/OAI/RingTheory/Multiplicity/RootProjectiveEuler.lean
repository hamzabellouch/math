import Mathlib
import OAI.RingTheory.Multiplicity.RootCoefficientEuler

namespace OAI

noncomputable section
open scoped TensorProduct

namespace Lech.ProjectiveRoot
open ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

def coordinateMul (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) (b : Bool) :
    Sections R n s hs m →ₗ[Ring R n s] Sections R n s hs (Pi.single i 1+m) where
  toFun x := ⟨rootCoordinate R n i b*x.val,
    grid_mul_mem R n (Pi.single i 1) m s ∅ _ _ (rootCoordinate_mem R n s i b) x.property⟩
  map_add' x y := Subtype.ext (mul_add _ _ _)
  map_smul' a x := Subtype.ext (by
    change rootCoordinate R n i b*(scalarMap R n s a*x.val)=
      scalarMap R n s a*(rootCoordinate R n i b*x.val)
    ring)

def eulerLeft (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections R n s hs m →ₗ[Ring R n s]
      Sections R n s hs (Pi.single i 1+m) × Sections R n s hs (Pi.single i 1+m) :=
  (coordinateMul R n s hs m i false).prod (-coordinateMul R n s hs m i true)
def eulerRight (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Sections R n s hs (Pi.single i 1+m) × Sections R n s hs (Pi.single i 1+m) →ₗ[Ring R n s]
      Sections R n s hs (Pi.single i 1+(Pi.single i 1+m)) :=
  (coordinateMul R n s hs (Pi.single i 1+m) i true).coprod
    (coordinateMul R n s hs (Pi.single i 1+m) i false)

section Intersection
variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hs : s.Nonempty) [hks : Fact (k∈s)]
private local instance projectiveEulerInstance1 : Algebra (UniversalCoefficientChart.Ring R n k) (Ring R n s) :=
  coefficientAlgebra R n k s hks.out

lemma chartBaseChange_tmul_val (m : Fin n → ℤ) (a : Ring R n s) (x : sectionModule R n k m) :
    (chartBaseChange R n k s hs m (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x):GridAmbient R n)=
      scalarMap R n s a*x.val := by
  have he : a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x=
      a • ((1:Ring R n s) ⊗ₜ[UniversalCoefficientChart.Ring R n k] x) := by
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [he,map_smul,chartBaseChange_one]
  rfl

lemma chartBaseChange_coordinateMul (m : Fin n → ℤ) (i : Fin n) (b : Bool)
    (a : Ring R n s) (x : sectionModule R n k m) :
    chartBaseChange R n k s hs (Pi.single i 1+m)
      (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] ProductSourceCover.coordinateMul R n k m i b x)=
      coordinateMul R n s hs m i b (chartBaseChange R n k s hs m (a ⊗ₜ x)) := by
  apply Subtype.ext
  rw [chartBaseChange_tmul_val]
  change scalarMap R n s a*(rootCoordinate R n i b*x.val)=
    rootCoordinate R n i b*(chartBaseChange R n k s hs m (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x):GridAmbient R n)
  rw [chartBaseChange_tmul_val]
  ring

def chartEulerMiddle (m : Fin n → ℤ) :
    Ring R n s ⊗[UniversalCoefficientChart.Ring R n k] (sectionModule R n k m × sectionModule R n k m)
      ≃ₗ[Ring R n s] Sections R n s hs m × Sections R n s hs m :=
  TensorProduct.prodRight _ (Ring R n s) (Ring R n s) _ _ ≪≫ₗ
    (chartBaseChange R n k s hs m).prodCongr (chartBaseChange R n k s hs m)

include k hks in
lemma intersection_euler_shortExact (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n s hs m i) ∧
      Function.Exact (eulerLeft R n s hs m i) (eulerRight R n s hs m i) ∧
        Function.Surjective (eulerRight R n s hs m i) := by
  let := (sectionModule_properties R n k (Pi.single i 1+(Pi.single i 1+m))).2.1
  obtain ⟨hi,he,hq⟩ := ProductSourceCover.euler_shortExact R n k m i
  obtain ⟨hi,he,hq⟩ := ModuleSequence.baseChange (Ring R n s)
    (ProductSourceCover.eulerLeft R n k m i) (ProductSourceCover.eulerRight R n k m i) hi he hq
  apply ModuleSequence.transport
    (A := Ring R n s)
    (M := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k] sectionModule R n k m)
    (N := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
      (sectionModule R n k (Pi.single i 1+m) × sectionModule R n k (Pi.single i 1+m)))
    (P := Ring R n s ⊗[UniversalCoefficientChart.Ring R n k]
      sectionModule R n k (Pi.single i 1+(Pi.single i 1+m)))
    ((ProductSourceCover.eulerLeft R n k m i).baseChange (Ring R n s))
    ((ProductSourceCover.eulerRight R n k m i).baseChange (Ring R n s))
    (eulerLeft R n s hs m i) (eulerRight R n s hs m i)
    (chartBaseChange R n k s hs m) (chartEulerMiddle R n k s hs (Pi.single i 1+m))
    (chartBaseChange R n k s hs (Pi.single i 1+(Pi.single i 1+m)))
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
        apply Prod.ext
        · exact chartBaseChange_coordinateMul R n k s hs m i false a x
        · change chartBaseChange R n k s hs (Pi.single i 1+m)
            (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] (-ProductSourceCover.coordinateMul R n k m i true x))=_
          rw [TensorProduct.tmul_neg]
          change chartBaseChange R n k s hs (Pi.single i 1+m)
            (-(a ⊗ₜ[UniversalCoefficientChart.Ring R n k] ProductSourceCover.coordinateMul R n k m i true x))=
            -(coordinateMul R n s hs m i true (chartBaseChange R n k s hs m
              (a ⊗ₜ[UniversalCoefficientChart.Ring R n k] x)))
          exact (map_neg (chartBaseChange R n k s hs (Pi.single i 1+m)) _).trans
            (congrArg Neg.neg (chartBaseChange_coordinateMul R n k s hs m i true a x))
    | add x y hx hy => simp only [map_add,hx,hy]
  · apply LinearMap.ext
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a x =>
        change chartBaseChange R n k s hs _
          (a ⊗ₜ[UniversalCoefficientChart.Ring R n k]
            (ProductSourceCover.coordinateMul R n k _ i true x.1+
              ProductSourceCover.coordinateMul R n k _ i false x.2))=_
        rw [TensorProduct.tmul_add,map_add,chartBaseChange_coordinateMul,chartBaseChange_coordinateMul]
        rfl
    | add x y hx hy => simp only [map_add,hx,hy]
  · exact hi
  · exact he
  · exact hq
end Intersection

 

theorem euler_shortExact (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) (i : Fin n) :
    Function.Injective (eulerLeft R n s hs m i) ∧
      Function.Exact (eulerLeft R n s hs m i) (eulerRight R n s hs m i) ∧
        Function.Surjective (eulerRight R n s hs m i) := by
  let k := hs.choose
  let : Fact (k∈s) := ⟨hs.choose_spec⟩
  exact intersection_euler_shortExact R n k s hs m i

lemma coordinateMul_natural {s t : Finset (Fin (n+1))} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (m : Fin n → ℤ) (i : Fin n) (b : Bool) (x : Sections R n s hs m) :
    sectionsRestriction R n hs ht (Pi.single i 1+m) hst (coordinateMul R n s hs m i b x)=
      coordinateMul R n t ht m i b (sectionsRestriction R n hs ht m hst x) := rfl
end Lech.ProjectiveRoot

end

end OAI
