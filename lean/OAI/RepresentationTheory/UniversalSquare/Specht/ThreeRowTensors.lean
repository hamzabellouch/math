import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowPieri
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowDensity

namespace OAI

/-! Three Row Tensors. -/

section

noncomputable section
namespace Saxl.ThreeRow

def powerVector (n : ℕ) {d : ℕ} (x : Fin d → ℂ) : WordSpace n d :=
  fun w => ∏ i, x (w i)

lemma wordMap_constant {n a d : ℕ} (L : Fin a → Fin d → ℂ) (k : Fin a) :
    wordMap L (Pi.single (fun _ : Fin n => k) 1) = powerVector n (L k) := by
  ext w
  exact wordMap_single L (fun _ => k) w

lemma powerVector_smul {n d : ℕ} (c : ℂ) (x : Fin d → ℂ) :
    powerVector n (c • x) = c^n • powerVector n x := by
  funext w
  simp [powerVector, Finset.prod_mul_distrib]

def independentTensor {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) : WordSpace n 3 :=
  positionProduct e (positionProduct p (pairFormTensor q Q) (powerVector s x))
    (powerVector 3 y)

def symmetricIndex : Fin 3 → Fin 3 → Fin 12 := !![0,1,2; 1,3,4; 2,4,5]

def matrixCoord (w : Coordinates) (i j : Fin 3) := w (symmetricIndex i j)
def xCoord (w : Coordinates) (i : Fin 3) := w ⟨6+i.val, by omega⟩
def yCoord (w : Coordinates) (i : Fin 3) := w ⟨9+i.val, by omega⟩

def independentFamily {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (w : Coordinates) : WordSpace n 3 :=
  independentTensor q p e (matrixCoord w) (xCoord w) (yCoord w)

lemma gram_symm (z : Parameters) (i j : Fin 3) : gram z i j = gram z j i := by
  unfold gram
  ring

lemma matrixCoord_parameter (z : Parameters) : matrixCoord (parameterMap z) = gram z := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoord,parameterMap,symmetricIndex,Matrix.cons_val,gram_symm] <;>
      exact gram_symm _ _ _

lemma xCoord_parameter (z : Parameters) : xCoord (parameterMap z) = fun i => z (idx 2 i) := by
  funext i
  fin_cases i <;> rfl

lemma yCoord_parameter (z : Parameters) : yCoord (parameterMap z) = fun i => z (idx 3 i) := by
  funext i
  fin_cases i <;> rfl

lemma independentFamily_analytic {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (v : WordSpace n 3) :
    AnalyticOnNhd ℂ (fun w => dotProduct v (independentFamily q p e w)) Set.univ := by
  intro w hw
  unfold dotProduct independentFamily independentTensor positionProduct pairFormTensor powerVector
  apply Finset.analyticAt_fun_sum
  intro c hc
  apply AnalyticAt.mul analyticAt_const
  apply AnalyticAt.mul
  · apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w
    · apply Finset.analyticAt_fun_prod
      intro i hi
      exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w
  · apply Finset.analyticAt_fun_prod
    intro i hi
    exact (ContinuousLinearMap.proj _ : Coordinates →L[ℂ] ℂ).analyticAt w

def packCoordinates (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) : Coordinates :=
  ![Q 0 0,Q 0 1,Q 0 2,Q 1 1,Q 1 2,Q 2 2,x 0,x 1,x 2,y 0,y 1,y 2]

lemma matrixCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ)
    (h : ∀ i j, Q i j = Q j i) : matrixCoord (packCoordinates Q x y) = Q := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixCoord,packCoordinates,symmetricIndex,Matrix.cons_val,h] <;> exact h _ _

lemma xCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    xCoord (packCoordinates Q x y) = x := by
  funext i
  fin_cases i <;> rfl

lemma yCoord_pack (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) :
    yCoord (packCoordinates Q x y) = y := by
  funext i
  fin_cases i <;> rfl

lemma independentFamily_pack {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (Q : Matrix (Fin 3) (Fin 3) ℂ) (x y : Fin 3 → ℂ) (h : ∀ i j, Q i j = Q j i) :
    independentFamily q p e (packCoordinates Q x y) = independentTensor q p e Q x y := by
  rw [independentFamily,matrixCoord_pack Q x y h,xCoord_pack,yCoord_pack]

lemma wordMap_symmetricPairs {n m d : ℕ} (q : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin d → Fin 3 → ℂ) :
    wordMap L (symmetricPairs q d) = pairFormTensor q (fun i j => ∑ k, L k i * L k j) := by
  rw [← pairFormTensor_one,wordMap_pairFormTensor]
  congr 1
  funext i j
  simp [Fintype.sum_prod_type,Matrix.one_apply]

lemma colorTensor_image {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    (L : Fin 5 → Fin 3 → ℂ) :
    wordMap L (colorTensor q p e) = independentTensor q p e
      (fun i j => ∑ k : Fin 3, L (Fin.castAdd 2 k) i * L (Fin.castAdd 2 k) j)
      (L 3) (L 4) := by
  rw [colorTensor,wordMap_positionProduct,wordMap_positionProduct,wordMap_letterLift,
    wordMap_symmetricPairs,wordMap_constant,wordMap_constant]
  rfl

theorem independent_nonvanishing {n r a m s : ℕ} (q : Fin a ≃ Fin m ⊕ Fin m)
    (p : Fin r ≃ Fin a ⊕ Fin s) (e : Fin n ≃ Fin r ⊕ Fin 3)
    {μ : YoungDiagram} (t : Tableau n μ) (ht : μ.colLen 0 ≤ 3)
    (hs : ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 5) (colorTensor q p e)).toRepresentation, F ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (w : Coordinates),
      dotProduct (letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t)))
        (independentFamily q p e w) ≠ 0 := by
  classical
  obtain ⟨F,hF⟩ := hs
  obtain ⟨g,L,hL⟩ := dual_polytabloid_necessary t _ F hF
  let B : Fin 3 → Fin 5 → ℂ := fun i j => if hi : i.val < μ.colLen 0 then L ⟨i.val,hi⟩ j else 0
  have hB (i : Fin (μ.colLen 0)) (j : Fin 5) : B (Fin.castLE ht i) j = L i j := by
    simp [B,i.isLt]
  have hpair : dotProduct
      (letterLift (Fin.castLE ht) (wordRep n (μ.colLen 0) g (polytabloid t)))
      (wordMap (fun j i => B i j) (colorTensor q p e)) ≠ 0 := by
    rw [← wordMap_pair_transpose,wordMap_letterLift]
    simpa only [hB] using hL
  rw [colorTensor_image] at hpair
  let Q : Matrix (Fin 3) (Fin 3) ℂ := fun i j => ∑ k : Fin 3,
    B i (Fin.castAdd 2 k) * B j (Fin.castAdd 2 k)
  have hQ (i j : Fin 3) : Q i j = Q j i := by
    apply Finset.sum_congr rfl
    intro k hk
    exact mul_comm _ _
  refine ⟨g, packCoordinates Q (fun i => B i 3) (fun i => B i 4), ?_⟩
  rwa [independentFamily_pack q p e Q _ _ hQ]

end Saxl.ThreeRow
end
end

end OAI
