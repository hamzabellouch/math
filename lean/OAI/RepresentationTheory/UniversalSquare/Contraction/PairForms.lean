import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SymmetricPairs

namespace OAI

/-! Pair Forms. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def pairFormTensor {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (B : Matrix (Fin d) (Fin d) ℂ) : WordSpace n d :=
  fun w => ∏ i, B (leftWord e w i) (rightWord e w i)

lemma pairFormTensor_one {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    pairFormTensor e (1 : Matrix (Fin d) (Fin d) ℂ) = symmetricPairs e d := by
  classical
  funext w
  change (∏ i, if leftWord e w i = rightWord e w i then (1 : ℂ) else 0) = _
  by_cases hw : leftWord e w = rightWord e w
  · simp [hw, symmetricPairs]
  · have hi : ∃ i, leftWord e w i ≠ rightWord e w i := by
      exact not_forall.mp (fun he => hw (funext he))
    obtain ⟨i, hi⟩ := hi
    rw [symmetricPairs, ite_eq_right hw]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma pairFormTensor_smul {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (c : ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    pairFormTensor e (c • B) = c^m • pairFormTensor e B := by
  funext w
  simp [pairFormTensor, Finset.prod_mul_distrib]

def pairWordsEquiv {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    (Fin n → Fin d) ≃ (Fin m → Fin d × Fin d) :=
  (positionWordsEquiv e).trans
    (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin d) (fun _ => Fin d)).symm

@[simp] lemma pairWordsEquiv_apply {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (w : Fin n → Fin d) (i : Fin m) :
    pairWordsEquiv e w i = (leftWord e w i, rightWord e w i) := rfl

lemma wordMap_pairFormTensor {n m a b : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (L : Fin a → Fin b → ℂ) (B : Matrix (Fin a) (Fin a) ℂ) :
    wordMap L (pairFormTensor e B) = pairFormTensor e
      (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) := by
  classical
  funext w
  change (∑ c, pairFormTensor e B c * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i) := by
      apply Fintype.sum_equiv (pairWordsEquiv e)
      intro c
      simp only [pairWordsEquiv_apply, pairFormTensor, Finset.prod_mul_distrib]
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ x : Fin m ⊕ Fin m, L (c (e.symm x)) (w (e.symm x)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by
            rw [Fintype.prod_sum_type]
            rfl
      rw [he, mul_assoc]
    _ = _ := by
      change (∑ c : Fin m → Fin a × Fin a,
        ∏ i, B (c i).1 (c i).2 * L (c i).1 (leftWord e w i) *
          L (c i).2 (rightWord e w i)) =
        ∏ i, ∑ p : Fin a × Fin a,
          B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i)
      exact (Fintype.prod_sum (fun (i : Fin m) (p : Fin a × Fin a) =>
        B p.1 p.2 * L p.1 (leftWord e w i) * L p.2 (rightWord e w i))).symm

theorem even_rows_pairFormTensor_support {n m a d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (B : Matrix (Fin a) (Fin a) ℂ)
    (L : Fin a → Fin d → ℂ) (c : ℂ) (hc : c ≠ 0)
    (hL : (fun j k => ∑ p : Fin a × Fin a, B p.1 p.2 * L p.1 j * L p.2 k) =
      c • (1 : Matrix (Fin d) (Fin d) ℂ))
    (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n a) (pairFormTensor e B)).toRepresentation, F ≠ 0 := by
  have hmap : wordMap L (pairFormTensor e B) = c^m • symmetricPairs e d := by
    rw [wordMap_pairFormTensor, hL, pairFormTensor_smul, pairFormTensor_one]
  have hs := even_rows_symmetricPairs_support e μ t he hd
  have hcyc : cyclic (wordRep n d) (wordMap L (pairFormTensor e B)) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [hmap, cyclic_smul_eq _ _ _ (pow_ne_zero m hc)]
  rw [← hcyc] at hs
  obtain ⟨F,hF⟩ := hs
  exact cyclic_projection_support (wordMap L) (pairFormTensor e B) F hF

def shortPairForm : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0,0,0,1; 0,0,-1,0; 0,-1,0,0; 1,0,0,0]

def shortPairCongruence : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1,Complex.I,0,0; 0,0,1,Complex.I; 0,0,-1,Complex.I; 1,-Complex.I,0,0]

lemma shortPairCongruence_gram :
    (fun j k => ∑ p : Fin 4 × Fin 4,
      shortPairForm p.1 p.2 * shortPairCongruence p.1 j * shortPairCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, shortPairForm,
      shortPairCongruence, Matrix.one_apply]

theorem even_rows_shortPair_support {n m : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4) (pairFormTensor e shortPairForm)).toRepresentation, F ≠ 0 :=
  even_rows_pairFormTensor_support e shortPairForm shortPairCongruence 2 (by norm_num)
    shortPairCongruence_gram μ t he hd

def outputTwoForm : Matrix (Fin 2) (Fin 2) ℂ := !![0,1; 1,0]

def outputTwoCongruence : Matrix (Fin 2) (Fin 2) ℂ := !![1,Complex.I; 1,-Complex.I]

lemma outputTwoCongruence_gram :
    (fun j k => ∑ p : Fin 2 × Fin 2,
      outputTwoForm p.1 p.2 * outputTwoCongruence p.1 j * outputTwoCongruence p.2 k) =
      (2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext j k
  fin_cases j <;> fin_cases k <;>
    norm_num [Fintype.sum_prod_type, Fin.sum_univ_succ, outputTwoForm,
      outputTwoCongruence, Matrix.one_apply]

theorem even_rows_outputTwo_support {n m : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ 2) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 2) (pairFormTensor e outputTwoForm)).toRepresentation, F ≠ 0 :=
  even_rows_pairFormTensor_support e outputTwoForm outputTwoCongruence 2 (by norm_num)
    outputTwoCongruence_gram μ t he hd

end Saxl
end
end

end OAI
