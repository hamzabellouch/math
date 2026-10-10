import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ThreeRowColumns

namespace OAI

/-! Three Row Local. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.ThreeRow
open FlagColumns Columns Balance

def twos (m : ℕ) : List ℕ := List.replicate m 2

def ones (s : ℕ) : List ℕ := List.replicate s 1

def pairPositions (m : ℕ) : Fin (twos m).sum ≃ Fin m ⊕ Fin m :=
  (finCongr (by simp [twos,Nat.mul_comm])).trans (ShortColumns.pairSplit m)

@[simp] lemma pairPositions_left_val (m : ℕ) (i : Fin m) :
    ((pairPositions m).symm (Sum.inl i)).val = 2*i.val := rfl

@[simp] lemma pairPositions_right_val (m : ℕ) (i : Fin m) :
    ((pairPositions m).symm (Sum.inr i)).val = 2*i.val+1 := rfl

lemma sixSquare_twos (m : ℕ) :
    sixSquare (blocks (twos m) (standard 3)) = pairFormTensor (pairPositions m) sixPairForm := by
  induction m with
  | zero =>
    funext w
    change sixSquare (blocks [] (standard 3)) w = _
    erw [blocks_nil,sixSquare_apply]
    simp [pairFormTensor]
  | succ m ih =>
    change sixSquare (blocks (2 :: twos m) (standard 3)) = _
    rw [blocks_cons]
    erw [sixSquare_product,ih]
    funext w
    change sixSquare (wedge 2 (standard 3)) (leftWord finSumFinEquiv.symm w) *
      pairFormTensor (pairPositions m) sixPairForm (rightWord finSumFinEquiv.symm w) = _
    rw [sixSquare_pair]
    unfold pairFormTensor
    rw [Fin.prod_univ_succ]
    apply congrArg₂ (· * ·)
    · congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      congr 1 <;> apply congrArg w <;> apply Fin.ext <;> simp <;> omega

lemma sixSquare_one (w : Fin 1 → Fin 6) :
    sixSquare (wedge 1 (standard 3)) w = if w 0 = 0 then 1 else 0 := by
  rw [sixSquare_apply,wedge_apply_det,wedge_apply_det]
  simp only [Matrix.det_unique,Matrix.of_apply]
  generalize w 0 = a
  fin_cases a <;> norm_num [standard,pairCoords,Fin.ext_iff]

lemma sixSquare_ones (s : ℕ) :
    sixSquare (blocks (ones s) (standard 3)) = Pi.single (fun _ => (0 : Fin 6)) 1 := by
  classical
  induction s with
  | zero =>
    funext w
    change sixSquare (blocks [] (standard 3)) w = _
    erw [blocks_nil,sixSquare_apply]
    have hw : w = fun _ => 0 := by ext i; exact Fin.elim0 i
    simp [hw]
  | succ s ih =>
    change sixSquare (blocks (1 :: ones s) (standard 3)) = _
    rw [blocks_cons]
    erw [sixSquare_product,ih,
      single_positionProduct finSumFinEquiv.symm (fun _ => 0)]
    congr 1
    funext w
    rw [sixSquare_one,Pi.single_apply]
    congr 1
    simp only [eq_iff_iff]
    constructor
    · intro h
      funext i
      have he : i = 0 := Subsingleton.elim _ _
      simpa [he,leftWord] using h
    · intro h
      exact congrFun h 0

def columns (m s : ℕ) : List ℕ := (twos m ++ ones s) ++ [3]

def shortSplit (m s : ℕ) : Fin (twos m ++ ones s).sum ≃ Fin (twos m).sum ⊕ Fin s :=
  (appendPositions (twos m) (ones s)).trans
    (Equiv.sumCongr (Equiv.refl _) (finCongr (by simp [ones])))

def tripleSplit (m s : ℕ) : Fin (columns m s).sum ≃ Fin (twos m ++ ones s).sum ⊕ Fin 3 :=
  (appendPositions (twos m ++ ones s) [3]).trans
    (Equiv.sumCongr (Equiv.refl _) (finCongr (by simp)))

lemma sixSquare_columns (m s : ℕ) :
    sixSquare (blocks (columns m s) (standard 3)) =
      -generator (pairPositions m) (shortSplit m s) (tripleSplit m s) := by
  change sixSquare (blocks ((twos m ++ ones s) ++ [3]) (standard 3)) = _
  rw [blocks_append,blocks_append]
  erw [sixSquare_product,sixSquare_product,sixSquare_twos,sixSquare_ones]
  have hthree : sixSquare (blocks [3] (standard 3)) = -symmetricTriple := by
    rw [blocks_cons,blocks_nil]
    erw [sixSquare_product]
    funext w
    change sixSquare (wedge 3 (standard 3)) _ * sixSquare (fun _ => 1) _ = _
    erw [sixSquare_triple,sixSquare_apply]
    simp only [mul_one]
    congr 1
  rw [hthree]
  funext w
  change (_ * _) * (-symmetricTriple _) = -((_ * _) * symmetricTriple _)
  rw [mul_neg]
  congr 2
  apply congrArg₂ (· * ·)
  · rfl
  · simp only [Pi.single_apply]
    congr 1
    apply propext
    constructor
    · intro h
      funext i
      have hi := congrFun h (⟨i.val,by simp [ones]⟩ : Fin (ones s).sum)
      exact hi
    · intro h
      funext i
      have hi := congrFun h (⟨i.val,by simpa [ones] using i.isLt⟩ : Fin s)
      exact hi

end Saxl.ThreeRow
end
end

end OAI
