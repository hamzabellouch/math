import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Balanced Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

lemma short_height_ge_two (m : ℕ) (hm : 1 ≤ m) :
    2 ≤ (ShortColumns.shape m 0).colLen 0 := by
  have hc : (1,0) ∈ ShortColumns.shape m 0 :=
    (ShortColumns.mem_shape m 0 1 0).mpr (Or.inr ⟨rfl, by omega⟩)
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
  omega

def pairAtOutputTwo (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    Fin ((ShortColumns.shape m 0).colLen 0 * (ShortColumns.shape m 0).colLen 0) :=
  finProdFinEquiv (Fin.castLE (short_height_ge_two m hm) i,
    Fin.castLE (short_height_ge_two m hm) (Fin.rev i))

lemma pairAtOutputTwo_output (m : ℕ) (hm : 1 ≤ m) (i : Fin 2) :
    output (pairAtOutputTwo m hm i) = 2 := by
  simp only [output, pairAtOutputTwo, Equiv.symm_apply_apply, Fin.val_castLE, Fin.val_rev]
  have hi := i.isLt
  omega

lemma evenTableau_eval (m : ℕ) (w : Fin (2*m) → Fin ((ShortColumns.shape m 0).colLen 0)) :
    polytabloid (ShortColumns.evenTableau m) w =
      ShortColumns.evenAlt m (Fin.castLE (ShortColumns.height_le m 0) ∘ w) := by
  have he := congrFun (ShortColumns.evenTableau_polytabloid m)
    (Fin.castLE (ShortColumns.height_le m 0) ∘ w)
  rw [letterLift_eval _ (Fin.castLE_injective _) _ w] at he
  exact he

lemma outputTwo_pair_entry (i j : Fin 2) :
    PathLayer.J i j * PathLayer.J (Fin.rev i) (Fin.rev j) =
      (-1 : ℂ) * outputTwoForm i j := by
  fin_cases i <;> fin_cases j <;> norm_num [PathLayer.J, outputTwoForm, Fin.rev]

lemma outputTwo_squared_polytabloid (m : ℕ) (hm : 1 ≤ m)
    (w : Fin (2*m) → Fin 2) :
    wordTensor (2*m) _ _ (polytabloid (ShortColumns.evenTableau m) ⊗ₜ[ℂ]
      polytabloid (ShortColumns.evenTableau m)) (pairAtOutputTwo m hm ∘ w) =
      ((-1 : ℂ)^m • pairFormTensor (ShortColumns.pairSplit m) outputTwoForm) w := by
  rw [wordTensor_tmul, evenTableau_eval, evenTableau_eval]
  have hl : Fin.castLE (ShortColumns.height_le m 0) ∘
      splitLeft (pairAtOutputTwo m hm ∘ w) = w := by
    funext i
    apply Fin.ext
    simp [splitLeft, pairAtOutputTwo]
  have hr : Fin.castLE (ShortColumns.height_le m 0) ∘
      splitRight (pairAtOutputTwo m hm ∘ w) = Fin.rev ∘ w := by
    funext i
    apply Fin.ext
    simp [splitRight, pairAtOutputTwo]
  rw [hl,hr, ShortColumns.evenAlt_formula, ShortColumns.evenAlt_formula,
    ← Finset.prod_mul_distrib]
  simp only [Function.comp_apply, outputTwo_pair_entry, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem repeated_twos (m : ℕ) (hm : 1 ≤ m)
    (a b : Tableau (2*m) (ShortColumns.shape m 0))
    (μ : YoungDiagram) (t : Tableau (2*m) μ)
    (he : ∀ i, Even (μ.rowLen i)) (hμ : μ.colLen 0 ≤ 2) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs ({2} : Set ℕ))
        (inOutputs_invariant ({2} : Set ℕ))).toRepresentation, Function.Injective F := by
  classical
  let P := inOutputs (n := 2*m) (d := (ShortColumns.shape m 0).colLen 0)
    (e := (ShortColumns.shape m 0).colLen 0) ({2} : Set ℕ)
  let hP := inOutputs_invariant (n := 2*m) (d := (ShortColumns.shape m 0).colLen 0)
    (e := (ShortColumns.shape m 0).colLen 0) ({2} : Set ℕ)
  let W := projectedSpechtTensor a b P hP
  have hma : polytabloid (ShortColumns.evenTableau m) ∈ spechtSub a := by
    rw [← spechtSub_tableau_independent (ShortColumns.evenTableau m) a]
    exact mem_cyclic _ _
  have hmb : polytabloid (ShortColumns.evenTableau m) ∈ spechtSub b := by
    rw [← spechtSub_tableau_independent (ShortColumns.evenTableau m) b]
    exact mem_cyclic _ _
  let z : W.toSubmodule := projectedTensorQuotient a b P hP
    (⟨polytabloid (ShortColumns.evenTableau m),hma⟩ ⊗ₜ[ℂ]
      ⟨polytabloid (ShortColumns.evenTableau m),hmb⟩)
  let D : Representation.IntertwiningMap W.toRepresentation (wordRep (2*m) 2) :=
    (restrictLetters (pairAtOutputTwo m hm)).comp (subrepInclusion W)
  have hz : D z = (-1 : ℂ)^m • pairFormTensor (ShortColumns.pairSplit m) outputTwoForm := by
    funext w
    change coordinateProjection P (spechtTensorMap a b
      (⟨polytabloid (ShortColumns.evenTableau m),hma⟩ ⊗ₜ[ℂ]
        ⟨polytabloid (ShortColumns.evenTableau m),hmb⟩))
          (pairAtOutputTwo m hm ∘ w) = _
    rw [spechtTensorMap, coordinateProjection_apply, ite_eq_left]
    · exact outputTwo_squared_polytabloid m hm w
    · intro i
      exact pairAtOutputTwo_output m hm (w i)
  have hs := even_rows_outputTwo_support (ShortColumns.pairSplit m) μ t he hμ
  have hc : cyclic (wordRep (2*m) 2) (D z) =
      cyclic (wordRep (2*m) 2) (pairFormTensor (ShortColumns.pairSplit m) outputTwoForm) := by
    rw [hz, cyclic_smul_eq _ _ _ (pow_ne_zero m (by norm_num))]
  rw [← hc] at hs
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D z f hf
  let F := (subrepInclusion (cyclic W.toRepresentation z)).comp g
  have hF : F ≠ 0 := by
    intro hz
    apply hg
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun H => H x) hz
  let := specht_irreducible t
  exact ⟨F, (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF⟩

end Saxl.Balance
end
end

end OAI
