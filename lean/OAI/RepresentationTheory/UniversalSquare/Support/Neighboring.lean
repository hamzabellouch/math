import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.Extensions
import OAI.RepresentationTheory.UniversalSquare.Support.ProjectedTensor

namespace OAI

/-! Neighboring. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl
namespace Balance

def output {d e : ℕ} (a : Fin (d*e)) : ℕ :=
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).1.val +
  ((finProdFinEquiv : Fin d × Fin e ≃ Fin (d*e)).symm a).2.val + 1

def inOutputs {n d e : ℕ} (I : Set ℕ) (w : Fin n → Fin (d*e)) : Prop :=
  ∀ i, output (w i) ∈ I

lemma inOutputs_invariant {n d e : ℕ} (I : Set ℕ)
    (g : Equiv.Perm (Fin n)) (w : Fin n → Fin (d*e)) :
    inOutputs I (w ∘ g) ↔ inOutputs I w := by
  constructor
  · intro h i
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using h (g.symm i)
  · intro h i
    exact h (g i)

def reverseShortColumn (r j : ℕ) : ℕ := if j = r then r else r-1-j

lemma reverseShortColumn_invol (r j : ℕ) (hj : j ≤ r) :
    reverseShortColumn r (reverseShortColumn r j) = j := by
  unfold reverseShortColumn
  split_ifs <;> omega

def reverseShortColumns (r : ℕ) : (ShortColumns.shape r 1).cells ≃
    (ShortColumns.shape r 1).cells where
  toFun c := ⟨(c.val.1, reverseShortColumn r c.val.2), by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply (ShortColumns.mem_shape r 1 _ _).mpr
    unfold reverseShortColumn
    split_ifs <;> omega⟩
  invFun c := ⟨(c.val.1, reverseShortColumn r c.val.2), by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply (ShortColumns.mem_shape r 1 _ _).mpr
    unfold reverseShortColumn
    split_ifs <;> omega⟩
  left_inv c := by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact reverseShortColumn_invol r c.val.2 (by omega)
  right_inv c := by
    have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
    change (c.val.1 = 0 ∧ c.val.2 < r+1) ∨ (c.val.1 = 1 ∧ c.val.2 < r) at hc
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact reverseShortColumn_invol r c.val.2 (by omega)

def neighborLayer (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1) :=
  (ShortColumns.oddTableau r).trans (reverseShortColumns r)

def neighborTableau (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1).transpose :=
  transposeTableau (neighborLayer r)

def neighborRight (r : ℕ) : Tableau (2*r+1) (ShortColumns.shape r 1).transpose :=
  Fin.revPerm.trans (neighborTableau r)

lemma neighborLayer_row (r : ℕ) (i : Fin (2*r+1)) :
    ((neighborLayer r) i).val.1 = (PathLayer.base i).val :=
  ShortColumns.oddTableau_row r i

lemma neighborLayer_col (r : ℕ) (i : Fin (2*r+1)) :
    ((neighborLayer r) i).val.2 = if i.val = 0 then r else r-1-(i.val-1)/2 := by
  have hi := i.isLt
  simp only [neighborLayer, Equiv.trans_apply, reverseShortColumns, Equiv.coe_fn_mk,
    ShortColumns.oddTableau, reverseShortColumn]
  split_ifs <;> dsimp only at * <;> omega

lemma neighborLayer_col_iff (r : ℕ) (i j : Fin (2*r+1)) :
    ((neighborLayer r) i).val.2 = ((neighborLayer r) j).val.2 ↔
      PathLayer.tag i = PathLayer.tag j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [neighborLayer_col, neighborLayer_col]
  simp only [PathLayer.tag]
  split_ifs <;> omega

lemma neighborLayer_group (r : ℕ) :
    columnGroup (neighborLayer r) = fiberGroup (@PathLayer.tag r) := by
  apply Subgroup.ext
  intro g
  change (∀ i, ((neighborLayer r) (g i)).val.2 = ((neighborLayer r) i).val.2) ↔ _
  simp only [neighborLayer_col_iff]
  rfl

lemma neighborLayer_polytabloid (r : ℕ) :
    letterLift (Fin.castLE (ShortColumns.height_le r 1)) (polytabloid (neighborLayer r)) =
      PathLayer.rowAlt r := by
  rw [polytabloid_eq_altWord, letterLift_altWord, neighborLayer_group]
  congr 1
  funext i
  apply Fin.ext
  exact neighborLayer_row r i

lemma neighbor_outputs (r : ℕ) :
    inOutputs (Set.Icc r (r+1))
      (mergeWords (rowWord (neighborTableau r)) (rowWord (neighborRight r))) := by
  intro i
  simp only [output, mergeWords, Equiv.symm_apply_apply]
  change ((neighborLayer r i).val.2 + (neighborLayer r i.rev).val.2 + 1) ∈ Set.Icc r (r+1)
  rw [neighborLayer_col, neighborLayer_col]
  simp only [Set.mem_Icc, Fin.val_rev]
  have hi := i.isLt
  split_ifs <;> omega

def neighborLetter (r : ℕ) : Fin ((ShortColumns.shape r 1).transpose.transpose.colLen 0) → Fin 2 :=
  (Fin.castLE (ShortColumns.height_le r 1)) ∘ Fin.cast
    (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose (ShortColumns.shape r 1)))

lemma letterLift_comp {n a b c : ℕ} (f : Fin a → Fin b) (g : Fin b → Fin c) :
    letterLift (n := n) (g ∘ f) = (letterLift g).comp (letterLift f) := by
  classical
  apply Representation.IntertwiningMap.ext
  apply LinearMap.pi_ext
  intro w c
  have he : (Pi.single w c : WordSpace n a) = c • Pi.single w 1 := by
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  rw [he, map_smul, map_smul]
  congr 1
  change letterLift (g ∘ f) (Pi.single w 1) = letterLift g (letterLift f (Pi.single w 1))
  rw [letterLift_single, letterLift_single, letterLift_single]
  rfl

lemma neighbor_left_word (r : ℕ) :
    letterLift (neighborLetter r) (polytabloid (transposeTableau (neighborTableau r))) =
      PathLayer.rowAlt r := by
  rw [neighborLetter, letterLift_comp]
  change letterLift _ (letterLift _
    (polytabloid (transposeTableau (transposeTableau (neighborLayer r))))) = _
  rw [polytabloid_doubleTranspose, neighborLayer_polytabloid]

lemma neighbor_move (r : ℕ) :
    tableauMove (transposeTableau (neighborTableau r))
      (transposeTableau (neighborRight r)) = Fin.revPerm := by
  rw [transposeTableau_move]
  apply Equiv.ext
  intro i
  simp only [tableauMove, Equiv.trans_apply, neighborRight,
    Equiv.symm_trans_apply, Equiv.symm_apply_apply]
  rfl

lemma neighbor_right_word (r : ℕ) :
    letterLift (neighborLetter r) (polytabloid (transposeTableau (neighborRight r))) =
      wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r) := by
  rw [polytabloid_move (transposeTableau (neighborTableau r))
    (transposeTableau (neighborRight r)), neighbor_move]
  rw [Representation.IntertwiningMap.isIntertwining]
  rw [neighbor_left_word]

lemma neighbor_pair_word (r : ℕ) :
    pairWordMap (letterLift (neighborLetter r)) (letterLift (neighborLetter r))
      (wordTensor _ _ _ (polytabloid (transposeTableau (neighborTableau r)) ⊗ₜ[ℂ]
        polytabloid (transposeTableau (neighborRight r)))) =
      (-1 : ℂ)^r • Path.bandWord r := by
  rw [pairWordMap_tensor, neighbor_left_word, neighbor_right_word]
  funext w
  rw [wordTensor_tmul]
  exact PathLayer.paired_rowAlt r w

theorem neighboring (r : ℕ)
    (a b : Tableau (2*r+1) (ShortColumns.shape r 1).transpose)
    (μ : YoungDiagram) (t : Tableau (2*r+1) μ) (hμ : μ.colLen 0 ≤ 4) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc r (r+1)))
        (inOutputs_invariant (Set.Icc r (r+1)))).toRepresentation, Function.Injective F := by
  let D := pairWordMap (n := 2*r+1)
    (letterLift (neighborLetter r)) (letterLift (neighborLetter r))
  let v := wordTensor _ _ _
    (polytabloid (transposeTableau (neighborTableau r)) ⊗ₜ[ℂ]
      polytabloid (transposeTableau (neighborRight r)))
  have hs : ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*r+1) 4) (D v)).toRepresentation, f ≠ 0 := by
    dsimp only [D, v]
    rw [neighbor_pair_word, cyclic_smul_eq _ _ _ (pow_ne_zero r (by norm_num))]
    exact Path.odd_path_support r μ t hμ
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D v f hf
  exact projectedTensor_support_of_coordinate a (neighborTableau r)
    b (neighborRight r) t _ _ (neighbor_outputs r) g hg

end Balance
end Saxl
end
end

end OAI
