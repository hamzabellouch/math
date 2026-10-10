import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateRotation
import OAI.RepresentationTheory.UniversalSquare.Support.PairSwap

namespace OAI

/-! Candidate Cut. -/

section

noncomputable section
open scoped TensorProduct
namespace UniversalTensorSquare
open Saxl

def candidateCutRow {n M b δ : ℕ} (hM : 4 ≤ M) (t : Tableau n (candidate M b δ)) :=
  altWord (columnGroup (transposeTableau t) ⊓ sectorGroup (candidateTriangle t))
    (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)))

def candidateCutCol {n M b δ : ℕ} (hM : 4 ≤ M) (t : Tableau n (candidate M b δ)) :=
  altWord (columnGroup t ⊓ sectorGroup (candidateTriangle t))
    (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n)))

lemma candidateRotatePositions_sign {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    signC (candidateRotateColPositions hM t : Equiv.Perm (Fin n)) =
      signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) := by
  let q : Equiv.Perm (Fin n) := (t.trans (candidateSwap M b δ)).trans t.symm
  have he : (candidateRotateColPositions hM t : Equiv.Perm (Fin n)) =
      q * (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * q := by
    ext i
    simp [q, candidateRotateColPositions, candidateRotateRowPositions, candidateRotateCol]
  rw [he, map_mul, map_mul]
  calc
    signC q * signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * signC q =
      signC (candidateRotateRowPositions hM t : Equiv.Perm (Fin n)) * (signC q * signC q) := by ring
    _ = _ := by rw [signC_mul_self, mul_one]

theorem candidate_cut_layers {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      wordTensor _ _ _ (candidateCutRow hM t ⊗ₜ[ℂ] candidateCutCol hM t) := by
  rw [candidate_projected_sector hM, rowColumnWord]
  rw [coordinateProjection_tensor
    (fun a : Fin n → Fin ((candidate M b δ).transpose.colLen 0) =>
      ∀ i, candidateMark M b (a i).val ↔ candidateTriangle t i)
    (fun a : Fin n → Fin ((candidate M b δ).colLen 0) =>
      ∀ i, candidateMark M b (a i).val ↔ candidateTriangle t i)]
  have hr := altWord_sector_rotated (columnGroup (transposeTableau t))
    (rowWord (transposeTableau t)) (fun a => candidateMark M b a.val) (candidateTriangle t)
    (candidateRotateRowPositions hM t) (by
      intro i
      simpa [rowWord, transposeTableau, candidateRotateRowPositions, candidateTriangle] using
        candidateRotateRow_mark M b δ hM (t i))
  have hc := altWord_sector_rotated (columnGroup t)
    (rowWord t) (fun a => candidateMark M b a.val) (candidateTriangle t)
    (candidateRotateColPositions hM t) (by
      intro i
      simpa [rowWord, candidateRotateColPositions, candidateTriangle] using
        candidateRotateCol_mark M b δ hM (t i))
  rw [polytabloid_eq_altWord, polytabloid_eq_altWord, hr, hc,
    TensorProduct.smul_tmul_smul, candidateRotatePositions_sign, signC_mul_self, one_smul]
  rfl

def candidateHighPositions {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    {i : Fin n // candidateTriangle t i} ≃ Fin (staircase (M-2)).card where
  toFun i := (stairTableau (M-2)).symm ⟨(t i.val).val, mem_staircase.mpr i.property⟩
  invFun j := ⟨t.symm ⟨(stairTableau (M-2) j).val, mem_candidate.mpr (Or.inl (by
    have := mem_staircase.mp (stairTableau (M-2) j).property; omega))⟩, by
      change (t (t.symm _)).val.1 + (t (t.symm _)).val.2 < M-2
      simp only [Equiv.apply_symm_apply]
      exact mem_staircase.mp (stairTableau (M-2) j).property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by simp

abbrev candidateBandSize {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :=
  Nat.card {i : Fin n // ¬candidateTriangle t i}

def candidateCutPositions {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    Fin n ≃ Fin (staircase (M-2)).card ⊕ Fin (candidateBandSize t) := by
  classical
  exact (Equiv.sumCompl (candidateTriangle t)).symm.trans
    (Equiv.sumCongr (candidateHighPositions t) (Fintype.equivFinOfCardEq
      (show Fintype.card {i : Fin n // ¬candidateTriangle t i} = candidateBandSize t
        from Fintype.card_eq_nat_card)))

lemma candidateCutPositions_high {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) (i : Fin n) :
    (candidateCutPositions t i).isLeft = true ↔ candidateTriangle t i := by
  classical
  by_cases hi : candidateTriangle t i <;>
    simp [candidateCutPositions, Equiv.sumCompl, Equiv.sumCongr, hi]

lemma candidateCutPositions_left {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (i : Fin (staircase (M-2)).card) :
    (t ((candidateCutPositions t).symm (Sum.inl i))).val = (stairTableau (M-2) i).val := by
  classical
  simp [candidateCutPositions, Equiv.sumCompl, candidateHighPositions]

lemma candidateBandSize_add {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    (staircase (M-2)).card + candidateBandSize t = n := by
  have hh := Fintype.card_congr (candidateCutPositions t)
  simpa using hh.symm

def candidateHighLetter (M b δ : ℕ) (hM : 4 ≤ M) :
    Fin ((staircase (M-2)).colLen 0) → Fin ((candidate M b δ).colLen 0) :=
  fun a => ⟨if a.val = M-3 then M+b-1 else a.val+2, by
    have ha := a.isLt
    simp only [staircase_colLen, Nat.sub_zero] at ha
    simp only [candidate_colLen M b δ 0 hM]
    simp only [candidateLengths, ite_true]
    split_ifs <;> omega⟩

def candidateHighRowLetter (M b δ : ℕ) (hM : 4 ≤ M) :
    Fin ((staircase (M-2)).colLen 0) → Fin ((candidate M b δ).transpose.colLen 0) :=
  Fin.cast (congrArg (fun α : YoungDiagram => α.colLen 0) (candidate_transpose M b δ)).symm ∘
    candidateHighLetter M b δ hM

lemma candidateRotateRow_triangle {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hx : x.val.1 + x.val.2 < M-2) :
    (candidateRotateRow M b δ hM x).val.2 =
      if x.val.2 = M-3 then M+b-1 else x.val.2+2 := by
  change (if x.val.1 = 0 then Equiv.swap (M-1) (M+b-1)
      (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)
    else (if x.val.2 < M-2-x.val.1 then x.val.2+2
      else if x.val.2 < M-2-x.val.1+2 then x.val.2-(M-2-x.val.1) else x.val.2)) = _
  simp only [Equiv.swap_apply_def]
  split_ifs <;> omega

lemma candidateRotateCol_triangle {M b δ : ℕ} (hM : 4 ≤ M)
    (x : (candidate M b δ).cells) (hx : x.val.1 + x.val.2 < M-2) :
    (candidateRotateCol M b δ hM x).val.1 =
      if x.val.1 = M-3 then M+b-1 else x.val.1+2 := by
  exact candidateRotateRow_triangle hM (candidateSwap M b δ x) (by
    change x.val.2 + x.val.1 < M-2
    omega)

lemma candidate_highRow_word {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    leftWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))) =
      candidateHighRowLetter M b δ hM ∘ rowWord (stairRowTableau (M-2)) := by
  funext i
  apply Fin.ext
  have hi := mem_staircase.mp (stairTableau (M-2) i).property
  have he := candidateCutPositions_left t i
  simp only [leftWord, Function.comp_apply, rowWord, stairRowTableau, transposeTableau,
    candidateRotateRowPositions, Equiv.trans_apply, Equiv.apply_symm_apply,
    staircaseSwap, candidateHighRowLetter, candidateHighLetter, Fin.val_cast]
  change (candidateRotateRow M b δ hM (t ((candidateCutPositions t).symm (Sum.inl i)))).val.2 = _
  rw [candidateRotateRow_triangle hM _ (by rw [he]; exact hi), he]
  rfl

lemma candidate_highCol_word {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    leftWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))) =
      candidateHighLetter M b δ hM ∘ rowWord (stairTableau (M-2)) := by
  funext i
  apply Fin.ext
  have hi := mem_staircase.mp (stairTableau (M-2) i).property
  have he := candidateCutPositions_left t i
  simp only [leftWord, Function.comp_apply, rowWord, candidateRotateColPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, candidateHighLetter]
  change (candidateRotateCol M b δ hM (t ((candidateCutPositions t).symm (Sum.inl i)))).val.1 = _
  rw [candidateRotateCol_triangle hM _ (by rw [he]; exact hi), he]
  rfl

def candidateBandTableau {n M b δ : ℕ} (t : Tableau n (candidate M b δ))
    (j : Fin (candidateBandSize t)) : (candidate M b δ).cells :=
  t ((candidateCutPositions t).symm (Sum.inr j))

def candidateBandRow {n M b δ : ℕ} (hM : 4 ≤ M) (t : Tableau n (candidate M b δ)) :=
  altWord (fiberGroup (fun j => (candidateBandTableau t j).val.1))
    (rightWord (candidateCutPositions t)
      (rowWord (transposeTableau t) ∘ (candidateRotateRowPositions hM t : Equiv.Perm (Fin n))))

def candidateBandCol {n M b δ : ℕ} (hM : 4 ≤ M) (t : Tableau n (candidate M b δ)) :=
  altWord (fiberGroup (fun j => (candidateBandTableau t j).val.2))
    (rightWord (candidateCutPositions t)
      (rowWord t ∘ (candidateRotateColPositions hM t : Equiv.Perm (Fin n))))

lemma candidate_row_cut_group {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    columnGroup (transposeTableau t) ⊓ sectorGroup (candidateTriangle t) =
      fiberGroup (fun i => (t i).val.1) ⊓
        sectorGroup (fun i => (candidateCutPositions t i).isLeft = true) := by
  congr 1
  congr 1
  funext i
  exact propext (candidateCutPositions_high t i).symm

lemma candidate_col_cut_group {n M b δ : ℕ} (t : Tableau n (candidate M b δ)) :
    columnGroup t ⊓ sectorGroup (candidateTriangle t) =
      fiberGroup (fun i => (t i).val.2) ⊓
        sectorGroup (fun i => (candidateCutPositions t i).isLeft = true) := by
  congr 1
  congr 1
  funext i
  exact propext (candidateCutPositions_high t i).symm

theorem candidateCutRow_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateCutRow hM t = positionProduct (candidateCutPositions t)
      (letterLift (candidateHighRowLetter M b δ hM) (polytabloid (stairRowTableau (M-2))))
      (candidateBandRow hM t) := by
  unfold candidateCutRow
  rw [candidate_row_cut_group, altWord_fiber_split]
  congr 1
  rw [candidate_highRow_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau (M-2) i).val.1)
  congr 1
  funext i
  exact congrArg Prod.fst (candidateCutPositions_left t i)

theorem candidateCutCol_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateCutCol hM t = positionProduct (candidateCutPositions t)
      (letterLift (candidateHighLetter M b δ hM) (polytabloid (stairTableau (M-2))))
      (candidateBandCol hM t) := by
  unfold candidateCutCol
  rw [candidate_col_cut_group, altWord_fiber_split]
  congr 1
  rw [candidate_highCol_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau (M-2) i).val.2)
  congr 1
  funext i
  exact congrArg Prod.snd (candidateCutPositions_left t i)

def candidateHighMap {n : ℕ} (M b δ : ℕ) (hM : 4 ≤ M) :=
  pairWordMap (n := n) (letterLift (candidateHighRowLetter M b δ hM))
    (letterLift (candidateHighLetter M b δ hM))

def candidateHighWord (M b δ : ℕ) (hM : 4 ≤ M) :=
  candidateHighMap M b δ hM (staircaseWord (M-2))

def candidateBandWord {n M b δ : ℕ} (hM : 4 ≤ M) (t : Tableau n (candidate M b δ)) :=
  wordTensor _ _ _ (candidateBandRow hM t ⊗ₜ[ℂ] candidateBandCol hM t)

theorem candidate_cut_factor {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    sameMarkProjection _ _ _ (candidateMark M b) (rowColumnWord t) =
      positionProduct (candidateCutPositions t) (candidateHighWord M b δ hM)
        (candidateBandWord hM t) := by
  rw [candidate_cut_layers, candidateCutRow_factor, candidateCutCol_factor]
  unfold candidateHighWord candidateHighMap staircaseWord
  rw [pairWordMap_tensor]
  ext w
  simp only [wordTensor_tmul, candidateBandWord, positionProduct]
  exact mul_mul_mul_comm _ _ _ _

end UniversalTensorSquare
end
end

end OAI
