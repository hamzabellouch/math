import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.SplitFlag
import OAI.RepresentationTheory.UniversalSquare.Specht.ColumnTensorSplit
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! No Mixed Columns. -/

section

noncomputable section
namespace Saxl.FlagColumns
open Columns

lemma wedge_apply_det {r d : ℕ} (N : ℕ → Fin d → ℂ) (w : Fin r → Fin d) :
    wedge r N w = (Matrix.of (fun i j : Fin r => N i.val (w j))).det := by
  classical
  simp only [wedge, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    pure, Matrix.det_apply', Matrix.of_apply, signC]
  rfl

theorem wedge_split_of_zero {a b d : ℕ}
    (L N Q : ℕ → Fin d → ℂ) (w : Fin (a+b) → Fin d)
    (hN : ∀ i : Fin a, L i.val = N i.val)
    (hQ : ∀ i : Fin b, L (a+i.val) = Q i.val)
    (hz : ∀ (i : Fin b) (j : Fin a), Q i.val (w (Fin.castAdd b j)) = 0) :
    wedge (a+b) L w = wedge a N (leftWord finSumFinEquiv.symm w) *
      wedge b Q (rightWord finSumFinEquiv.symm w) := by
  classical
  rw [wedge_apply_det, wedge_apply_det, wedge_apply_det]
  rw [← Matrix.det_submatrix_equiv_self (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b))]
  let A : Matrix (Fin a) (Fin a) ℂ := fun i j => N i.val (w (Fin.castAdd b j))
  let B : Matrix (Fin a) (Fin b) ℂ := fun i j => N i.val (w (Fin.natAdd a j))
  let D : Matrix (Fin b) (Fin b) ℂ := fun i j => Q i.val (w (Fin.natAdd a j))
  have hm : (Matrix.of (fun i j : Fin (a+b) => L i.val (w j))).submatrix
      (finSumFinEquiv : Fin a ⊕ Fin b → Fin (a+b)) finSumFinEquiv =
      Matrix.fromBlocks A B 0 D := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · exact congrFun (hN i) _
    · exact congrFun (hN i) _
    · exact (congrFun (hQ i) _).trans (hz i j)
    · exact congrFun (hQ i) _
  rw [hm, Matrix.det_fromBlocks_zero₂₁]
  rfl

def joinedFlag {D : ℕ} (d : ℕ) (N Q : ℕ → Fin D → ℂ) : ℕ → Fin D → ℂ :=
  fun i => if i < d then N i else Q (i-d)

lemma joinedFlag_left {D d : ℕ} (N Q : ℕ → Fin D → ℂ) (i : Fin d) :
    joinedFlag d N Q i.val = N i.val := ite_eq_left i.isLt

lemma joinedFlag_right {D d : ℕ} (N Q : ℕ → Fin D → ℂ) (i : ℕ) :
    joinedFlag d N Q (d+i) = Q i := by
  simp [joinedFlag]

theorem joinedFlag_column_factor {a b d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ha : a ≤ d) (hb : b ≠ 0 → a = d)
    (hQ : ∀ i c, P c → Q i c = 0) (w : Fin (a+b) → Fin D)
    (hw : b ≠ 0 → ∀ i : Fin a, P (w (Fin.castAdd b i))) :
    wedge (a+b) (joinedFlag d N Q) w =
      wedge a N (leftWord finSumFinEquiv.symm w) *
        wedge b Q (rightWord finSumFinEquiv.symm w) := by
  apply wedge_split_of_zero
  · intro i
    exact ite_eq_left (i.isLt.trans_le ha)
  · intro i
    have hb' : b ≠ 0 := by have hi := i.isLt; omega
    rw [hb hb']
    exact joinedFlag_right N Q i.val
  · intro i j
    have hb' : b ≠ 0 := by have hi := i.isLt; omega
    exact hQ i.val _ (hw hb' j)

def clearSlots {D : ℕ} (P : Fin D → Prop) :
    (ps : List (ℕ × ℕ)) → (Fin (ps.map (fun p => p.1+p.2)).sum → Fin D) → Prop
  | [], _ => True
  | (a,b)::ps, w =>
      (b ≠ 0 → ∀ i : Fin a,
        P ((leftWord finSumFinEquiv.symm w) (Fin.castAdd b i))) ∧
      clearSlots P ps (rightWord finSumFinEquiv.symm w)

theorem blocks_factor_of_clearSlots {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hQ : ∀ i c, P c → Q i c = 0)
    (w : Fin (ps.map (fun p => p.1+p.2)).sum → Fin D) (hw : clearSlots P ps w) :
    blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q) w =
      positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
        (blocks (ps.map Prod.snd) Q) w := by
  rw [blocks_eq_tensorList Prod.fst, blocks_eq_tensorList Prod.snd, tensorList_split,
    blocks_eq_tensorList (fun p : ℕ × ℕ => p.1+p.2)]
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    have hl := joinedFlag_column_factor N Q P (ha (a,b) (by simp))
      (hb (a,b) (by simp)) hQ (leftWord finSumFinEquiv.symm w) hw.1
    have hr := ih (fun p hp => ha p (by simp [hp]))
      (fun p hp => hb p (by simp [hp])) (rightWord finSumFinEquiv.symm w) hw.2
    change wedge (a+b) (joinedFlag d N Q) _ * _ =
      (wedge a N _ * wedge b Q _) * _
    erw [hl,hr]
    rfl

theorem blocks_pair_factor_of_clearSlots {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hQ : ∀ i c, P c → Q i c = 0)
    (z : WordSpace (ps.map (fun p => p.1+p.2)).sum D)
    (hz : ∀ w, z w ≠ 0 → clearSlots P ps w) :
    dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z =
      dotProduct (positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
        (blocks (ps.map Prod.snd) Q)) z := by
  apply Finset.sum_congr rfl
  intro w hw
  by_cases he : z w = 0
  · simp only [he, mul_zero]
  · rw [blocks_factor_of_clearSlots N Q P ps ha hb hQ w (hz w he)]

lemma blocks_alphabet {D : ℕ} (rs : List ℕ) (N : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (hN : ∀ i c, ¬P c → N i c = 0) :
    blocks rs N ∈ alphabetSub rs.sum D P := by
  classical
  intro w hw
  obtain ⟨i,hi⟩ := hw
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro π hπ
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hN _ _ hi)

theorem band_contraction_factor {d D : ℕ} (N Q : ℕ → Fin D → ℂ)
    (P : Fin D → Prop) (ps : List (ℕ × ℕ))
    (ha : ∀ p ∈ ps, p.1 ≤ d) (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d)
    (hN : ∀ i c, ¬P c → N i c = 0) (hQ : ∀ i c, P c → Q i c = 0)
    (z : WordSpace (ps.map (fun p => p.1+p.2)).sum D)
    (hz : ∀ w, z w ≠ 0 → clearSlots P ps w)
    (v : WordSpace (ps.map Prod.fst).sum D) (u : WordSpace (ps.map Prod.snd).sum D)
    (c : ℂ)
    (hsep : coordinateProjection
        (wordSector (fun i => ((splitPositions ps) i).isLeft = true) P) z =
      c • positionProduct (splitPositions ps) v u) :
    dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z =
      c * (dotProduct (blocks (ps.map Prod.fst) N) v *
        dotProduct (blocks (ps.map Prod.snd) Q) u) := by
  classical
  rw [blocks_pair_factor_of_clearSlots N Q P ps ha hb hQ z hz]
  let f := positionProduct (splitPositions ps) (blocks (ps.map Prod.fst) N)
    (blocks (ps.map Prod.snd) Q)
  let S := wordSector (fun i => ((splitPositions ps) i).isLeft = true) P
  have hf : f ∈ coordinateSub _ _ S := positionProduct_sector (splitPositions ps) P _ _
    (blocks_alphabet _ N P hN)
    (blocks_alphabet _ Q (fun a => ¬P a) (fun i a h => hQ i a (not_not.mp h)))
  have he : coordinateProjection S f = f := by
    funext w
    rw [coordinateProjection_apply]
    split_ifs with h
    · rfl
    · exact (hf w h).symm
  change dotProduct f z = _
  rw [← he, coordinateProjection_pair, hsep]
  rw [dotProduct_smul, smul_eq_mul, positionProduct_pair]

end Saxl.FlagColumns
end
end

end OAI
