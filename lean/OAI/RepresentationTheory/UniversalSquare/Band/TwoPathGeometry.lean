import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.SubdiagramSupport
import OAI.RepresentationTheory.UniversalSquare.Band.OddStrip
import OAI.RepresentationTheory.UniversalSquare.Contraction.TwoPathContraction

namespace OAI

/-! Two Path Geometry. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

def appendShortMap (p r q : ℕ) (hq : p+r=q) :
    (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells →
      (ShortColumns.shape q 2).cells :=
  Sum.elim
    (fun c => ⟨(c.val.1, if c.val.2 = p then q else c.val.2), by
      have hc := (ShortColumns.mem_shape p 1 c.val.1 c.val.2).mp c.property
      apply (ShortColumns.mem_shape q 2 _ _).mpr
      split_ifs <;> omega⟩)
    (fun c => ⟨(c.val.1, if c.val.2 = r then q+1 else p+c.val.2), by
      have hc := (ShortColumns.mem_shape r 1 c.val.1 c.val.2).mp c.property
      apply (ShortColumns.mem_shape q 2 _ _).mpr
      split_ifs <;> omega⟩)

lemma appendShortMap_injective (p r q : ℕ) (hq : p+r=q) :
    Function.Injective (appendShortMap p r q hq) := by
  intro x y he
  have hh := congrArg Subtype.val he
  cases x with
  | inl x =>
    have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
    cases y with
    | inl y =>
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      apply congrArg Sum.inl
      apply Subtype.ext
      apply Prod.ext
      · simpa only [appendShortMap, Sum.elim_inl, Sum.elim_inr] using congrArg Prod.fst hh
      · have ht := congrArg Prod.snd hh
        change (if x.val.2 = p then q else x.val.2) =
          (if y.val.2 = p then q else y.val.2) at ht
        split_ifs at ht <;> omega
    | inr y =>
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      have ht := congrArg Prod.snd hh
      change (if x.val.2 = p then q else x.val.2) =
        (if y.val.2 = r then q+1 else p+y.val.2) at ht
      split_ifs at ht <;> omega
  | inr x =>
    have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
    cases y with
    | inl y =>
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      have ht := congrArg Prod.snd hh
      change (if x.val.2 = r then q+1 else p+x.val.2) =
        (if y.val.2 = p then q else y.val.2) at ht
      split_ifs at ht <;> omega
    | inr y =>
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      apply congrArg Sum.inr
      apply Subtype.ext
      apply Prod.ext
      · simpa only [appendShortMap, Sum.elim_inl, Sum.elim_inr] using congrArg Prod.fst hh
      · have ht := congrArg Prod.snd hh
        change (if x.val.2 = r then q+1 else p+x.val.2) =
          (if y.val.2 = r then q+1 else p+y.val.2) at ht
        split_ifs at ht <;> omega

def appendShortCells (p r q : ℕ) (hq : p+r=q) :
    (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells ≃
      (ShortColumns.shape q 2).cells :=
  Equiv.ofBijective (appendShortMap p r q hq)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨appendShortMap_injective p r q hq, by
        rw [Fintype.card_sum, Fintype.card_coe, Fintype.card_coe, Fintype.card_coe]
        change (ShortColumns.shape p 1).card + (ShortColumns.shape r 1).card =
          (ShortColumns.shape q 2).card
        rw [short_card, short_card, short_card]
        omega⟩)

@[simp] lemma appendShortCells_left (p r q : ℕ) (hq : p+r=q)
    (c : (ShortColumns.shape p 1).cells) :
    (appendShortCells p r q hq (Sum.inl c)).val =
      (c.val.1, if c.val.2 = p then q else c.val.2) := rfl

@[simp] lemma appendShortCells_right (p r q : ℕ) (hq : p+r=q)
    (c : (ShortColumns.shape r 1).cells) :
    (appendShortCells p r q hq (Sum.inr c)).val =
      (c.val.1, if c.val.2 = r then q+1 else p+c.val.2) := rfl

lemma appendShortCells_column_same (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape p 1).cells ⊕ (ShortColumns.shape r 1).cells)
    (h : (appendShortCells p r q hq x).val.2 =
      (appendShortCells p r q hq y).val.2) : x.isLeft = y.isLeft := by
  cases x with
  | inl x =>
    cases y with
    | inl y => rfl
    | inr y =>
      have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
      have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
      simp only [appendShortCells_left, appendShortCells_right] at h
      split_ifs at h <;> omega
  | inr x =>
    cases y with
    | inr y => rfl
    | inl y =>
      have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
      have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
      simp only [appendShortCells_left, appendShortCells_right] at h
      split_ifs at h <;> omega

lemma appendShortCells_left_col (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape p 1).cells) :
    (appendShortCells p r q hq (Sum.inl x)).val.2 =
      (appendShortCells p r q hq (Sum.inl y)).val.2 ↔ x.val.2 = y.val.2 := by
  have hx := (ShortColumns.mem_shape p 1 x.val.1 x.val.2).mp x.property
  have hy := (ShortColumns.mem_shape p 1 y.val.1 y.val.2).mp y.property
  simp only [appendShortCells_left]
  split_ifs <;> omega

lemma appendShortCells_right_col (p r q : ℕ) (hq : p+r=q)
    (x y : (ShortColumns.shape r 1).cells) :
    (appendShortCells p r q hq (Sum.inr x)).val.2 =
      (appendShortCells p r q hq (Sum.inr y)).val.2 ↔ x.val.2 = y.val.2 := by
  have hx := (ShortColumns.mem_shape r 1 x.val.1 x.val.2).mp x.property
  have hy := (ShortColumns.mem_shape r 1 y.val.1 y.val.2).mp y.property
  simp only [appendShortCells_right]
  split_ifs <;> omega

def appendShortTableau {n a b : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ShortColumns.shape p 1))
    (t : Tableau b (ShortColumns.shape r 1)) : Tableau n (ShortColumns.shape q 2) :=
  e.trans ((s.sumCongr t).trans (appendShortCells p r q hq))

lemma appendShort_polytabloid {n a b : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin a ⊕ Fin b)
    (s : Tableau a (ShortColumns.shape p 1))
    (t : Tableau b (ShortColumns.shape r 1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (appendShortTableau p r q hq e s t)) =
      positionProduct e
        (letterLift (Fin.castLE (ShortColumns.height_le p 1)) (polytabloid s))
        (letterLift (Fin.castLE (ShortColumns.height_le r 1)) (polytabloid t)) := by
  let T := appendShortTableau p r q hq e s t
  let f := fun i => (T i).val.2
  have hs (i : Fin a) : T (e.symm (Sum.inl i)) =
      appendShortCells p r q hq (Sum.inl (s i)) := by simp [T, appendShortTableau]
  have ht (i : Fin b) : T (e.symm (Sum.inr i)) =
      appendShortCells p r q hq (Sum.inr (t i)) := by simp [T, appendShortTableau]
  have hf : fiberGroup f = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg, ?_⟩
      intro i
      have hh := appendShortCells_column_same p r q hq
        ((s.sumCongr t) (e (g i))) ((s.sumCongr t) (e i)) (hg i)
      have he (i : Fin n) : ((s.sumCongr t) (e i)).isLeft = (e i).isLeft := by
        cases e i <;> rfl
      rw [he, he] at hh
      change (e (g i)).isLeft = true ↔ (e i).isLeft = true
      rw [hh]
    · exact inf_le_left
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (T (e.symm (Sum.inl (g i)))).val.2 =
      (T (e.symm (Sum.inl i))).val.2) ↔ (∀ i, (s (g i)).val.2 = (s i).val.2)
    simp only [hs, appendShortCells_left_col]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup t := by
    apply Subgroup.ext
    intro g
    change (∀ i, (T (e.symm (Sum.inr (g i)))).val.2 =
      (T (e.symm (Sum.inr i))).val.2) ↔ (∀ i, (t (g i)).val.2 = (t i).val.2)
    simp only [ht, appendShortCells_right_col]
  rw [polytabloid_eq_altWord, letterLift_altWord]
  change altWord (fiberGroup f) _ = _
  rw [hf, altWord_fiber_split, hl, hr,
    polytabloid_eq_altWord, polytabloid_eq_altWord, letterLift_altWord, letterLift_altWord]
  congr 2
  · funext i
    apply Fin.ext
    change (T (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [hs]
    rfl
  · funext i
    apply Fin.ext
    change (T (e.symm (Sum.inr i))).val.1 = (t i).val.1
    rw [ht]
    rfl

def twoPathLeft {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    Tableau n (ShortColumns.shape q 2) :=
  appendShortTableau p r q hq e (neighborLayer p) (neighborLayer r)

def twoPathRight {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    Tableau n (ShortColumns.shape q 2) :=
  appendShortTableau r p q (by omega) (e.trans (Equiv.sumComm _ _))
    (Fin.revPerm.trans (neighborLayer r)) (Fin.revPerm.trans (neighborLayer p))

lemma appendShortCells_left_neighbor (p r q : ℕ) (hq : p+r=q)
    (i : Fin (2*p+1)) :
    (appendShortCells p r q hq (Sum.inl (neighborLayer p i))).val.2 =
      if i.val = 0 then q else p-1-(i.val-1)/2 := by
  rw [appendShortCells_left, neighborLayer_col]
  have hi := i.isLt
  split_ifs <;> omega

lemma appendShortCells_right_neighbor (p r q : ℕ) (hq : p+r=q)
    (i : Fin (2*r+1)) :
    (appendShortCells p r q hq (Sum.inr (neighborLayer r i))).val.2 =
      if i.val = 0 then q+1 else p+(r-1-(i.val-1)/2) := by
  rw [appendShortCells_right, neighborLayer_col]
  have hi := i.isLt
  split_ifs <;> omega

lemma twoPathLeft_col_left {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*p+1)) :
    (twoPathLeft p r q hq e (e.symm (Sum.inl i))).val.2 =
      if i.val = 0 then q else p-1-(i.val-1)/2 := by
  simp only [twoPathLeft, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inl]
  exact appendShortCells_left_neighbor p r q hq i

lemma twoPathLeft_col_right {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*r+1)) :
    (twoPathLeft p r q hq e (e.symm (Sum.inr i))).val.2 =
      if i.val = 0 then q+1 else p+(r-1-(i.val-1)/2) := by
  simp only [twoPathLeft, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumCongr_apply, Sum.map_inr]
  exact appendShortCells_right_neighbor p r q hq i

lemma twoPathRight_col_left {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*p+1)) :
    (twoPathRight p r q hq e (e.symm (Sum.inl i))).val.2 =
      if i.rev.val = 0 then q+1 else r+(p-1-(i.rev.val-1)/2) := by
  simp only [twoPathRight, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumComm_apply, Sum.swap_inl,
    Equiv.sumCongr_apply, Sum.map_inr]
  exact appendShortCells_right_neighbor r p q (by omega) i.rev

lemma twoPathRight_col_right {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) (i : Fin (2*r+1)) :
    (twoPathRight p r q hq e (e.symm (Sum.inr i))).val.2 =
      if i.rev.val = 0 then q else r-1-(i.rev.val-1)/2 := by
  simp only [twoPathRight, appendShortTableau, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.sumComm_apply, Sum.swap_inr,
    Equiv.sumCongr_apply, Sum.map_inl]
  exact appendShortCells_left_neighbor r p q (by omega) i.rev

theorem twoPath_outputs {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    inOutputs (Set.Icc q (2*q+3))
      (mergeWords (rowWord (transposeTableau (twoPathLeft p r q hq e)))
        (rowWord (transposeTableau (twoPathRight p r q hq e)))) := by
  intro i
  simp only [output, mergeWords, Equiv.symm_apply_apply]
  change (twoPathLeft p r q hq e i).val.2 +
    (twoPathRight p r q hq e i).val.2 + 1 ∈ Set.Icc q (2*q+3)
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    rw [twoPathLeft_col_left, twoPathRight_col_left]
    simp only [Set.mem_Icc, Fin.val_rev]
    have hj := j.isLt
    split_ifs <;> omega
  | inr j =>
    rw [twoPathLeft_col_right, twoPathRight_col_right]
    simp only [Set.mem_Icc, Fin.val_rev]
    have hj := j.isLt
    split_ifs <;> omega

lemma positionProduct_swap {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionProduct (e.trans (Equiv.sumComm _ _)) y x = positionProduct e x y := by
  funext w
  exact mul_comm _ _

lemma neighborLayer_reverse_word (r : ℕ) :
    letterLift (Fin.castLE (ShortColumns.height_le r 1))
      (polytabloid (Fin.revPerm.trans (neighborLayer r))) =
        wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r) := by
  rw [polytabloid_move (neighborLayer r) (Fin.revPerm.trans (neighborLayer r))]
  have he : tableauMove (neighborLayer r) (Fin.revPerm.trans (neighborLayer r)) =
      Fin.revPerm := by
    apply Equiv.ext
    intro i
    simp only [tableauMove, Equiv.trans_apply, Equiv.symm_trans_apply,
      Equiv.symm_apply_apply]
    rfl
  rw [he, Representation.IntertwiningMap.isIntertwining, neighborLayer_polytabloid]

lemma twoPathLeft_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (twoPathLeft p r q hq e)) =
        positionProduct e (PathLayer.rowAlt p) (PathLayer.rowAlt r) := by
  rw [twoPathLeft, appendShort_polytabloid,
    neighborLayer_polytabloid, neighborLayer_polytabloid]

lemma twoPathRight_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    letterLift (Fin.castLE (ShortColumns.height_le q 2))
      (polytabloid (twoPathRight p r q hq e)) =
        positionProduct e (wordRep (2*p+1) 2 Fin.revPerm (PathLayer.rowAlt p))
          (wordRep (2*r+1) 2 Fin.revPerm (PathLayer.rowAlt r)) := by
  rw [twoPathRight, appendShort_polytabloid,
    neighborLayer_reverse_word, neighborLayer_reverse_word, positionProduct_swap]

def twoPathLetter (q : ℕ) :
    Fin ((ShortColumns.shape q 2).transpose.transpose.colLen 0) → Fin 2 :=
  (Fin.castLE (ShortColumns.height_le q 2)) ∘ Fin.cast
    (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose (ShortColumns.shape q 2)))

lemma twoPath_doubleTranspose_word {n : ℕ} (q : ℕ)
    (t : Tableau n (ShortColumns.shape q 2)) :
    letterLift (twoPathLetter q) (polytabloid (transposeTableau (transposeTableau t))) =
      letterLift (Fin.castLE (ShortColumns.height_le q 2)) (polytabloid t) := by
  rw [twoPathLetter, letterLift_comp]
  change letterLift _ (letterLift _ (polytabloid (transposeTableau (transposeTableau t)))) = _
  rw [polytabloid_doubleTranspose]

lemma twoPath_pair_word {n : ℕ} (p r q : ℕ) (hq : p+r=q)
    (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    pairWordMap (letterLift (twoPathLetter q)) (letterLift (twoPathLetter q))
      (wordTensor _ _ _
        (polytabloid (transposeTableau (transposeTableau (twoPathLeft p r q hq e))) ⊗ₜ[ℂ]
          polytabloid (transposeTableau (transposeTableau (twoPathRight p r q hq e))))) =
      (-1 : ℂ)^q • positionProduct e (Path.bandWord p) (Path.bandWord r) := by
  rw [pairWordMap_tensor, twoPath_doubleTranspose_word, twoPath_doubleTranspose_word,
    twoPathLeft_word, twoPathRight_word]
  funext w
  rw [wordTensor_tmul]
  change (PathLayer.rowAlt p (leftWord e (splitLeft w)) *
      PathLayer.rowAlt r (rightWord e (splitLeft w))) *
    (PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev) *
      PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev)) =
    (-1 : ℂ)^q * (Path.bandWord p (leftWord e w) * Path.bandWord r (rightWord e w))
  have hp := PathLayer.paired_rowAlt p (leftWord e w)
  have hr := PathLayer.paired_rowAlt r (rightWord e w)
  change PathLayer.rowAlt p (leftWord e (splitLeft w)) *
    PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev) = _ at hp
  change PathLayer.rowAlt r (rightWord e (splitLeft w)) *
    PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev) = _ at hr
  calc
    _ = (PathLayer.rowAlt p (leftWord e (splitLeft w)) *
        PathLayer.rowAlt p (leftWord e (splitRight w) ∘ Fin.rev)) *
      (PathLayer.rowAlt r (rightWord e (splitLeft w)) *
        PathLayer.rowAlt r (rightWord e (splitRight w) ∘ Fin.rev)) := by ring
    _ = _ := by rw [hp, hr, ← hq, pow_add]; ring

theorem two_paths (q : ℕ)
    (a b : Tableau (2*q+2) (ShortColumns.shape q 2).transpose)
    (μ : YoungDiagram) (t : Tableau (2*q+2) μ) (hμ : μ.colLen 0 ≤ 4)
    (ho : ∃ j, μ.colLen j % 2 = 1) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (projectedSpechtTensor a b (inOutputs (Set.Icc q (2*q+3)))
        (inOutputs_invariant (Set.Icc q (2*q+3)))).toRepresentation,
      Function.Injective F := by
  have hn : μ.card = 2*q+2 := by
    have h := Fintype.card_congr t
    simpa only [Fintype.card_fin, Fintype.card_coe] using h.symm
  obtain ⟨p,rs,hpq,hp,hrs,hr,hc⟩ := Columns.odd_column_split q μ hn hμ ho
  let r := q-p
  have hrq : p+r=q := by omega
  have heq : 2*q+2 = (2*p+1)+(2*r+1) := by omega
  let e : Fin (2*q+2) ≃ Fin (2*p+1) ⊕ Fin (2*r+1) :=
    (finCongr heq).trans finSumFinEquiv.symm
  let s := transposeTableau (twoPathLeft p r q hrq e)
  let u := transposeTableau (twoPathRight p r q hrq e)
  let D := pairWordMap (n := 2*q+2)
    (letterLift (twoPathLetter q)) (letterLift (twoPathLetter q))
  let v := wordTensor _ _ _
    (polytabloid (transposeTableau s) ⊗ₜ[ℂ] polytabloid (transposeTableau u))
  have hs : ∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep (2*q+2) 4) (D v)).toRepresentation, f ≠ 0 := by
    dsimp only [D, v, s, u]
    rw [twoPath_pair_word, cyclic_smul_eq _ _ _ (pow_ne_zero q (by norm_num))]
    exact Columns.two_path_cyclic_support_placed p r rs hp hrs hr μ hc t e
  obtain ⟨f,hf⟩ := hs
  obtain ⟨g,hg⟩ := cyclic_projection_support D v f hf
  exact projectedTensor_support_of_coordinate a s b u t _ _
    (twoPath_outputs p r q hrq e) g hg

end Saxl.Balance
end
end

end OAI
