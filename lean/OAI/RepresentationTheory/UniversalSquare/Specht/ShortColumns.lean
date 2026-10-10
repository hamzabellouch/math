import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SingletonForms

namespace OAI

/-! Short Columns. -/

section

noncomputable section
open scoped TensorProduct

namespace Saxl.ShortColumns

def shape (b δ : ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens [b+δ,b] (by apply List.Pairwise.sortedGE; simp)

lemma mem_shape (b δ i j : ℕ) :
    (i,j) ∈ shape b δ ↔ (i = 0 ∧ j < b+δ) ∨ (i = 1 ∧ j < b) := by
  simp only [shape, YoungDiagram.mem_ofRowLens, List.length_cons, List.length_nil]
  constructor
  · rintro ⟨h,hj⟩
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl <;> simp_all
  · rintro (⟨rfl,h⟩ | ⟨rfl,h⟩) <;> simp_all

lemma height_le (b δ : ℕ) : (shape b δ).colLen 0 ≤ 2 := by
  by_contra h
  have hm : (2,0) ∈ shape b δ := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  simp only [mem_shape] at hm
  omega

def oddTableau (b : ℕ) : Tableau (2*b+1) (shape b 1) where
  toFun i := if hi : i.val = 0 then ⟨(0,b), (mem_shape b 1 0 b).mpr (Or.inl ⟨rfl, by omega⟩)⟩
    else ⟨((i.val+1)%2,(i.val-1)/2), (mem_shape _ _ _ _).mpr (by
      have ht := i.isLt
      rcases Nat.mod_two_eq_zero_or_one (i.val+1) with h | h
      · exact Or.inl ⟨h, by omega⟩
      · exact Or.inr ⟨h, by omega⟩)⟩
  invFun c := if h : c.val.2 = b then ⟨0,by omega⟩ else
    ⟨2*c.val.2+c.val.1+1, by
      have hc := (mem_shape b 1 c.val.1 c.val.2).mp c.property
      change 2*c.val.2+c.val.1+1 < 2*b+1
      change c.val.2 ≠ b at h
      omega⟩
  left_inv i := by
    dsimp only
    by_cases hi : i.val = 0
    · simp only [dite_eq_left hi, dite_true]
      apply Fin.ext
      exact hi.symm
    · simp only [dite_eq_right hi]
      have hj : (i.val-1)/2 ≠ b := by have ht := i.isLt; omega
      simp only [dite_eq_right hj]
      apply Fin.ext
      dsimp only
      omega
  right_inv c := by
    have hc := (mem_shape b 1 c.val.1 c.val.2).mp c.property
    dsimp only
    by_cases h : c.val.2 = b
    · simp only [dite_eq_left h, dite_true]
      apply Subtype.ext
      apply Prod.ext <;> dsimp only <;> omega
    · simp only [dite_eq_right h]
      have h' : 2*c.val.2+c.val.1+1 ≠ 0 := by omega
      simp only [dite_eq_right h']
      apply Subtype.ext
      apply Prod.ext <;> dsimp only <;> omega

lemma oddTableau_row (b : ℕ) (i : Fin (2*b+1)) :
    ((oddTableau b) i).val.1 = (PathLayer.base i).val := by
  simp only [oddTableau, Equiv.coe_fn_mk, PathLayer.base]
  split_ifs <;> rfl

lemma oddTableau_col_iff (b : ℕ) (i j : Fin (2*b+1)) :
    ((oddTableau b) i).val.2 = ((oddTableau b) j).val.2 ↔
      PathLayer.tag i = PathLayer.tag j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [oddTableau, Equiv.coe_fn_mk, PathLayer.tag]
  split_ifs <;> dsimp only <;> omega

lemma oddTableau_group (b : ℕ) :
    columnGroup (oddTableau b) = fiberGroup (@PathLayer.tag b) := by
  apply Subgroup.ext
  intro g
  change (∀ i, ((oddTableau b) (g i)).val.2 = ((oddTableau b) i).val.2) ↔ _
  simp only [oddTableau_col_iff]
  rfl

lemma oddTableau_polytabloid (b : ℕ) :
    letterLift (Fin.castLE (height_le b 1)) (polytabloid (oddTableau b)) =
      PathLayer.rowAlt b := by
  rw [polytabloid_eq_altWord, letterLift_altWord, oddTableau_group]
  congr 1
  funext i
  apply Fin.ext
  exact oddTableau_row b i

def oddSplit (b : ℕ) : Fin (2*b+1) ≃ Fin (2*b) ⊕ Fin 1 :=
  (finCongr (by omega : 2*b+1 = 1+2*b)).trans <|
  (finSumFinEquiv : Fin 1 ⊕ Fin (2*b) ≃ Fin (1+2*b)).symm.trans
    (Equiv.sumComm _ _)

@[simp] lemma oddSplit_left (b : ℕ) (i : Fin (2*b)) :
    ((oddSplit b).symm (Sum.inl i)).val = i.val+1 := by
  change 1+i.val = i.val+1
  omega

@[simp] lemma oddSplit_right (b : ℕ) :
    (oddSplit b).symm (Sum.inr (0 : Fin 1)) = 0 := rfl

def pairSplit (b : ℕ) : Fin (2*b) ≃ Fin b ⊕ Fin b where
  toFun i := if h : i.val % 2 = 0 then Sum.inl ⟨i.val/2, by omega⟩
    else Sum.inr ⟨i.val/2, by omega⟩
  invFun := Sum.elim (fun i => ⟨2*i.val,by omega⟩) (fun i => ⟨2*i.val+1,by omega⟩)
  left_inv i := by
    dsimp only
    split_ifs <;> apply Fin.ext <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega
  right_inv i := by
    cases i with
    | inl i => simp
    | inr i =>
      simp
      apply Fin.ext
      dsimp only
      omega

@[simp] lemma pairSplit_left (b : ℕ) (i : Fin b) :
    ((pairSplit b).symm (Sum.inl i)).val = 2*i.val := rfl

@[simp] lemma pairSplit_right (b : ℕ) (i : Fin b) :
    ((pairSplit b).symm (Sum.inr i)).val = 2*i.val+1 := rfl

lemma shortPairForm_eq (i j : Fin 4) :
    shortPairForm i j = PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).1 *
      PathLayer.J ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm j).2 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [shortPairForm, PathLayer.J, finProdFinEquiv, Fin.divNat, Fin.modNat]

lemma singleton_square (i : Fin 4) :
    (if ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).1 = (0 : Fin 2) then (1 : ℂ) else 0) *
      (if ((finProdFinEquiv : Fin 2 × Fin 2 ≃ Fin 4).symm i).2 = 0 then 1 else 0) =
      (Pi.single 0 1 : Fin 4 → ℂ) i := by
  fin_cases i <;>
    norm_num [finProdFinEquiv, Fin.divNat, Fin.modNat, Pi.single_apply, Fin.ext_iff]

lemma odd_square (b : ℕ) :
    wordTensor (2*b+1) 2 2 (PathLayer.rowAlt b ⊗ₜ[ℂ] PathLayer.rowAlt b) =
      pairSingletonTensor (oddSplit b) (pairSplit b) shortPairForm (Pi.single 0 1) := by
  funext w
  rw [wordTensor_tmul, PathLayer.rowAlt_formula, PathLayer.rowAlt_formula]
  have hp (i : Fin b) :
      leftWord (pairSplit b) (leftWord (oddSplit b) w) i =
        w ⟨2*i.val+1,by omega⟩ ∧
      rightWord (pairSplit b) (leftWord (oddSplit b) w) i =
        w ⟨2*i.val+2,by omega⟩ := by
    constructor <;> apply congrArg w <;> apply Fin.ext <;>
      simp only [oddSplit_left, pairSplit_left, pairSplit_right]
  change (if splitLeft w 0 = 0 then (1 : ℂ) else 0) * _ *
    ((if splitRight w 0 = 0 then 1 else 0) * _) =
    (∏ i, shortPairForm (leftWord (pairSplit b) (leftWord (oddSplit b) w) i)
      (rightWord (pairSplit b) (leftWord (oddSplit b) w) i)) *
      (Pi.single 0 1 : Fin 4 → ℂ) (rightWord (oddSplit b) w 0)
  simp_rw [(hp _).1, (hp _).2, shortPairForm_eq]
  simp only [Finset.prod_mul_distrib, rightWord, oddSplit_right, splitLeft, splitRight]
  rw [← singleton_square]
  ac_rfl

def evenTableau (b : ℕ) : Tableau (2*b) (shape b 0) where
  toFun i := ⟨(i.val%2,i.val/2), (mem_shape b 0 _ _).mpr (by
    have ht := i.isLt
    rcases Nat.mod_two_eq_zero_or_one i.val with h | h
    · exact Or.inl ⟨h,by omega⟩
    · exact Or.inr ⟨h,by omega⟩)⟩
  invFun c := ⟨2*c.val.2+c.val.1, by
    have hc := (mem_shape b 0 c.val.1 c.val.2).mp c.property
    omega⟩
  left_inv i := by apply Fin.ext; dsimp only; omega
  right_inv c := by
    have hc := (mem_shape b 0 c.val.1 c.val.2).mp c.property
    apply Subtype.ext
    apply Prod.ext <;> dsimp only <;> omega

def evenAlt (b : ℕ) : WordSpace (2*b) 2 :=
  altWord (fiberGroup (fun i : Fin (2*b) => i.val/2))
    (fun i => ⟨i.val%2,Nat.mod_lt _ (by omega)⟩)

lemma evenTableau_polytabloid (b : ℕ) :
    letterLift (Fin.castLE (height_le b 0)) (polytabloid (evenTableau b)) = evenAlt b := by
  rw [polytabloid_eq_altWord, letterLift_altWord]
  rfl

def appendEven (b : ℕ) : Fin (2*(b+1)) ≃ Fin (2*b) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(b+1) = 2*b+2)).trans finSumFinEquiv.symm

@[simp] lemma appendEven_left (b : ℕ) (i : Fin (2*b)) :
    ((appendEven b).symm (Sum.inl i)).val = i.val := rfl
@[simp] lemma appendEven_right (b : ℕ) (i : Fin 2) :
    ((appendEven b).symm (Sum.inr i)).val = 2*b+i.val := rfl

lemma evenAlt_step (b : ℕ) :
    evenAlt (b+1) = positionProduct (appendEven b) (evenAlt b)
      (altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  have hs (i : Fin (2*(b+1))) :
      (appendEven b i).isLeft = true ↔ i.val/2 < b := by
    obtain ⟨j,rfl⟩ := (appendEven b).symm.surjective i
    cases j with
    | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff,
        appendEven_left]; omega
    | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true,
        appendEven_right, false_iff]; omega
  have hg : fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) =
      fiberGroup (fun i : Fin (2*(b+1)) => i.val/2) ⊓
        sectorGroup (fun i => (appendEven b i).isLeft = true) := by
    apply le_antisymm
    · intro g hg
      refine ⟨hg, ?_⟩
      intro i
      change (appendEven b (g i)).isLeft = true ↔ (appendEven b i).isLeft = true
      rw [hs,hs]
      exact congrArg (fun k => k < b) (hg i) |>.to_iff
    · exact inf_le_left
  have hr : fiberGroup (fun i : Fin 2 => ((appendEven b).symm (Sum.inr i)).val/2) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, _ = _) ↔ True
    simp only [appendEven_right]
    constructor
    · intro _; trivial
    · intro _ i; have hi := i.isLt; have hgi := (g i).isLt; omega
  unfold evenAlt
  rw [hg, altWord_fiber_split, hr]
  congr 2
  funext i
  apply Fin.ext
  change (2*b+i.val)%2 = i.val
  omega

lemma evenAlt_zero (w : Fin 0 → Fin 2) : evenAlt 0 w = 1 := by
  classical
  let := Fintype.ofFinite (fiberGroup (fun i : Fin (2*0) => i.val/2))
  have hu : (Finset.univ : Finset (fiberGroup (fun i : Fin (2*0) => i.val/2))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  unfold evenAlt altWord
  rw [hu, Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (fun i : Fin 0 => (⟨i.val%2, _⟩ : Fin 2)) (1 : ℂ) : WordSpace 0 2) w = 1
  rw [Pi.single_apply, ite_eq_left (Subsingleton.elim _ _)]

lemma evenAlt_formula (b : ℕ) (w : Fin (2*b) → Fin 2) :
    evenAlt b w = ∏ i : Fin b,
      PathLayer.J (w ⟨2*i.val,by omega⟩) (w ⟨2*i.val+1,by omega⟩) := by
  induction b with
  | zero => simpa using evenAlt_zero w
  | succ b ih =>
    rw [evenAlt_step]
    change evenAlt b (leftWord (appendEven b) w) *
      altWord ⊤ (fun i : Fin 2 => i) (rightWord (appendEven b) w) = _
    rw [ih, PathLayer.pair_alt, Fin.prod_univ_castSucc]
    rfl

lemma even_square (b : ℕ) :
    wordTensor (2*b) 2 2 (evenAlt b ⊗ₜ[ℂ] evenAlt b) =
      pairFormTensor (pairSplit b) shortPairForm := by
  funext w
  rw [wordTensor_tmul, evenAlt_formula, evenAlt_formula]
  change (∏ i : Fin b, _) * (∏ i : Fin b, _) =
    ∏ i, shortPairForm (leftWord (pairSplit b) w i) (rightWord (pairSplit b) w i)
  simp only [shortPairForm_eq, leftWord, rightWord, Finset.prod_mul_distrib,
    splitLeft, splitRight]
  rfl

end Saxl.ShortColumns
end
end

end OAI
