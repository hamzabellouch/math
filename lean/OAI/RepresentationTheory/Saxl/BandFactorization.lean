import OAI.RepresentationTheory.Saxl.PositionSplit

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

def highPositionsEquiv (h s : ℕ) :
    {i : Fin (staircase (h+s)).card // stairHigh h s i} ≃ Fin (staircase h).card where
  toFun i := (stairTableau h).symm ⟨(stairTableau (h+s) i.val).val, mem_staircase.mpr i.property⟩
  invFun j := ⟨(stairTableau (h+s)).symm ⟨(stairTableau h j).val, by
    apply mem_staircase.mpr
    have := mem_staircase.mp (stairTableau h j).property
    omega⟩, by
      change ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.1 +
        ((stairTableau (h+s)) ((stairTableau (h+s)).symm _)).val.2 < h
      simp only [Equiv.apply_symm_apply]
      exact mem_staircase.mp (stairTableau h j).property⟩
  left_inv i := by apply Subtype.ext; simp
  right_inv i := by simp

abbrev bandSize (h s : ℕ) := Nat.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i}

def cutPositions (h s : ℕ) :
    Fin (staircase (h+s)).card ≃ Fin (staircase h).card ⊕ Fin (bandSize h s) := by
  classical
  exact (Equiv.sumCompl (stairHigh h s)).symm.trans
    (Equiv.sumCongr (highPositionsEquiv h s) (Fintype.equivFinOfCardEq (show Fintype.card {i : Fin (staircase (h+s)).card // ¬stairHigh h s i} = bandSize h s from Fintype.card_eq_nat_card)))

lemma cutPositions_high (h s : ℕ) (i : Fin (staircase (h+s)).card) :
    (cutPositions h s i).isLeft = true ↔ stairHigh h s i := by
  classical
  by_cases hi : stairHigh h s i <;> simp [cutPositions, Equiv.sumCompl, Equiv.sumCongr, hi]

lemma cutPositions_left (h s : ℕ) (i : Fin (staircase h).card) :
    (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val = (stairTableau h i).val := by
  classical
  simp [cutPositions, Equiv.sumCompl, highPositionsEquiv]

lemma bandSize_add (h s : ℕ) : (staircase h).card + bandSize h s = (staircase (h+s)).card := by
  have hh := Fintype.card_congr (cutPositions h s)
  simpa using hh.symm

def bandTableau (h s : ℕ) (j : Fin (bandSize h s)) : (staircase (h+s)).cells :=
  stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))

def bandRowGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.1)
def bandColumnGroup (h s : ℕ) := fiberGroup (fun j => (bandTableau h s j).val.2)

def highLetter (h s : ℕ) : Fin ((staircase h).colLen 0) → Fin ((staircase (h+s)).colLen 0) :=
  fun a => ⟨a.val+s, by have := a.isLt; simp only [staircase_colLen, Nat.sub_zero] at *; omega⟩

def letterLift {n d e : ℕ} (f : Fin d → Fin e) :
    Representation.IntertwiningMap (wordRep n d) (wordRep n e) :=
  wordMap (fun a b => if f a = b then 1 else 0)

lemma letterLift_single {n d e : ℕ} (f : Fin d → Fin e) (a : Fin n → Fin d) :
    letterLift f (Pi.single a 1) = Pi.single (f ∘ a) (1:ℂ) := by
  classical
  ext b
  rw [letterLift, wordMap_single, Pi.single_apply]
  by_cases he : b = f ∘ a
  · subst b; simp
  · rw [ite_eq_right he]
    have hn : ∃ i, f (a i) ≠ b i := by
      by_contra hh
      push Not at hh
      exact he (funext (fun i => (hh i).symm))
    obtain ⟨i,hi⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

lemma letterLift_altWord {n d e : ℕ} (f : Fin d → Fin e)
    (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    letterLift f (altWord G a) = altWord G (f ∘ a) := by
  classical
  unfold altWord
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g hg
  rw [map_smul, Representation.IntertwiningMap.isIntertwining, letterLift_single]

def bandRowWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandRowGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)))

def bandColumnWord (h s : ℕ) : WordSpace (bandSize h s) ((staircase (h+s)).colLen 0) :=
  altWord (bandColumnGroup h s) (rightWord (cutPositions h s)
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)))

lemma row_cut_group (h s : ℕ) :
    columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.1) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma column_cut_group (h s : ℕ) :
    columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s) =
      fiberGroup (fun i => (stairTableau (h+s) i).val.2) ⊓
        sectorGroup (fun i => (cutPositions h s i).isLeft = true) := by
  congr 1
  congr 1; funext i; exact propext (cutPositions_high h s i).symm

lemma highRow_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairRowTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap, highLetter]
  change (rotateRow h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.2 = _
  change (if _ then _ else _) = (stairTableau h i).val.2+s
  rw [he]
  rw [ite_eq_left (by omega)]

lemma highColumn_word (h s : ℕ) :
    leftWord (cutPositions h s) (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _)) =
      highLetter h s ∘ rowWord (stairTableau h) := by
  funext i
  apply Fin.ext
  have hi : (stairTableau h i).val.1 + (stairTableau h i).val.2 < h :=
    mem_staircase.mp (stairTableau h i).property
  have he := cutPositions_left h s i
  simp only [leftWord, Function.comp_apply, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, highLetter]
  change (rotateColumn h s (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i)))).val.1 = _
  change (if (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 <
      h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2 then
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1+s else
      (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.1 -
        (h - (stairTableau (h+s) ((cutPositions h s).symm (Sum.inl i))).val.2)) = _
  simp only [he]
  rw [ite_eq_left (by omega)]

/- The first-layer exact band factorization, including the high-letter shift. -/
theorem cutRowWord_factor (h s : ℕ) : cutRowWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairRowTableau h))) (bandRowWord h s) := by
  unfold cutRowWord
  rw [row_cut_group, altWord_fiber_split]
  congr 1
  rw [highRow_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.1)
  congr 1
  funext i
  exact congrArg Prod.fst (cutPositions_left h s i)

/- The second-layer exact band factorization. -/
theorem cutColumnWord_factor (h s : ℕ) : cutColumnWord h s =
    positionProduct (cutPositions h s)
      (letterLift (highLetter h s) (polytabloid (stairTableau h))) (bandColumnWord h s) := by
  unfold cutColumnWord
  rw [column_cut_group, altWord_fiber_split]
  congr 1
  rw [highColumn_word, polytabloid_eq_altWord, letterLift_altWord]
  congr 1
  change fiberGroup _ = fiberGroup (fun i => (stairTableau h i).val.2)
  congr 1
  funext i
  exact congrArg Prod.snd (cutPositions_left h s i)



lemma bandTableau_bounds (h s : ℕ) (j : Fin (bandSize h s)) :
    h ≤ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 ∧
      (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h+s := by
  refine ⟨?_,mem_staircase.mp (bandTableau h s j).property⟩
  have hh := cutPositions_high h s ((cutPositions h s).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hh
  change ¬ (bandTableau h s j).val.1 + (bandTableau h s j).val.2 < h at hh
  omega

def bandCellsEquiv (h s : ℕ) : Fin (bandSize h s) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} :=
  Equiv.ofBijective (fun j => ⟨(bandTableau h s j).val,bandTableau_bounds h s j⟩) (by
    constructor
    · intro i j hij
      have hh : bandTableau h s i = bandTableau h s j := Subtype.ext (congrArg (fun c : {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+s} => c.val) hij)
      exact Sum.inr.inj ((cutPositions h s).symm.injective ((stairTableau (h+s)).injective hh))
    · intro c
      let x : (staircase (h+s)).cells := ⟨c.val,mem_staircase.mpr c.property.2⟩
      let i := (stairTableau (h+s)).symm x
      have hi : ¬ stairHigh h s i := by
        change ¬ (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.1 +
          (stairTableau (h+s) ((stairTableau (h+s)).symm x)).val.2 < h
        simp only [Equiv.apply_symm_apply]
        exact Nat.not_lt.mpr c.property.1
      have he := cutPositions_high h s i
      cases hp : cutPositions h s i with
      | inl j => simp only [hp, Sum.isLeft_inl, true_iff] at he; exact False.elim (hi he)
      | inr j =>
        refine ⟨j, ?_⟩
        apply Subtype.ext
        have hj : (cutPositions h s).symm (Sum.inr j) = i := by rw [← hp,Equiv.symm_apply_apply]
        change (stairTableau (h+s) ((cutPositions h s).symm (Sum.inr j))).val = c.val
        rw [hj]
        exact congrArg Subtype.val ((stairTableau (h+s)).apply_symm_apply x))

def pathCellsEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃
    {c : ℕ × ℕ // h ≤ c.1+c.2 ∧ c.1+c.2 < h+2} where
  toFun k := ⟨(h+1-(k.val+1)/2,k.val/2), by have := k.isLt; omega⟩
  invFun c := ⟨h+1-c.val.1+c.val.2, by have := c.property; omega⟩
  left_inv k := by apply Fin.ext; dsimp; have := k.isLt; omega
  right_inv c := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> have := c.property <;> omega

/- The exact path order, starting at the bottom row singleton and ending
at the rightmost column singleton. -/
def bandPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  (pathCellsEquiv h).trans (bandCellsEquiv h 2).symm

lemma bandPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandPathEquiv h k)).val = (h+1-(k.val+1)/2,k.val/2) := by
  have hh := (bandCellsEquiv h 2).apply_symm_apply (pathCellsEquiv h k)
  exact congrArg Subtype.val hh

lemma bandPath_card (h : ℕ) : bandSize h 2 = 2*(h+1)+1 := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (bandPathEquiv h)).symm

end Saxl

end

end OAI
