import OAI.RepresentationTheory.Saxl.BandFactorization

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl.PathLayer

def tag {r : ℕ} (i : Fin (2*r+1)) : ℕ := (i.val+1)/2

def base {r : ℕ} (i : Fin (2*r+1)) : Fin 2 := if i.val=0 then 0 else ⟨(i.val+1)%2, Nat.mod_lt _ (by omega)⟩

def rowAlt (r : ℕ) : Saxl.WordSpace (2*r+1) 2 :=
  Saxl.altWord (Saxl.fiberGroup (@tag r)) (@base r)

def appendPair (r : ℕ) : Fin (2*(r+1)+1) ≃ Fin (2*r+1) ⊕ Fin 2 :=
  (finCongr (by omega : 2*(r+1)+1 = (2*r+1)+2)).trans finSumFinEquiv.symm

@[simp] lemma appendPair_left (r : ℕ) (i : Fin (2*r+1)) :
    ((appendPair r).symm (Sum.inl i)).val = i.val := rfl
@[simp] lemma appendPair_right (r : ℕ) (i : Fin 2) :
    ((appendPair r).symm (Sum.inr i)).val = 2*r+1+i.val := rfl

lemma tag_left (r : ℕ) (i : Fin (2*r+1)) :
    tag ((appendPair r).symm (Sum.inl i)) = tag i := rfl
lemma tag_right (r : ℕ) (i : Fin 2) :
    tag ((appendPair r).symm (Sum.inr i)) = r+1 := by
  unfold tag
  rw [appendPair_right]
  omega

lemma tag_side (r : ℕ) (i : Fin (2*(r+1)+1)) :
    (appendPair r i).isLeft = true ↔ tag i < r+1 := by
  obtain ⟨j,rfl⟩ := (appendPair r).symm.surjective i
  cases j with
  | inl j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, true_iff, tag_left]; unfold tag; omega
  | inr j => simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, tag_right, lt_self_iff_false]

lemma rowGroup_sector (r : ℕ) :
    Saxl.fiberGroup (@tag (r+1)) = Saxl.fiberGroup (@tag (r+1)) ⊓
      Saxl.sectorGroup (fun i => (appendPair r i).isLeft = true) := by
  apply le_antisymm
  · intro g hg
    refine ⟨hg, ?_⟩
    intro i
    change (appendPair r (g i)).isLeft = true ↔ (appendPair r i).isLeft = true
    rw [tag_side,tag_side]
    change ∀ i, tag (g i) = tag i at hg
    rw [hg]
  · exact inf_le_left

lemma rowAlt_step (r : ℕ) :
    rowAlt (r+1) = Saxl.positionProduct (appendPair r) (rowAlt r)
      (Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i)) := by
  unfold rowAlt
  rw [rowGroup_sector, Saxl.altWord_fiber_split]
  have hl : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inl i))) =
      Saxl.fiberGroup (@tag r) := rfl
  have hr : Saxl.fiberGroup (fun i => tag ((appendPair r).symm (Sum.inr i))) = ⊤ := by
    apply Subgroup.ext
    intro g
    change (∀ i, tag ((appendPair r).symm (Sum.inr (g i))) = tag ((appendPair r).symm (Sum.inr i))) ↔ True
    simp only [tag_right, implies_true]
  rw [hl,hr]
  congr 2
  funext i
  apply Fin.ext
  change (base ((appendPair r).symm (Sum.inr i))).val = i.val
  have hn : ((appendPair r).symm (Sum.inr i)).val ≠ 0 := by rw [appendPair_right]; omega
  unfold base
  rw [ite_eq_right hn]
  change (2*r+1+i.val+1)%2 = i.val
  omega

def J : Matrix (Fin 2) (Fin 2) ℂ := !![0,1;-1,0]

lemma pair_alt (w : Fin 2 → Fin 2) :
    Saxl.altWord (⊤ : Subgroup (Equiv.Perm (Fin 2))) (fun i => i) w = J (w 0) (w 1) := by
  classical
  let := Fintype.ofFinite (⊤ : Subgroup (Equiv.Perm (Fin 2)))
  unfold Saxl.altWord
  rw [Finset.sum_apply]
  change (∑ g : (⊤ : Subgroup (Equiv.Perm (Fin 2))), Saxl.signC (g : Equiv.Perm (Fin 2)) *
    ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ (g : Equiv.Perm (Fin 2))))) = _
  calc
    _ = ∑ g : Equiv.Perm (Fin 2), Saxl.signC g *
        ((Pi.single (fun i : Fin 2 => i) (1:ℂ) : Saxl.WordSpace 2 2) (w ∘ g)) :=
      Fintype.sum_equiv (Subgroup.topEquiv (G := Equiv.Perm (Fin 2))).toEquiv _ _ (by intro g; rfl)
    _ = _ := by
      have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1,Equiv.swap 0 1} := by decide
      rw [hu]
      have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
      simp only [Finset.sum_insert (Finset.notMem_singleton.mpr hne), Finset.sum_singleton]
      have hw : w = ![w 0,w 1] := by ext i; fin_cases i <;> rfl
      rw [hw]
      generalize h0 : w 0 = a
      generalize h1 : w 1 = b
      fin_cases a <;> fin_cases b <;>
        norm_num [Saxl.wordRep,Saxl.signC_def,Pi.single_apply,funext_iff,Fin.forall_fin_two,J]

lemma rowAlt_zero (w : Fin 1 → Fin 2) :
    rowAlt 0 w = if w 0 = 0 then 1 else 0 := by
  classical
  change Saxl.altWord (Saxl.fiberGroup (@tag 0)) (@base 0) w = _
  let := Fintype.ofFinite (Saxl.fiberGroup (@tag 0))
  unfold Saxl.altWord
  have hu : (Finset.univ : Finset (Saxl.fiberGroup (@tag 0))) = {1} := by
    ext g
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Fin.ext
    have := ((g : Equiv.Perm (Fin (2*0+1))) i).isLt
    have := i.isLt
    omega
  rw [hu,Finset.sum_singleton]
  simp only [OneMemClass.coe_one, map_one, one_smul]
  change (Pi.single (@base 0) (1:ℂ) : Saxl.WordSpace 1 2) w = _
  rw [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; have := congrFun h 0; simpa [base] using this
  · intro h; funext i; have hi : i=0 := Subsingleton.elim _ _; subst i; simpa [base] using h

lemma rowAlt_formula (r : ℕ) (w : Fin (2*r+1) → Fin 2) :
    rowAlt r w = (if w 0 = 0 then 1 else 0) *
      ∏ i : Fin r, J (w ⟨2*i.val+1,by omega⟩) (w ⟨2*i.val+2,by omega⟩) := by
  induction r with
  | zero => simpa using rowAlt_zero w
  | succ r ih =>
    rw [rowAlt_step]
    change rowAlt r (Saxl.leftWord (appendPair r) w) *
      Saxl.altWord ⊤ (fun i : Fin 2 => i) (Saxl.rightWord (appendPair r) w) = _
    rw [ih, pair_alt, Fin.prod_univ_castSucc]
    exact mul_assoc _ _ _

end Saxl.PathLayer

namespace Saxl

def fiberRelabel {n m : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin m) (c : Fin m → α) :
    fiberGroup (c ∘ e) ≃ fiberGroup c where
  toFun g := ⟨e.permCongr g.val, by
    intro i
    obtain ⟨j,rfl⟩ := e.surjective i
    change c (e (g.val (e.symm (e j)))) = c (e j)
    rw [Equiv.symm_apply_apply]
    exact g.property j⟩
  invFun g := ⟨e.symm.permCongr g.val, by
    intro i
    change c (e (e.symm (g.val (e i)))) = c (e i)
    rw [Equiv.apply_symm_apply]
    exact g.property (e i)⟩
  left_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]
  right_inv g := by apply Subtype.ext; ext i; simp [Equiv.permCongr]

lemma altWord_fiber_relabel {n m d : ℕ} {α : Type uAlpha}
    (e : Fin n ≃ Fin m) (c : Fin m → α) (a : Fin m → Fin d) (w : Fin n → Fin d) :
    altWord (fiberGroup c) a (w ∘ e.symm) =
      altWord (fiberGroup (c ∘ e)) (a ∘ e) w := by
  classical
  let := Fintype.ofFinite (fiberGroup c)
  let := Fintype.ofFinite (fiberGroup (c ∘ e))
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  symm
  apply Fintype.sum_equiv (fiberRelabel e c)
  intro g
  have hs : signC ((fiberRelabel e c g).val) = signC g.val := by
    change signC (e.permCongr g.val) = _
    simp only [signC_def, Equiv.Perm.sign_permCongr]
  rw [hs]
  congr 1
  change (Pi.single (a ∘ e) (1:ℂ) : WordSpace n d) (w ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace m d) ((w ∘ e.symm) ∘ (e.permCongr g.val))
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    obtain ⟨j,rfl⟩ := e.surjective i
    simpa [Equiv.permCongr] using congrFun h j
  · intro h
    funext i
    simpa [Equiv.permCongr] using congrFun h (e i)

lemma altWord_letter_eval {n d D : ℕ} (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (G : Subgroup (Equiv.Perm (Fin n))) (a w : Fin n → Fin d) :
    altWord G (φ ∘ a) (φ ∘ w) = altWord G a w := by
  classical
  unfold altWord
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro g hg
  congr 1
  change (Pi.single (φ ∘ a) (1:ℂ) : WordSpace n D) ((φ ∘ w) ∘ g.val) =
    (Pi.single a (1:ℂ) : WordSpace n d) (w ∘ g.val)
  simp only [Pi.single_apply]
  congr 1
  apply propext
  constructor
  · intro h; funext i; exact hφ (congrFun h i)
  · intro h; funext i; exact congrArg φ (congrFun h i)



def lowLetter (h : ℕ) : Fin 2 → Fin ((staircase (h+2)).colLen 0) :=
  fun i => ⟨i.val, by rw [staircase_colLen]; have := i.isLt; omega⟩

lemma lowLetter_injective (h : ℕ) : Function.Injective (lowLetter h) := by
  intro i j hij
  exact Fin.ext (congrArg (fun x : Fin ((staircase (h+2)).colLen 0) => x.val) hij)

def bandColumnPathEquiv (h : ℕ) : Fin (2*(h+1)+1) ≃ Fin (bandSize h 2) :=
  Fin.revPerm.trans (bandPathEquiv h)

lemma bandColumnPath_coordinates (h : ℕ) (k : Fin (2*(h+1)+1)) :
    (bandTableau h 2 (bandColumnPathEquiv h k)).val = (k.val/2,h+1-(k.val+1)/2) := by
  change (bandTableau h 2 (bandPathEquiv h k.rev)).val = _
  rw [bandPath_coordinates]
  apply Prod.ext <;> simp only [Fin.val_rev] <;> have := k.isLt <;> omega

lemma bandRow_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.1) ∘ bandPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandColumn_path_group (h : ℕ) :
    fiberGroup ((fun j => (bandTableau h 2 j).val.2) ∘ bandColumnPathEquiv h) =
      fiberGroup (@PathLayer.tag (h+1)) := by
  apply Subgroup.ext
  intro g
  change (∀ i, _ = _) ↔ (∀ i, _ = _)
  simp only [Function.comp_apply, bandColumnPath_coordinates, PathLayer.tag]
  constructor <;> intro hg i <;> have hh := hg i <;>
    have := i.isLt <;> have := (g i).isLt <;> omega

lemma bandRow_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairRowTableau (h+2)) ∘ (rotateRowPositions h 2 : Equiv.Perm _))) ∘ bandPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, stairRowTableau, rotateRowPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply, staircaseSwap]
  change (rotateRow h 2 (bandTableau h 2 (bandPathEquiv h k))).val.2 = _
  change (if (bandTableau h 2 (bandPathEquiv h k)).val.2 < h-(bandTableau h 2 (bandPathEquiv h k)).val.1 then
    (bandTableau h 2 (bandPathEquiv h k)).val.2+2 else
    (bandTableau h 2 (bandPathEquiv h k)).val.2-(h-(bandTableau h 2 (bandPathEquiv h k)).val.1)) = _
  rw [bandPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandColumn_path_base (h : ℕ) :
    (rightWord (cutPositions h 2)
      (rowWord (stairTableau (h+2)) ∘ (rotateColumnPositions h 2 : Equiv.Perm _))) ∘ bandColumnPathEquiv h =
      lowLetter h ∘ (@PathLayer.base (h+1)) := by
  funext k
  apply Fin.ext
  simp only [Function.comp_apply, rightWord, rowWord, rotateColumnPositions,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  change (rotateColumn h 2 (bandTableau h 2 (bandColumnPathEquiv h k))).val.1 = _
  change (if (bandTableau h 2 (bandColumnPathEquiv h k)).val.1 < h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2 then
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1+2 else
    (bandTableau h 2 (bandColumnPathEquiv h k)).val.1-(h-(bandTableau h 2 (bandColumnPathEquiv h k)).val.2)) = _
  rw [bandColumnPath_coordinates]
  simp only [lowLetter, PathLayer.base]
  split_ifs <;> have := k.isLt <;> simp only [Fin.val_zero] <;> omega

lemma bandRow_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandRowWord h 2 ((lowLetter h ∘ w) ∘ (bandPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandRowWord bandRowGroup
  rw [altWord_fiber_relabel, bandRow_path_group, bandRow_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

lemma bandColumn_path_eval (h : ℕ) (w : Fin (2*(h+1)+1) → Fin 2) :
    bandColumnWord h 2 ((lowLetter h ∘ w) ∘ (bandColumnPathEquiv h).symm) = PathLayer.rowAlt (h+1) w := by
  unfold bandColumnWord bandColumnGroup
  rw [altWord_fiber_relabel, bandColumn_path_group, bandColumn_path_base,
    altWord_letter_eval _ (lowLetter_injective h)]
  rfl

end Saxl

end

end OAI
