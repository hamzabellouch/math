import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.OddPath
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Column Reorder. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Columns

theorem columns_equiv_of_perm {rs ss : List ℕ} (h : rs.Perm ss) :
    ∃ e : Cells rs ≃ Cells ss,
      (∀ c, row (e c) = row c) ∧
      (∀ c d, col (e c) = col (e d) ↔ col c = col d) := by
  induction h with
  | nil =>
    exact ⟨Equiv.refl _, fun c => isEmptyElim c, fun c => isEmptyElim c⟩
  | @cons r rs ss h ih =>
    obtain ⟨e,hr,hc⟩ := ih
    refine ⟨(Equiv.refl (Fin r)).sumCongr e, ?_, ?_⟩
    · intro c
      rcases c with c | c
      · rfl
      · exact hr c
    · intro c d
      rcases c with c | c <;> rcases d with d | d
      · simp [col]
      · simp [col]
      · simp [col]
      · simpa only [Equiv.sumCongr_apply, Sum.map_inr, col, Nat.add_right_cancel_iff] using hc c d
  | swap r s rs =>
    let e : Cells (s::r::rs) ≃ Cells (r::s::rs) :=
      (Equiv.sumAssoc (Fin s) (Fin r) (Cells rs)).symm.trans
        (((Equiv.sumComm (Fin s) (Fin r)).sumCongr (Equiv.refl (Cells rs))).trans
          (Equiv.sumAssoc (Fin r) (Fin s) (Cells rs)))
    refine ⟨e, ?_, ?_⟩
    · intro c
      rcases c with c | (c | c) <;> rfl
    · intro c d
      rcases c with c | (c | c) <;> rcases d with d | (d | d) <;>
        simp [e, col]
  | @trans rs ss ts h h' ih ih' =>
    obtain ⟨e,hr,hc⟩ := ih
    obtain ⟨f,hr',hc'⟩ := ih'
    refine ⟨e.trans f, ?_, ?_⟩
    · intro c
      exact (hr' (e c)).trans (hr c)
    · intro c d
      exact (hc' (e c) (e d)).trans (hc c d)

theorem place_columns {rs : List ℕ} (μ : YoungDiagram)
    (h : rs.Perm μ.transpose.rowLens) :
    ∃ e : Cells rs ≃ μ.cells,
      (∀ c, (e c).val.1 = row c) ∧
      (∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d) := by
  obtain ⟨e,hr,hc⟩ := columns_equiv_of_perm h
  exact ⟨e.trans (toYoung μ), hr, hc⟩

def listColumnPerm (rs : List ℕ) (π : Perms rs) :
    fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) :=
  ⟨(enumerate rs).symm.permCongr (perm π), by
    intro i
    simp only [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]
    exact perm_col π _⟩

lemma listColumnPerm_bijective (rs : List ℕ) : Function.Bijective (listColumnPerm rs) := by
  constructor
  · intro π σ h
    apply perm_injective rs
    apply (enumerate rs).symm.permCongr.injective
    exact congrArg Subtype.val h
  · intro g
    let e := enumerate rs
    obtain ⟨π,hπ⟩ := perm_surjective rs (e.permCongr g.val) (by
      intro c
      have hh := g.property (e.symm c)
      simpa only [Equiv.permCongr_apply, e, Equiv.apply_symm_apply] using hh)
    refine ⟨π, ?_⟩
    apply Subtype.ext
    change e.symm.permCongr (perm π) = g.val
    rw [hπ]
    apply Equiv.ext
    intro i
    simp [Equiv.permCongr_apply]

lemma listColumnPerm_sign (rs : List ℕ) (π : Perms rs) :
    signC (listColumnPerm rs π).val = sg π := by
  change (((Equiv.Perm.sign ((enumerate rs).symm.permCongr (perm π)) : ℤ) : ℂ)) = sg π
  rw [Equiv.Perm.sign_permCongr]
  exact sign_perm π

lemma mapped_placed_columns {rs : List ℕ} {μ : YoungDiagram}
    (e : Cells rs ≃ μ.cells)
    (hr : ∀ c, (e c).val.1 = row c)
    (hc : ∀ c d, (e c).val.2 = (e d).val.2 ↔ col c = col d)
    (N : ℕ → Band.Mat) :
    wordMap (fun (i : Fin (μ.colLen 0)) (a : Fin 4) =>
      N i.val (Path.parts a).1 (Path.parts a).2)
      (polytabloid ((enumerate rs).trans e)) = dualBlockWord rs N := by
  classical
  have hg : columnGroup ((enumerate rs).trans e) =
      fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)) := by
    apply Subgroup.ext
    intro g
    change (∀ i, (e (enumerate rs (g i))).val.2 = (e (enumerate rs i)).val.2) ↔ _
    simp only [hc]
    rfl
  let := Fintype.ofFinite (fiberGroup (fun i : Fin rs.sum => col (enumerate rs i)))
  rw [polytabloid_eq_altWord, hg, altWord_inverse_sum, map_sum]
  unfold dualBlockWord
  symm
  apply Fintype.sum_equiv (Equiv.ofBijective (listColumnPerm rs) (listColumnPerm_bijective rs))
  intro π
  simp only [Equiv.ofBijective_apply, map_smul]
  rw [listColumnPerm_sign]
  congr 1
  funext w
  rw [wordMap_single]
  unfold Path.pureWord
  apply Finset.prod_congr rfl
  intro q hq
  apply congrArg (fun i => N i (Path.parts (w q)).1 (Path.parts (w q)).2)
  change row (perm π (enumerate rs q)) = (e (enumerate rs ((listColumnPerm rs π).val q))).val.1
  rw [hr]
  simp only [listColumnPerm, Equiv.permCongr_apply, Equiv.symm_symm, Equiv.apply_symm_apply]

lemma positionProduct_pair {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x u : WordSpace a d) (y v : WordSpace b d) :
    dotProduct (positionProduct e x y) (positionProduct e u v) =
      dotProduct x u * dotProduct y v := by
  classical
  let E : (Fin n → Fin d) ≃ (Fin a → Fin d) × (Fin b → Fin d) :=
    (Equiv.arrowCongr e (Equiv.refl _)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  rw [dotProduct, dotProduct, dotProduct, Finset.sum_mul_sum]
  rw [← Fintype.sum_prod_type (fun p : (Fin a → Fin d) × (Fin b → Fin d) =>
    x p.1 * u p.1 * (y p.2 * v p.2))]
  apply Fintype.sum_equiv E
  intro w
  change (x (leftWord e w) * y (rightWord e w)) *
      (u (leftWord e w) * v (rightWord e w)) =
      (x (leftWord e w) * u (leftWord e w)) *
      (y (rightWord e w) * v (rightWord e w))
  ring

def columnWedge (r : ℕ) (N : ℕ → Band.Mat) : WordSpace r 4 :=
  ∑ π : Equiv.Perm (Fin r), (((Equiv.Perm.sign π : ℤ) : ℂ)) •
    Path.pureWord (fun i => N (π i).val)

lemma dualBlockWord_cons (r : ℕ) (rs : List ℕ) (N : ℕ → Band.Mat) :
    dualBlockWord (r::rs) N = positionProduct finSumFinEquiv.symm
      (columnWedge r N) (dualBlockWord rs N) := by
  classical
  funext w
  change (∑ π : Perms (r::rs), sg π • Path.pureWord
    (fun q => N (row (perm π (enumerate (r::rs) q))))) w =
    columnWedge r N (leftWord finSumFinEquiv.symm w) *
      dualBlockWord rs N (rightWord finSumFinEquiv.symm w)
  simp only [Perms, Fintype.sum_prod_type, sg, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, columnWedge, dualBlockWord]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  apply Finset.sum_congr rfl
  intro σ hσ
  have hp : Path.pureWord (fun q => N (row (perm (rs := r::rs) (π,σ) (enumerate (r::rs) q)))) w =
      Path.pureWord (fun q => N (π q).val) (leftWord finSumFinEquiv.symm w) *
        Path.pureWord (fun q => N (row (perm σ (enumerate rs q))))
          (rightWord finSumFinEquiv.symm w) := by
    unfold Path.pureWord
    change (∏ i : Fin (r + rs.sum), N (row (perm (rs := r::rs) (π, σ)
      (enumerate (r::rs) i))) (Path.parts (w i)).1 (Path.parts (w i)).2) = _
    rw [Fin.prod_univ_add]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_left r rs i]
      rfl
    · apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_right r rs i]
      rfl
  rw [hp]
  ring

end Saxl.Columns
end
end

end OAI
