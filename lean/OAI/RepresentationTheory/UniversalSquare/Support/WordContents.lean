import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.ZeroColumns
import OAI.RepresentationTheory.UniversalSquare.Balance.BalancePacking

namespace OAI

/-! Word Contents. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

def wordContent {n d : ℕ} (w : Fin n → Fin d) (j : Fin d) : ℕ :=
  (Finset.univ.filter (fun i => w i = j)).card

lemma wordContent_position_join {n a b d e E : ℕ}
    (p : Fin n ≃ Fin a ⊕ Fin b) (q : Fin E ≃ Fin d ⊕ Fin e)
    (w : Fin a → Fin d) (z : Fin b → Fin e) (j : Fin E) :
    wordContent
      ((positionWordsEquiv p).symm ((fun i => q.symm (Sum.inl (w i))),
        (fun i => q.symm (Sum.inr (z i))))) j =
      Sum.elim (wordContent w) (wordContent z) (q j) := by
  classical
  rw [wordContent, Finset.card_filter]
  rw [← Equiv.sum_comp p.symm]
  rw [Fintype.sum_sum_type]
  rcases hj : q j with k | k
  · have hqq : j = q.symm (Sum.inl k) := (q.eq_symm_apply).mpr hj
    subst j
    simp only [positionWordsEquiv, Equiv.coe_fn_symm_mk, joinPositions, Equiv.apply_symm_apply, Sum.elim_inl,
      Sum.elim_inr, q.symm.injective.eq_iff,
      Sum.inl.injEq, Sum.inr_ne_inl, ite_false, Finset.sum_const_zero, add_zero]
    rw [wordContent,Finset.card_filter]
  · have hqq : j = q.symm (Sum.inr k) := (q.eq_symm_apply).mpr hj
    subst j
    simp only [positionWordsEquiv, Equiv.coe_fn_symm_mk, joinPositions, Equiv.apply_symm_apply, Sum.elim_inl,
      Sum.elim_inr, q.symm.injective.eq_iff,
      Sum.inr.injEq, Sum.inl_ne_inr, ite_false, Finset.sum_const_zero, zero_add]
    rw [wordContent,Finset.card_filter]

lemma wordContent_lift_equiv {n d e : ℕ} (q : Fin d ≃ Fin e)
    (w : Fin n → Fin d) (j : Fin e) :
    wordContent (q ∘ w) j = wordContent w (q.symm j) := by
  classical
  unfold wordContent
  congr 1
  apply Finset.filter_congr
  intro i _
  change q (w i) = j ↔ w i = q.symm j
  exact q.eq_symm_apply.symm

def appendLetters (ps qs : List ℕ) : Fin (ps ++ qs).length ≃ Fin ps.length ⊕ Fin qs.length :=
  (finCongr (List.length_append (as := ps) (bs := qs))).trans finSumFinEquiv.symm

lemma get_appendLetters (ps qs : List ℕ) (j : Fin (ps ++ qs).length) :
    (ps ++ qs).get j = Sum.elim ps.get qs.get (appendLetters ps qs j) := by
  obtain ⟨j,rfl⟩ := (appendLetters ps qs).symm.surjective j
  rcases j with j | j
  · simp only [Equiv.apply_symm_apply, Sum.elim_inl]
    change (ps ++ qs)[j.val] = ps[j.val]
    exact List.getElem_append_left j.isLt
  · simp only [Equiv.apply_symm_apply, Sum.elim_inr]
    change (ps ++ qs)[ps.length+j.val] = qs[j.val]
    rw [List.getElem_append_right (by omega)]
    simp

lemma list_get_fiber_card (ps : List ℕ) (k : ℕ) :
    Fintype.card {i : Fin ps.length // ps.get i = k} = ps.count k := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter]
  induction ps with
  | nil => simp
  | cons p ps ih =>
    change (∑ i : Fin (ps.length+1), if (p::ps).get i = k then (1:ℕ) else 0) = _
    rw [Fin.sum_univ_succ]
    change (if p = k then 1 else 0) + (∑ i : Fin ps.length, if ps.get i = k then 1 else 0) = _
    rw [ih]
    simp [List.count_cons, Nat.add_comm]

theorem list_get_equiv {ps qs : List ℕ} (h : ps.Perm qs) :
    ∃ q : Fin ps.length ≃ Fin qs.length, ∀ i, qs.get (q i) = ps.get i := by
  classical
  let f (k : ℕ) : {i : Fin ps.length // ps.get i = k} ≃
      {i : Fin qs.length // qs.get i = k} :=
    Fintype.equivOfCardEq (by rw [list_get_fiber_card,list_get_fiber_card,h.count_eq])
  let q := (Equiv.sigmaFiberEquiv ps.get).symm.trans
    ((Equiv.sigmaCongrRight f).trans (Equiv.sigmaFiberEquiv qs.get))
  exact ⟨q,fun i => (f (ps.get i) ⟨i,rfl⟩).property⟩

lemma columnShape_rows_permutation (ps : List ℕ) (hp : ∀ p ∈ ps, 0 < p) :
    ps.Perm (Columns.columnShape ps).transpose.rowLens := by
  rw [Columns.columnShape_cols]
  have he : ps.filter (fun p => 0 < p) = ps := by
    apply List.filter_eq_self.mpr
    intro p h
    simpa using hp p h
  simpa only [he] using Columns.positiveSorted_perm ps

end Saxl
end
end

end OAI
