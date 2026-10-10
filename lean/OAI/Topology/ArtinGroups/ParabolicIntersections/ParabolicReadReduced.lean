import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicRead

namespace OAI

/-! A parabolic read of a reduced gallery is reduced. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

private lemma conjugate_sequence (a b : W) (l : List W) :
    (l.map (MulAut.conj b)).map (MulAut.conj a) = l.map (MulAut.conj (a*b)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply,MulAut.conj_apply]
  group

/-- The converse to the usual no-repeated-inversion property. -/
theorem reduced_of_nodup_inversions (u : List S) (hu : (cs.leftInvSeq u).Nodup) :
    cs.IsReduced u := by
  induction u with
  | nil => simp [CoxeterSystem.IsReduced]
  | cons s u ih =>
    change (cs.simple s :: (cs.leftInvSeq u).map (MulAut.conj (cs.simple s))).Nodup at hu
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hu
    have hr := ih htail.of_map
    rcases cs.length_simple_mul (cs.wordProd u) s with ha | hd
    · change cs.length (cs.simple s*cs.wordProd u)=(s::u).length
      rw [ha,hr.eq,List.length_cons]
    · have hm := simple_mem_leftInvSeq_of_shorter cs hr s (by omega)
      apply (hnot ?_).elim
      exact List.mem_map.mpr ⟨cs.simple s,hm,by simp only [MulAut.conj_apply,mul_inv_cancel_right]⟩

/-- The read gallery crosses a subsequence of the original reflecting
walls; conjugating by the initial component identifies their labels. -/
theorem parabolicRead_inversions (J : Set S) (w : W) (u : List S) :
    ((cs.leftInvSeq ((parabolicRead cs J w u).map Subtype.val)).map
      (MulAut.conj (parabolicComponent cs J w))).Sublist
      ((cs.leftInvSeq u).map (MulAut.conj w)) := by
  induction u generalizing w with
  | nil => simp [parabolicRead]
  | cons s u ih =>
    have hi := ih (w*cs.simple s)
    cases hl : parabolicStepLetter cs J w s with
    | none =>
      have hv := parabolicStepLetter_value cs J w s
      rw [hl] at hv
      change 1=(parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s) at hv
      have hc : parabolicComponent cs J (w*cs.simple s)=parabolicComponent cs J w :=
        (inv_mul_eq_one.mp hv.symm).symm
      rw [hc] at hi
      simpa only [parabolicRead,hl,Option.toList_none,List.nil_append,
        CoxeterSystem.leftInvSeq,List.map_cons,conjugate_sequence] using
        List.Sublist.cons (MulAut.conj w (cs.simple s)) hi
    | some t =>
      have hv := parabolicStepLetter_value cs J w s
      rw [hl] at hv
      change cs.simple t=(parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.simple s) at hv
      have hc : parabolicComponent cs J (w*cs.simple s)=parabolicComponent cs J w*cs.simple t :=
        ((eq_inv_mul_iff_mul_eq).mp hv).symm
      rw [hc] at hi
      have href := parabolicStepLetter_conjugate cs J w s t hl
      simpa only [parabolicRead,hl,Option.toList_some,List.singleton_append,List.map_cons,
        CoxeterSystem.leftInvSeq,conjugate_sequence,href] using
        List.Sublist.cons_cons (MulAut.conj w (cs.simple s)) hi

/-- Retraction to a standard parabolic preserves reducedness of galleries,
allowing letters which do not cross a parabolic wall to disappear. -/
theorem parabolicRead_reduced (J : Set S) (w : W) (u : List S) (hu : cs.IsReduced u) :
    cs.IsReduced ((parabolicRead cs J w u).map Subtype.val) := by
  apply reduced_of_nodup_inversions cs
  have h := (parabolicRead_inversions cs J w u).nodup
    (hu.nodup_leftInvSeq.map (MulAut.conj w).injective)
  exact h.of_map

end HarmonicArtin.ParabolicIntersections

end OAI
