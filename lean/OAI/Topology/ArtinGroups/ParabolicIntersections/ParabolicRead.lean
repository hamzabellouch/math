import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicCosetProjection

namespace OAI

/-! Reading the parabolic letters crossed by a Coxeter gallery. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W)
    (J : Set S)

noncomputable def parabolicLetterValue : Option J → W
  | none => 1
  | some t => cs.simple t

noncomputable def parabolicLetter (r : W) : Option J :=
  Classical.epsilon (fun l => parabolicLetterValue cs J l=r)

noncomputable def parabolicStepLetter (w : W) (s : S) : Option J :=
  parabolicLetter cs J (parabolicStepRatio cs J w s)

lemma parabolicStepLetter_value (w : W) (s : S) :
    parabolicLetterValue cs J (parabolicStepLetter cs J w s)=parabolicStepRatio cs J w s := by
  unfold parabolicStepLetter parabolicLetter
  refine Classical.epsilon_spec (p := fun l : Option J =>
    parabolicLetterValue cs J l=parabolicStepRatio cs J w s) ?_
  rcases parabolicStepRatio_cases cs J w s with h | ⟨t,h⟩
  · exact ⟨none,h.symm⟩
  · exact ⟨some t,h.symm⟩

lemma parabolicStepLetter_reverse (w : W) (s : S) :
    parabolicStepLetter cs J (w*cs.simple s) s=parabolicStepLetter cs J w s := by
  unfold parabolicStepLetter
  rw [parabolicStepRatio_reverse]

lemma parabolicStepLetter_conjugate (w : W) (s : S) (t : J)
    (ht : parabolicStepLetter cs J w s=some t) :
    MulAut.conj (parabolicComponent cs J w) (cs.simple t)=MulAut.conj w (cs.simple s) := by
  have hr := parabolicStepLetter_value cs J w s
  rw [ht] at hr
  change cs.simple t=parabolicStepRatio cs J w s at hr
  have hne : parabolicStepRatio cs J w s ≠ 1 := by
    intro he
    have hl := congrArg cs.length (hr.trans he)
    rw [cs.length_simple,cs.length_one] at hl
    omega
  rw [parabolicStepRatio_reflection cs J w s hne] at hr
  simp only [MulAut.conj_apply]
  rw [hr]
  have hw := parabolicComponent_mul_rep cs J w
  calc _ = (parabolicComponent cs J w*parabolicRep cs J w)*cs.simple s*
      (parabolicComponent cs J w*parabolicRep cs J w)⁻¹ := by group
       _ = _ := by rw [hw]

noncomputable def parabolicRead : W → List S → List J
  | _, [] => []
  | w, s::u => (parabolicStepLetter cs J w s).toList ++ parabolicRead (w*cs.simple s) u

lemma parabolicLetter_word (l : Option J) :
    cs.wordProd (l.toList.map Subtype.val)=parabolicLetterValue cs J l := by
  cases l <;> simp [parabolicLetterValue]

/-- The read word records exactly the change in the parabolic component. -/
theorem parabolicRead_product (w : W) (u : List S) :
    cs.wordProd ((parabolicRead cs J w u).map Subtype.val) =
      (parabolicComponent cs J w)⁻¹*parabolicComponent cs J (w*cs.wordProd u) := by
  induction u generalizing w with
  | nil => simp [parabolicRead]
  | cons s u ih =>
    simp only [parabolicRead,List.map_append,cs.wordProd_append,
      parabolicLetter_word,parabolicStepLetter_value,ih,cs.wordProd_cons]
    unfold parabolicStepRatio
    rw [mul_assoc w]
    group

end HarmonicArtin.ParabolicIntersections

end OAI
