import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel
import OAI.Topology.ArtinGroups.Complexes.HomMono

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

namespace FiniteModel
noncomputable def positiveWord : List V → FiniteModel.{u} Q (K:=K) → FiniteModel.{u} Q (K:=K)
  | [],E=>E
  | α::w,E=>ofComplex Q ((positiveWord w E).complex.positiveTwist Q α)

noncomputable def positiveWordMap : (w:List V) → {E F:FiniteModel.{u} Q (K:=K)} →
    Map Q E.complex F.complex → Map Q (positiveWord Q w E).complex (positiveWord Q w F).complex
  | [],_,_,f=>f
  | α::w,_,_,f=>(positiveWordMap w f).positiveTwist Q α

lemma positiveWord_class (w:List V) (E:FiniteModel.{u} Q (K:=K)) :
    classOfComplex Q (positiveWord Q w E).complex=positiveWordAction Q w (classOfComplex Q E.complex) := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classPositiveTwist Q α (classOfComplex Q (positiveWord Q w E).complex)=
      classPositiveTwist Q α (positiveWordAction Q w (classOfComplex Q E.complex))
    rw [ih]

lemma positiveWord_homMono (hn:∀ a,Q.source a≠Q.target a) (w:List V)
    (T E F:FiniteModel.{u} Q (K:=K)) (f:Map Q E.complex F.complex)
    (h:HomMonoFrom Q T.complex f) :
    HomMonoFrom Q (positiveWord Q w T).complex (positiveWordMap Q w f) := by
  induction w with
  | nil => exact h
  | cons α w ih => exact ih.positiveTwist Q hn α
end FiniteModel

variable {I J L M:Type u} [Fintype I] [Fintype J] [Fintype L] [Fintype M]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq M]

omit [Fintype V] [DecidableEq A] [DecidableEq I] [DecidableEq J]
  [DecidableEq L] [DecidableEq M] in
lemma HomMonoFrom.comp {T:BasedComplex Q (K:=K) I} {E:BasedComplex Q (K:=K) J}
    {F:BasedComplex Q (K:=K) L} {G:BasedComplex Q (K:=K) M}
    {f:Map Q E F} {g:Map Q F G} (hf:HomMonoFrom Q T f) (hg:HomMonoFrom Q T g) :
    HomMonoFrom Q T (f.comp Q g) := by
  intro a ha hb
  apply hf a ha
  have hac:a*f.matrix∈homCycles Q T F 0 0 := by
    simpa only [zero_add] using homCycles_mul Q ha (map_mem_homCycles Q f)
  apply hg (a*f.matrix) hac
  simpa only [Map.comp,Matrix.mul_assoc] using hb

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma HomotopyEquivalence.homMonoFrom (T:BasedComplex Q (K:=K) I)
    {E:BasedComplex Q (K:=K) J} {F:BasedComplex Q (K:=K) L}
    (e:HomotopyEquivalence Q E F) : HomMonoFrom Q T e.forward := by
  intro g hg hb
  have hb':=homBoundary_mul_cycle Q hb (map_mem_homCycles Q e.backward)
  have hc:=homCycle_mul_boundary Q hg (e.sourceCorrection_boundary Q)
  simp only [zero_add] at hb' hc
  have hz:=(homBoundaries Q T E 0 0).sub_mem hb' hc
  rw [Matrix.mul_sub] at hz
  erw [mul_projectiveIdentity Q hg.1.1] at hz
  simpa only [Matrix.mul_assoc,sub_sub_cancel] using hz

omit [Fintype V] [DecidableEq A] [DecidableEq J] [DecidableEq L] in
lemma HomMonoFrom.sourceEquivalence
    {T:BasedComplex Q (K:=K) I} {T':BasedComplex Q (K:=K) M}
    {E:BasedComplex Q (K:=K) J} {F:BasedComplex Q (K:=K) L}
    (e:HomotopyEquivalence Q T T') {f:Map Q E F} (h:HomMonoFrom Q T f) :
    HomMonoFrom Q T' f := by
  intro g hg hb
  have hc:e.forward.matrix*g∈homCycles Q T E 0 0 := by
    simpa only [zero_add] using homCycles_mul Q (map_mem_homCycles Q e.forward) hg
  have hbc:e.forward.matrix*g*f.matrix∈homBoundaries Q T F 0 0 := by
    have hz:=homCycle_mul_boundary Q (map_mem_homCycles Q e.forward) hb
    simpa only [zero_add,Matrix.mul_assoc] using hz
  have hh:=h _ hc hbc
  have hh':=homCycle_mul_boundary Q (map_mem_homCycles Q e.backward) hh
  have hec:=homBoundary_mul_cycle Q ((e.symm Q).sourceCorrection_boundary Q) hg
  simp only [zero_add] at hh' hec
  have hz:=(homBoundaries Q T' E 0 0).sub_mem hh' hec
  change e.backward.matrix*(e.forward.matrix*g)-
    ((e.backward.matrix*e.forward.matrix-projectiveIdentity Q T'.placement)*g)∈
      homBoundaries Q T' E 0 0 at hz
  rw [Matrix.sub_mul] at hz
  erw [projectiveIdentity_mul Q hg.1.1] at hz
  simpa only [Matrix.mul_assoc,sub_sub_cancel] using hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
