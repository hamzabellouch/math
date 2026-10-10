import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TestExact

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} (Q:ReversibleQuiver V A)

inductive PositiveBraidRel : List V→List V→Prop
  | refl (w) : PositiveBraidRel w w
  | symm {v w} : PositiveBraidRel v w→PositiveBraidRel w v
  | trans {v w z} : PositiveBraidRel v w→PositiveBraidRel w z→PositiveBraidRel v z
  | cons (α) {v w} : PositiveBraidRel v w→PositiveBraidRel (α::v) (α::w)
  | orthogonal {α β} (h:OrthogonalVertices Q α β) (w) :
      PositiveBraidRel (α::β::w) (β::α::w)
  | adjacent {α β} (e:SimpleEdge Q α β) (w) :
      PositiveBraidRel (α::β::α::w) (β::α::β::w)

namespace PositiveBraidRel
lemma length_eq {v w:List V} (h:PositiveBraidRel Q v w) : v.length=w.length := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => exact congrArg Nat.succ ih
  | orthogonal => rfl
  | adjacent => rfl

lemma mem_iff {v w:List V} (h:PositiveBraidRel Q v w) (s:V) : s∈v↔s∈w := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => simpa only [List.mem_cons] using or_congr Iff.rfl ih
  | orthogonal => simp only [List.mem_cons]; tauto
  | adjacent => simp only [List.mem_cons]; tauto

lemma mem_set {v w:List V} (h:PositiveBraidRel Q v w) (U:Set V)
    (hv:∀ s∈v,s∈U) : ∀ s∈w,s∈U := fun s hs=>hv s ((h.mem_iff Q s).mpr hs)
end PositiveBraidRel

variable {K:Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def positiveWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>classPositiveTwist Q α (positiveWordAction w x)

lemma PositiveBraidRel.action_eq (hn:∀ a,Q.source a≠Q.target a)
    {v w:List V} (h:PositiveBraidRel Q v w) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q v x=positiveWordAction Q w x := by
  induction h with
  | refl => rfl
  | symm h ih => exact ih.symm
  | trans h k ih ik => exact ih.trans ik
  | cons α h ih => exact congrArg (classPositiveTwist Q α) ih
  | orthogonal h w =>
    exact congrArg (fun f:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f (positiveWordAction Q w x))
      (classTwistPerm_orthogonal Q hn h)
  | adjacent e w =>
    exact congrArg (fun f:Equiv.Perm (FiniteHomotopyClass Q (K:=K))=>f (positiveWordAction Q w x))
      (classTwistPerm_adjacent Q hn e)

lemma positiveWordAction_testUpper_reflect (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V)
    (hw:∀ s∈w,s∈U) {t:ℤ} (h:ClassTestUpper Q (positiveWordAction Q w x) U t) :
    ClassTestUpper Q x U t := by
  induction w with
  | nil => exact h
  | cons α w ih =>
    apply ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs))
    exact classPositiveTwist_testUpper_reflect Q hn _ U α (hw α (by simp)) h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
