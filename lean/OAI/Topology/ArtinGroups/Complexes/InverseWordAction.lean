import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveWordLowerBound
import OAI.Topology.ArtinGroups.Complexes.PlacedProjective

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma negativeTwist_upper_bound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,(E.placement i).level≤d) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.negativeTwist Q α) F) :
    ∀ j,(F.placement j).level≤d := by
  have reduction : HomotopyEquivalence Q (E.negativeTwist Q α)
      (reducedNegativeAmplitudeTwist Q E α) := by
    convert negativeAmplitudeTwistReduction Q E α using 1
  apply minimal_bound_transport Q (reducedNegativeAmplitudeTwist Q E α) F hF
    ((reduction.symm Q).trans Q e) (fun p=>p.level≤d)
  intro k
  obtain ⟨i,hi⟩:=reducedNegativeAmplitudeTwist_level Q E α k
  have hh:=hE i
  rcases hi with hi|⟨hi,_⟩ <;> omega

lemma classNegativeTwist_upper_bound (α:V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassUpperBound Q d x) : ClassUpperBound Q d (classNegativeTwist Q α x) := by
  let E:=minimalClassModel Q x
  let y:=classNegativeTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.negativeTwist Q α)=classOfComplex Q F.complex := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  exact negativeTwist_upper_bound Q E.complex F.complex hx α (minimalClassModel_minimal Q y) e

noncomputable def inverseWordAction : List V→FiniteHomotopyClass Q (K:=K)→FiniteHomotopyClass Q (K:=K)
  | [],x=>x
  | α::w,x=>inverseWordAction w (classNegativeTwist Q α x)

lemma positive_inverseWord (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    positiveWordAction Q w (inverseWordAction Q w x)=x := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change classPositiveTwist Q α (positiveWordAction Q w
      (inverseWordAction Q w (classNegativeTwist Q α x)))=x
    rw [ih]
    exact (classTwistPerm Q hn α).apply_symm_apply x

lemma inverse_positiveWord (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    inverseWordAction Q w (positiveWordAction Q w x)=x := by
  induction w generalizing x with
  | nil => rfl
  | cons α w ih =>
    change inverseWordAction Q w ((classTwistPerm Q hn α).symm
      ((classTwistPerm Q hn α) (positiveWordAction Q w x)))=x
    rw [Equiv.symm_apply_apply,ih]

lemma positiveWord_homDimension (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x y:FiniteHomotopyClass Q (K:=K)) (n v:ℤ) :
    classHomDimension Q n v (positiveWordAction Q w x) (positiveWordAction Q w y)=
      classHomDimension Q n v x y := by
  induction w with
  | nil => rfl
  | cons α w ih =>
    change classHomDimension Q n v (classPositiveTwist Q α _) (classPositiveTwist Q α _)=_
    rw [classPositiveTwist_homDimension Q hn,ih]

lemma inverseWord_upper_bound (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassUpperBound Q d x) : ClassUpperBound Q d (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => exact hx
  | cons α w ih => exact ih _ (classNegativeTwist_upper_bound Q α x hx)

theorem inverseReducedWord_layer_bounds (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (a b:ℤ)
    (hlo:ClassLowerBound Q a x) (hhi:ClassUpperBound Q b x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q (a-1) (inverseWordAction Q w x) ∧
      ClassUpperBound Q b (inverseWordAction Q w x) := by
  refine ⟨?_,inverseWord_upper_bound Q w x hhi⟩
  apply classLowerBound_of_placed_vanishing Q _ (a-1)
  intro p hp
  let P:=classOfComplex Q (placedProjective Q (K:=K) p)
  have hPlo:ClassLowerBound Q p.level P :=
    classLowerBound_of_representative Q _ (fun _=>le_rfl)
  have hPhi:ClassUpperBound Q p.level P :=
    classUpperBound_of_representative Q _ (fun _=>le_rfl)
  have hcap:ClassUpperBound Q (p.level+1) (positiveWordAction Q w P) :=
    (reducedWord_layer_bounds Q hn U hU P p.level p.level hPlo hPhi w hw hr).2
  rw [← positiveWord_homDimension Q hn w P (inverseWordAction Q w x) 0 0,
    positive_inverseWord Q hn]
  exact classHomDimension_zero_of_layer_gap Q _ x (p.level+1) a hcap hlo (by omega)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
