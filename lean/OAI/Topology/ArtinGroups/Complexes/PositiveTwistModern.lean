import Mathlib
import OAI.Topology.ArtinGroups.Complexes.NegativeTwistModern
import OAI.Topology.ArtinGroups.Complexes.PositiveConeIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def HomotopyEquivalence.positiveTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.positiveTwist Q α) (F.positiveTwist Q α) := by
  convert e.positiveTwist Q α using 1

lemma positiveLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (α:V) :
    classLayer Q q (classOfComplex Q ((lowerTruncation Q E hE q).positiveTwist Q α))=
      classLayer Q q (classOfComplex Q (E.positiveTwist Q α)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  let G:=minimalClassModel Q (classOfComplex Q (R.positiveTwist Q α))
  let e₀:HomotopyEquivalence Q (R.positiveTwist Q α) G.complex:=
    (minimalClassModelEquivalence Q (R.positiveTwist Q α)).symm Q
  have hr:∀ i,q+1≤(R.placement i).level := by
    intro i
    have hi:=i.property
    change ¬(E.placement i).level≤q at hi
    change q+1≤(E.placement i).level
    omega
  have hg:∀ i,q+1≤(G.complex.placement i).level :=
    positiveTwist_lower_bound Q R G.complex hr α (minimalClassModel_minimal Q _) e₀
  have coneIso : ChainIsomorphism Q ((f.cone Q).positiveTwist Q α)
      ((f.positiveTwist Q α).cone Q) := by
    convert positiveTwistCone Q f α using 1
  let e:HomotopyEquivalence Q ((f.positiveTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (((lowConeReduction Q E (lowerLevelSet Q E q) (levelDownClosed Q E hE q)).positiveTwistModern Q α).trans Q e₀)
  apply classLayer_eq_of_cone_equivalence Q (f.positiveTwist Q α) G.complex e q
  intro i
  have hi:=hg i
  constructor <;> omega

noncomputable def lowPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (hE:∀ i,q≤(E.placement i).level) :
    {i:I // (E.placement i).level=q} ≃ lowerLevelSet Q E q where
  toFun i:=⟨i.val,le_of_eq i.property⟩
  invFun i:=⟨i.val,le_antisymm i.property (hE i.val)⟩
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype V] [DecidableEq A] in
lemma lowRestriction_bottom_eq_layer (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hlo:∀ i,q≤(E.placement i).level) :
    classOfComplex Q (lowerTruncation Q E hE q)=
      classLayer Q q (classOfComplex Q E) := by
  have he:(lowerTruncation Q E hE q).reindex Q (lowPureIndex Q E q hlo)=
      E.pureLayer Q hE q := by
    apply ext_placement_differential Q <;> rfl
  rw [classLayer_minimal]
  exact (classOfComplex_reindex Q _ (lowPureIndex Q E q hlo)).trans (by rw [he])

lemma classPositiveTwist_bottom_layer (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hfloor:ClassLowerBound Q q x) (α:V) :
    classLayer Q q (classPositiveTwist Q α x)=
      classLayer Q q (classPositiveTwist Q α (classLayer Q q x)) := by
  let E:=minimalClassModel Q x
  have hE:=minimalClassModel_minimal Q x
  have hx:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  have hl:=positiveLayer_lowerTruncation Q E.complex hE q α
  have he:=lowRestriction_bottom_eq_layer Q E.complex hE q hfloor
  change classLayer Q q (classPositiveTwist Q α (classOfComplex Q (lowerTruncation Q E.complex hE q)))=
    classLayer Q q (classPositiveTwist Q α (classOfComplex Q E.complex)) at hl
  rw [he,hx] at hl
  exact hl.symm

theorem positiveWord_bottom_layer (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (q:ℤ) (hfloor:ClassLowerBound Q q x) :
    classLayer Q q (positiveWordAction Q w x)=
      classLayer Q q (positiveWordAction Q w (classLayer Q q x)) := by
  induction w generalizing x with
  | nil=>exact (classLayer_idempotent Q x q).symm
  | cons α w ih=>
    have hc:=classPositiveTwist_bottom_layer Q (positiveWordAction Q w x) q
      (positiveWord_lower_bound Q w x hfloor) α
    have hc':=classPositiveTwist_bottom_layer Q (positiveWordAction Q w (classLayer Q q x)) q
      (positiveWord_lower_bound Q w _ (classLayer_lowerBound Q x q)) α
    exact hc.trans ((congrArg (fun y=>classLayer Q q (classPositiveTwist Q α y))
      (ih x hfloor)).trans hc'.symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
