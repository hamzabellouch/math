import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood
import OAI.Topology.ArtinGroups.Complexes.LayerConeEquivalence
import OAI.Topology.ArtinGroups.Complexes.NegativeConeIndex
import OAI.Topology.ArtinGroups.Complexes.HighConeIndex
import OAI.Topology.ArtinGroups.Complexes.EmptyTestIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

noncomputable def HomotopyEquivalence.negativeTwistModern
    {J:Type u} [Fintype J] [DecidableEq J]
    {E:BasedComplex Q (K:=K) I} {F:BasedComplex Q (K:=K) J}
    (e:HomotopyEquivalence Q E F) (α:V) :
    HomotopyEquivalence Q (E.negativeTwist Q α) (F.negativeTwist Q α) := by
  convert e.negativeTwist Q α using 1

omit [Fintype V] [DecidableEq A] in
lemma classLayer_upperBound (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    ClassUpperBound Q q (classLayer Q q x) :=
  classUpperBound_of_representative Q _ (fun i=>le_of_eq i.property)

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerBound (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    ClassLowerBound Q q (classLayer Q q x) :=
  classLowerBound_of_representative Q _ (fun i=>le_of_eq i.property.symm)

noncomputable def allPureIndex (E:BasedComplex Q (K:=K) I) (q:ℤ)
    (h:∀ i,(E.placement i).level=q) : I ≃ {i:I // (E.placement i).level=q} where
  toFun i:=⟨i,h i⟩
  invFun i:=i.val
  left_inv _:=rfl
  right_inv _:=rfl

omit [Fintype V] [DecidableEq A] in
lemma classLayer_eq_self_of_pure (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (h:∀ i,(E.placement i).level=q) :
    classLayer Q q (classOfComplex Q E)=classOfComplex Q E := by
  rw [classLayer_minimal Q E hE]
  have he:(E.pureLayer Q hE q).reindex Q (allPureIndex Q E q h)=E := by
    apply ext_placement_differential Q <;> rfl
  exact (classOfComplex_reindex Q _ (allPureIndex Q E q h)).trans (by rw [he])

omit [Fintype V] [DecidableEq A] in
lemma classLayer_idempotent (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) :
    classLayer Q q (classLayer Q q x)=classLayer Q q x := by
  let y:=classLayer Q q x
  let E:=minimalClassModel Q y
  have hp:∀ i,(E.complex.placement i).level=q := fun i=>
    le_antisymm (classLayer_upperBound Q x q i) (classLayer_lowerBound Q x q i)
  have he:classOfComplex Q E.complex=y:=minimalClassModel_class Q y
  simpa only [he] using classLayer_eq_self_of_pure Q E.complex
    (minimalClassModel_minimal Q y) q hp

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (q:ℤ) :
    classLayer Q q (classOfComplex Q (lowerTruncation Q E hE q))=
      classLayer Q q (classOfComplex Q E) := by
  apply classLayer_eq_of_cone_equivalence Q (lowInclusion Q E _ (levelDownClosed Q E hE q))
    (upperTruncation Q E hE q) (lowConeReduction Q E _ _) q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma capped_upperTruncation_far (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q) :
    ∀ i,((upperTruncation Q E hE q).placement i).color∉Q.closedNeighborhood U := by
  intro i hi
  exact i.property (hcap i hi)

lemma negativeLayer_lowerTruncation (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (U:Set V) (q:ℤ)
    (hcap:∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classOfComplex Q ((lowerTruncation Q E hE q).negativeTwist Q α))=
      classLayer Q q (classOfComplex Q (E.negativeTwist Q α)) := by
  let f:=lowInclusion Q E _ (levelDownClosed Q E hE q)
  let R:=upperTruncation Q E hE q
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) R:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      (((lowConeReduction Q E (lowerLevelSet Q E q) (levelDownClosed Q E hE q)).negativeTwistModern Q α).trans Q
        (negativeTwistFar Q R U (capped_upperTruncation_far Q E hE U q hcap) α hα))
  apply classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) R e q
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠q-1 ∧ (E.placement j).level≠q
  omega

lemma negativeLayer_top (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (q:ℤ) (hhi:∀ i,(E.placement i).level≤q) (α:V) :
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q (classOfComplex Q E))) := by
  let f:=highProjection Q E _ (levelDownClosed Q E hE (q-1))
  let D:=(highConePivot Q E _ (levelDownClosed Q E hE (q-1))).reduced Q
  let G:=minimalClassModel Q (classOfComplex Q (D.negativeTwist Q α))
  let e₀:HomotopyEquivalence Q (D.negativeTwist Q α) G.complex:=
    (minimalClassModelEquivalence Q (D.negativeTwist Q α)).symm Q
  have hd:∀ i,(D.placement i).level≤q-2 := by
    intro i
    rw [highConeRetained_level]
    have hi:=i.property
    change (E.placement i).level≤q-1 at hi
    omega
  have hg:∀ i,(G.complex.placement i).level≤q-2 :=
    negativeTwist_upper_bound Q D G.complex hd α (minimalClassModel_minimal Q _) e₀
  have coneIso : ChainIsomorphism Q ((f.cone Q).negativeTwist Q α)
      ((f.negativeTwist Q α).cone Q) := by
    convert negativeTwistCone Q f α using 1
  let e:HomotopyEquivalence Q ((f.negativeTwist Q α).cone Q) G.complex:=
    ((coneIso.toHomotopyEquivalence Q).symm Q).trans Q
      ((((highConeReduction Q E (lowerLevelSet Q E (q-1)) (levelDownClosed Q E hE (q-1))).negativeTwistModern Q α)).trans Q e₀)
  have hh:=classLayer_eq_of_cone_equivalence Q (f.negativeTwist Q α) G.complex e q
    (fun i=>by have hi:=hg i; constructor <;> omega)
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q E))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q (upperTruncation Q E hE (q-1)))) at hh
  rwa [highRestriction_top_eq_layer Q E hE q hhi] at hh

lemma classNegativeTwist_capped_layer (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α:V) (hα:α∈U) :
    classLayer Q q (classNegativeTwist Q α x)=
      classLayer Q q (classNegativeTwist Q α (classLayer Q q x)) := by
  let E:=minimalClassModel Q x
  have hE:=minimalClassModel_minimal Q x
  let L:=lowerTruncation Q E.complex hE q
  have hx:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
  have hl:=negativeLayer_lowerTruncation Q E.complex hE U q hcap α hα
  have ht:=negativeLayer_top Q L (lowerTruncation_minimal Q E.complex hE q) q
    (fun i=>i.property) α
  have he:=classLayer_lowerTruncation Q E.complex hE q
  change classLayer Q q (classNegativeTwist Q α (classOfComplex Q L))=
    classLayer Q q (classNegativeTwist Q α (classOfComplex Q E.complex)) at hl
  rw [hx] at hl he
  exact hl.symm.trans (ht.trans (congrArg (fun y=>classLayer Q q (classNegativeTwist Q α y)) he))

theorem inverseWord_capped_layer (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hcap:ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw:∀ α∈w,α∈U) :
    classLayer Q q (inverseWordAction Q w x)=
      classLayer Q q (inverseWordAction Q w (classLayer Q q x)) := by
  induction w generalizing x with
  | nil=>exact (classLayer_idempotent Q x q).symm
  | cons α w ih=>
    have hα:=hw α (by simp)
    have hw':∀ β∈w,β∈U:=fun β hβ=>hw β (by simp [hβ])
    have hc:=classNegativeTwist_capped_layer Q x U q hcap α hα
    have hy:=classCapOn_of_upper Q (classLayer Q q x) (Q.closedNeighborhood U) q
      (classLayer_upperBound Q x q)
    exact (ih _ (classNegativeTwist_capOn Q x U q hcap α hα) hw').trans
      ((congrArg (fun y=>classLayer Q q (inverseWordAction Q w y)) hc).trans
        (ih _ (classNegativeTwist_capOn Q _ U q hy α hα) hw').symm)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
