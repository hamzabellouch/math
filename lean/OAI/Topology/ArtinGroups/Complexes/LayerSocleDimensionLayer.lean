import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureLayerSelf

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I:Type u} [Fintype I] [DecidableEq I]

lemma classLayerSocleDimension_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerSocleDimension Q q α c (classLayer Q q x)=classLayerSocleDimension Q q α c x := by
  let E:=((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q)
  have hE:∀ i,(E.placement i).level=q:=fun i=>i.property
  change classLayerSocleDimension Q q α c (classOfComplex Q E)=Module.finrank K (coefficientSocle Q E α c)
  rw [classLayerSocleDimension_minimal Q E (pure_minimal Q E hE)]
  exact ((pureLayerSelf Q E hE).coefficientSocle Q hE (fun i=>i.property) α c).finrank_eq.symm

lemma classLayerTopDimension_layer (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ) (α:V) (c:ℤ) :
    classLayerTopDimension Q q α c (classLayer Q q x)=classLayerTopDimension Q q α c x := by
  let E:=((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) q)
  have hE:∀ i,(E.placement i).level=q:=fun i=>i.property
  change classLayerTopDimension Q q α c (classOfComplex Q E)=Module.finrank K (coefficientTopDual Q E α c)
  rw [classLayerTopDimension_minimal Q E (pure_minimal Q E hE)]
  exact ((pureLayerSelf Q E hE).coefficientTopDual Q hE (fun i=>i.property) α c).finrank_eq.symm

omit [Fintype V] [DecidableEq A] in
lemma classLayer_lowerTruncation_le (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (d q:ℤ) (hd:d≤q) :
    classLayer Q d (classOfComplex Q (lowerTruncation Q E hE q))=
      classLayer Q d (classOfComplex Q E) := by
  apply classLayer_eq_of_cone_equivalence Q (lowInclusion Q E _ (levelDownClosed Q E hE q))
    (upperTruncation Q E hE q) (lowConeReduction Q E _ _) d
  intro j
  have hj:=j.property
  change ¬(E.placement j).level≤q at hj
  change (E.placement j).level≠d-1 ∧ (E.placement j).level≠d
  omega

lemma classLayerTopDimension_congr_layer {x y:FiniteHomotopyClass Q (K:=K)} (q:ℤ)
    (h:classLayer Q q x=classLayer Q q y) (α:V) (c:ℤ) :
    classLayerTopDimension Q q α c x=classLayerTopDimension Q q α c y := by
  rw [← classLayerTopDimension_layer Q x q α c,h,classLayerTopDimension_layer]

lemma classLayerSocleDimension_congr_layer {x y:FiniteHomotopyClass Q (K:=K)} (q:ℤ)
    (h:classLayer Q q x=classLayer Q q y) (α:V) (c:ℤ) :
    classLayerSocleDimension Q q α c x=classLayerSocleDimension Q q α c y := by
  rw [← classLayerSocleDimension_layer Q x q α c,h,classLayerSocleDimension_layer]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
