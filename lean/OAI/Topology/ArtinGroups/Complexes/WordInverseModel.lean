import Mathlib
import OAI.Topology.ArtinGroups.Complexes.CanonicalWordLow
import OAI.Topology.ArtinGroups.Complexes.PositiveWord

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def wordInverseModel (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  minimalClassModel Q (inverseWordAction Q w x)

noncomputable def wordLowModel (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.ofComplex Q (lowerTruncation Q (wordInverseModel Q w x).complex
    (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1))

noncomputable def canonicalLowSource (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.positiveWord Q w (wordLowModel Q w q x)
noncomputable def canonicalLowTarget (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :=
  FiniteModel.positiveWord Q w (wordInverseModel Q w x)

noncomputable def canonicalLowMap (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    Map Q (canonicalLowSource Q w q x).complex (canonicalLowTarget Q w x).complex :=
  FiniteModel.positiveWordMap Q w (lowInclusion Q (wordInverseModel Q w x).complex
    (lowerLevelSet Q (wordInverseModel Q w x).complex (q-1))
    (levelDownClosed Q _ (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1)))

lemma canonicalLowSource_class (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    classOfComplex Q (canonicalLowSource Q w q x).complex=canonicalWordLow Q w q x := by
  rw [canonicalLowSource,FiniteModel.positiveWord_class]
  rfl

lemma canonicalLowTarget_class (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) :
    classOfComplex Q (canonicalLowTarget Q w x).complex=x := by
  rw [canonicalLowTarget,FiniteModel.positiveWord_class]
  change positiveWordAction Q w (classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex)=x
  have he:classOfComplex Q (minimalClassModel Q (inverseWordAction Q w x)).complex=
      inverseWordAction Q w x:=minimalClassModel_class Q _
  rw [he,positive_inverseWord Q hn]

theorem canonicalLowMap_homMono (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (T:FiniteModel.{u} Q (K:=K)) (hT:ClassUpperBound Q q (classOfComplex Q T.complex)) :
    HomMonoFrom Q T.complex (canonicalLowMap Q w q x) := by
  let R:=wordInverseModel Q w (classOfComplex Q T.complex)
  have hR:∀ i,(R.complex.placement i).level≤(q-1)+1 := by
    intro i
    have hh:=inverseWord_upper_bound Q w (classOfComplex Q T.complex) hT i
    change (R.complex.placement i).level≤q at hh
    omega
  have hm:=FiniteModel.positiveWord_homMono Q hn w R (wordLowModel Q w q x)
    (wordInverseModel Q w x)
    (lowInclusion Q (wordInverseModel Q w x).complex
      (lowerLevelSet Q (wordInverseModel Q w x).complex (q-1))
      (levelDownClosed Q _ (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1)))
    (lowInclusion_homMono Q R.complex (wordInverseModel Q w x).complex
      (minimalClassModel_minimal Q (inverseWordAction Q w x)) (q-1) hR)
  have he:classOfComplex Q (FiniteModel.positiveWord Q w R).complex=classOfComplex Q T.complex :=
    canonicalLowTarget_class Q hn w (classOfComplex Q T.complex)
  obtain ⟨e⟩:=Quotient.exact he
  exact hm.sourceEquivalence Q e

theorem canonicalReducedWordLow_subobject (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ∃ E F:FiniteModel.{u} Q (K:=K),
      classOfComplex Q E.complex=canonicalWordLow Q w q x ∧
      classOfComplex Q F.complex=x ∧
      (∀ i,(E.complex.placement i).level=q) ∧
      (∀ j,(F.complex.placement j).level=q) ∧
      ∃ f:Map Q E.complex F.complex,
        ∀ T:FiniteModel.{u} Q (K:=K), ClassUpperBound Q q (classOfComplex Q T.complex) →
          HomMonoFrom Q T.complex f := by
  let E:=minimalClassModel Q (canonicalWordLow Q w q x)
  let F:=minimalClassModel Q x
  have hc:=canonicalReducedWordLow_pure Q hn U hU x q hlo hhi w hw hr
  have hE:classOfComplex Q E.complex=canonicalWordLow Q w q x:=minimalClassModel_class Q _
  have hF:classOfComplex Q F.complex=x:=minimalClassModel_class Q _
  have he:classOfComplex Q E.complex=classOfComplex Q (canonicalLowSource Q w q x).complex :=
    hE.trans (canonicalLowSource_class Q w q x).symm
  have hf:classOfComplex Q (canonicalLowTarget Q w x).complex=classOfComplex Q F.complex :=
    (canonicalLowTarget_class Q hn w x).trans hF.symm
  obtain ⟨e⟩:=Quotient.exact he
  obtain ⟨f⟩:=Quotient.exact hf
  refine ⟨E,F,hE,hF,fun i=>le_antisymm (hc.2 i) (hc.1 i),
    fun j=>le_antisymm (hhi j) (hlo j),
    (e.forward.comp Q (canonicalLowMap Q w q x)).comp Q f.forward,?_⟩
  intro T hT
  exact ((e.homMonoFrom Q T.complex).comp Q
    (canonicalLowMap_homMono Q hn w q x T hT)).comp Q (f.homMonoFrom Q T.complex)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
