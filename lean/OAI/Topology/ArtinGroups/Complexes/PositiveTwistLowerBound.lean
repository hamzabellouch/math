import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ReducedAmplitudeTwistLevel
import OAI.Topology.ArtinGroups.Complexes.TokenShift
import OAI.Topology.ArtinGroups.Complexes.Test
import OAI.Topology.ArtinGroups.Complexes.UpperBound
import OAI.Topology.ArtinGroups.Complexes.LayerVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem positiveTwist_lower_bound
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,d≤(E.placement i).level) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) :
    ∀ j,d≤(F.placement j).level := by
  have reduction : HomotopyEquivalence Q (E.positiveTwist Q α)
      (reducedAmplitudeTwist Q E α) := by
    convert amplitudeTwistReduction Q E α using 1
  apply minimal_bound_transport Q (reducedAmplitudeTwist Q E α) F hF
    ((reduction.symm Q).trans Q e) (fun p=>d≤p.level)
  intro k
  obtain ⟨i,hi⟩:=reducedAmplitudeTwist_level Q E α k
  have hh:=hE i
  rcases hi with hi|⟨hi,_⟩ <;> omega

theorem positiveTwist_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    {d:ℤ} (hE:∀ i,d≤(E.placement i).level) (α:V) (hF:F.IsMinimal Q)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) (c:ℤ) :
    coefficientSocle Q (F.pureLayer Q hF d) α c=⊥ := by
  let g:=((e.symm Q).test Q α).trans Q (positiveTwist_testShift Q hn E α)
  apply bottomSocle_zero_of_test_equiv_above Q F hF
    (positiveTwist_lower_bound Q E F hE α hF e) α ((E.testComplex Q α).tokenShift Q) g _ c
  intro j
  have hh:=hE j.1
  have hl:0≤Path.length j.2.val := by
    rcases j.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [GeneratorPlacement.level,tokenShift,testComplex,testPlacement] at *
  omega

theorem classPositiveTwist_lower_bound
    (α:V) (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) :
    ClassLowerBound Q d (classPositiveTwist Q α x) := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  exact positiveTwist_lower_bound Q E.complex F.complex hx α
    (minimalClassModel_minimal Q y) e

theorem classPositiveTwist_bottom_socle_zero
    (hn:∀ a,Q.source a≠Q.target a) (α:V)
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x) (c:ℤ) :
    classLayerSocleDimension Q d α c (classPositiveTwist Q α x)=0 := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  change Module.finrank K (coefficientSocle Q (F.complex.pureLayer Q
    (minimalClassModel_minimal Q y) d) α c)=0
  rw [positiveTwist_bottom_socle_zero Q hn E.complex F.complex hx α
    (minimalClassModel_minimal Q y) e c]
  simp

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
