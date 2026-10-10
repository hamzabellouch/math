import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistOtherTest

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassBottomSocleZero (d:ℤ) (J:Set V) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ α∈J,∀ c,classLayerSocleDimension Q d α c x=0

theorem classPositiveTwist_other_bottom_socle_zero
    (α β:V) (hne:β≠α) (x:FiniteHomotopyClass Q (K:=K)) {d c:ℤ}
    (hx:ClassLowerBound Q d x)
    (hα:classLayerSocleDimension Q d α (c+1) x=0)
    (hβ:classLayerSocleDimension Q d β c x=0) :
    classLayerSocleDimension Q d β c (classPositiveTwist Q α x)=0 := by
  let E:=minimalClassModel Q x
  let y:=classPositiveTwist Q α x
  let F:=minimalClassModel Q y
  have he:classOfComplex Q (E.complex.positiveTwist Q α)=classOfComplex Q F.complex := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hE:classOfComplex Q E.complex=x:=minimalClassModel_class Q x
    have hF:classOfComplex Q F.complex=y:=minimalClassModel_class Q y
    rw [hE,hF]
  obtain ⟨e⟩:=Quotient.exact he
  apply Submodule.finrank_eq_zero.mpr
  exact positiveTwist_other_bottom_socle_zero Q E.complex (minimalClassModel_minimal Q x)
    F.complex (minimalClassModel_minimal Q y) hx α β hne
    (Submodule.finrank_eq_zero.mp hα) (Submodule.finrank_eq_zero.mp hβ) e

theorem classPositiveTwist_preserves_open_socle
    (hn:∀ a,Q.source a≠Q.target a) (α:V) (J:Set V) (hα:α∈J)
    (x:FiniteHomotopyClass Q (K:=K)) {d:ℤ} (hx:ClassLowerBound Q d x)
    (hJ:ClassBottomSocleZero Q d J x) :
    ClassBottomSocleZero Q d J (classPositiveTwist Q α x) := by
  intro β hβ c
  by_cases he:β=α
  · subst β
    exact classPositiveTwist_bottom_socle_zero Q hn α x hx c
  · exact classPositiveTwist_other_bottom_socle_zero Q α β he x hx (hJ α hα (c+1)) (hJ β hβ c)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
