import Mathlib
import OAI.Topology.ArtinGroups.Complexes.WordInverseModel
import OAI.Topology.ArtinGroups.Complexes.Shift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassColorSupport (U:Set V) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∈U

def ClassOutsideFloor (U:Set V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∉U→
    q≤((minimalClassModel Q x).complex.placement i).level

lemma classNegativeTwist_outside_floor (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (α:V) (hα:α∈U) (h:ClassOutsideFloor Q U q x) :
    ClassOutsideFloor Q U q (classNegativeTwist Q α x) := by
  let E:=minimalClassModel Q x
  let F:=E.complex.negativeTwist Q α
  have hx:classOfComplex Q F=classNegativeTwist Q α x := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classNegativeTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∉U→q≤p.level)
  intro i hi
  rcases i with j|j
  · exact h j hi
  · exact (hi hα).elim

lemma inverseWord_outside_floor (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hw:∀ s∈w,s∈U) (h:ClassOutsideFloor Q U q x) :
    ClassOutsideFloor Q U q (inverseWordAction Q w x) := by
  induction w generalizing x with
  | nil => exact h
  | cons α w ih =>
    exact ih _ (fun s hs=>hw s (List.mem_cons_of_mem _ hs))
      (classNegativeTwist_outside_floor Q x U q α (hw α (by simp)) h)

lemma classPositiveTwist_colorSupport (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (α:V) (hα:α∈U) (h:ClassColorSupport Q U x) :
    ClassColorSupport Q U (classPositiveTwist Q α x) := by
  let E:=minimalClassModel Q x
  let F:=E.complex.positiveTwist Q α
  have hx:classOfComplex Q F=classPositiveTwist Q α x := by
    change classPositiveTwist Q α (classOfComplex Q E.complex)=_
    exact congrArg (classPositiveTwist Q α) (minimalClassModel_class Q x)
  rw [← hx]
  apply minimal_bound_transport Q F _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q F).symm Q) (fun p=>p.color∈U)
  intro i
  rcases i with j|j
  · exact hα
  · exact h j

lemma positiveWord_colorSupport (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (hw:∀ s∈w,s∈U) (h:ClassColorSupport Q U x) :
    ClassColorSupport Q U (positiveWordAction Q w x) := by
  induction w with
  | nil => exact h
  | cons α w ih =>
    exact classPositiveTwist_colorSupport Q _ U α (hw α (by simp))
      (ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs)))

lemma canonicalWordLow_colorSupport (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (q:ℤ) (hw:∀ s∈w,s∈U) (hx:ClassLowerBound Q q x) :
    ClassColorSupport Q U (canonicalWordLow Q w q x) := by
  apply positiveWord_colorSupport Q w _ U hw
  have hf:=inverseWord_outside_floor Q w x U q hw (fun i _=>hx i)
  apply minimal_bound_transport Q _ _ (minimalClassModel_minimal Q _)
    ((minimalClassModelEquivalence Q
      (lowerTruncation Q (minimalClassModel Q (inverseWordAction Q w x)).complex
        (minimalClassModel_minimal Q _) (q-1))).symm Q) (fun p=>p.color∈U)
  intro i
  by_contra hi
  have hh:=hf i hi
  have hl:=i.property
  change ((minimalClassModel Q (inverseWordAction Q w x)).complex.placement i).level≤q-1 at hl
  omega

lemma canonicalReducedWordLow_monic (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (_hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (_hlo:ClassLowerBound Q q x) (_hhi:ClassUpperBound Q q x)
    (w:List V) (_hw:∀ s∈w,s∈U)
    (_hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ∃ f:Map Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex (minimalClassModel Q x).complex,
      ∀ T:FiniteModel.{u} Q (K:=K),ClassUpperBound Q q (classOfComplex Q T.complex)→
        HomMonoFrom Q T.complex f := by
  let E:=minimalClassModel Q (canonicalWordLow Q w q x)
  let F:=minimalClassModel Q x
  have he:classOfComplex Q E.complex=classOfComplex Q (canonicalLowSource Q w q x).complex :=
    (minimalClassModel_class Q _).trans (canonicalLowSource_class Q w q x).symm
  have hf:classOfComplex Q (canonicalLowTarget Q w x).complex=classOfComplex Q F.complex :=
    (canonicalLowTarget_class Q hn w x).trans (minimalClassModel_class Q x).symm
  obtain ⟨e⟩:=Quotient.exact he
  obtain ⟨f⟩:=Quotient.exact hf
  refine ⟨(e.forward.comp Q (canonicalLowMap Q w q x)).comp Q f.forward,?_⟩
  intro T hT
  exact ((e.homMonoFrom Q T.complex).comp Q
    (canonicalLowMap_homMono Q hn w q x T hT)).comp Q (f.homMonoFrom Q T.complex)

theorem canonicalReducedWordLow_halfspace (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w)
    (Y:FiniteModel.{u} Q (K:=K)) (d:ℤ) (hY:∀ i,(Y.complex.placement i).level=d)
    (hsY:∀ α∈U,∀ c,coefficientSocle Q Y.complex α c=⊥)
    (hmid:totalHomDimension Q (minimalClassModel Q x).complex Y.complex (d-q+1)=0) :
    (totalHomDimension Q (minimalClassModel Q x).complex Y.complex (d-q):ℝ)≤
      (generatorVector Q (minimalClassModel Q x).complex-
        generatorVector Q (minimalClassModel Q (canonicalWordLow Q w q x)).complex) ⬝ᵥ
      ((unfoldedCartan Q).mulVec (generatorVector Q Y.complex)) := by
  obtain ⟨f,hm⟩:=canonicalReducedWordLow_monic Q hn U hU x q hlo hhi w hw hr
  have hp:=canonicalReducedWordLow_pure Q hn U hU x q hlo hhi w hw hr
  exact derivedSubobject_cartan_inequality Q _ _ Y.complex
    (fun i=>le_antisymm (hhi i) (hlo i)) (fun i=>le_antisymm (hp.2 i) (hp.1 i)) hY f hm U
    (canonicalWordLow_colorSupport Q w x U q hw hlo) hsY hmid

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
