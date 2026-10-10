import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseWordAction

namespace OAI

namespace HarmonicArtin.ReversibleQuiver
universe u
variable {V A : Type u} (Q : ReversibleQuiver V A)

def closedNeighborhood (U : Set V) : Set V :=
  {β | β∈U ∨ ∃ α∈U, ∃ a : A,Q.source a=α ∧ Q.target a=β}

lemma mem_closedNeighborhood {U : Set V} {α : V} (hα : α∈U) :
    α∈Q.closedNeighborhood U := Or.inl hα

lemma corner_target_mem_neighborhood {U : Set V} {α β : V} (hα : α∈U)
    (p : Zigzag.CornerPath Q α β) : β∈Q.closedNeighborhood U := by
  rcases p with ⟨x,hs,ht⟩
  rcases x with v|a|v
  · exact Or.inl (by simp only [Path.source, Path.target] at hs ht; exact ht ▸ hs.symm ▸ hα)
  · exact Or.inr ⟨α,hα,a,hs,ht⟩
  · exact Or.inl (by simp only [Path.source, Path.target] at hs ht; exact ht ▸ hs.symm ▸ hα)

namespace Zigzag.BasedComplex
open Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {K : Type*} [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def ClassCapOn (x : FiniteHomotopyClass Q (K:=K)) (U : Set V) (q : ℤ) : Prop :=
  ∀ i,((minimalClassModel Q x).complex.placement i).color∈U →
    ((minimalClassModel Q x).complex.placement i).level≤q

omit [Fintype V] [DecidableEq A] in
lemma ClassCapOn.mono {x : FiniteHomotopyClass Q (K:=K)} {U T : Set V} {q : ℤ}
    (h : ClassCapOn Q x U q) (hT : T⊆U) : ClassCapOn Q x T q := fun i hi=>h i (hT hi)

omit [Fintype V] [DecidableEq A] in
lemma classCapOn_of_upper (x : FiniteHomotopyClass Q (K:=K)) (U : Set V) (q : ℤ)
    (h : ClassUpperBound Q q x) : ClassCapOn Q x U q := fun i _=>h i

lemma reducedNegativeAmplitudeTwist_cap {I : Type u} [Fintype I] [DecidableEq I]
    (E : BasedComplex Q (K:=K) I) (U : Set V) (q : ℤ)
    (hcap : ∀ i,(E.placement i).color∈Q.closedNeighborhood U → (E.placement i).level≤q)
    (α : V) (hα : α∈U) :
    ∀ k,((reducedNegativeAmplitudeTwist Q E α).placement k).color∈Q.closedNeighborhood U →
      ((reducedNegativeAmplitudeTwist Q E α).placement k).level≤q := by
  intro k hk
  rw [reducedNegativeAmplitudeTwist_placement] at hk ⊢
  rcases k with p|i
  · have hi:=hcap p.val.1 (Q.corner_target_mem_neighborhood hα p.val.2)
    have hp:=Path.length_cases p.val.2.val
    have hn:=p.property
    dsimp only [GeneratorPlacement.level] at hi ⊢
    rcases hp with hp|hp|hp <;> omega
  · exact hcap i.val hk

theorem classNegativeTwist_capOn (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (α : V) (hα : α∈U) :
    ClassCapOn Q (classNegativeTwist Q α x) (Q.closedNeighborhood U) q := by
  let E:=minimalClassModel Q x
  let y:=classNegativeTwist Q α x
  let F:=minimalClassModel Q y
  have he : classOfComplex Q (E.complex.negativeTwist Q α)=classOfComplex Q F.complex := by
    change classNegativeTwist Q α (classOfComplex Q E.complex)=classOfComplex Q F.complex
    have hx : classOfComplex Q E.complex=x := minimalClassModel_class Q x
    have hy : classOfComplex Q F.complex=y := minimalClassModel_class Q y
    rw [hx,hy]
  obtain ⟨e⟩:=Quotient.exact he
  have reduction : HomotopyEquivalence Q (E.complex.negativeTwist Q α)
      (reducedNegativeAmplitudeTwist Q E.complex α) := by
    convert negativeAmplitudeTwistReduction Q E.complex α using 1
  exact minimal_bound_transport Q (reducedNegativeAmplitudeTwist Q E.complex α) F.complex
    (minimalClassModel_minimal Q y)
    ((reduction.symm Q).trans Q e)
    (fun p=>p.color∈Q.closedNeighborhood U → p.level≤q)
    (reducedNegativeAmplitudeTwist_cap Q E.complex U q hcap α hα)

lemma inverseWord_capOn (w : List V) (x : FiniteHomotopyClass Q (K:=K))
    (U : Set V) (q : ℤ) (hcap : ClassCapOn Q x (Q.closedNeighborhood U) q)
    (hw : ∀ α∈w,α∈U) :
    ClassCapOn Q (inverseWordAction Q w x) (Q.closedNeighborhood U) q := by
  induction w generalizing x with
  | nil => exact hcap
  | cons α w ih =>
    exact ih _ (classNegativeTwist_capOn Q x U q hcap α (hw α (by simp)))
      (fun β hβ=>hw β (by simp [hβ]))

end Zigzag.BasedComplex
end HarmonicArtin.ReversibleQuiver

end OAI
