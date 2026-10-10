import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshGraphNilpotence
import OAI.Topology.ArtinGroups.ParabolicIntersections.MeshNilpotence
import Mathlib.RingTheory.Congruence.Basic

namespace OAI

/-! The simple graph of a finite induced reversible quiver. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A : Type} (Q : ReversibleQuiver V A) (U : Set V)

def QuiverSimpleOn : Prop := ∀ a b : A, Q.source a∈U → Q.target a∈U →
  Q.source a=Q.source b → Q.target a=Q.target b → a=b

def meshQuiverGraph (hloop : ∀ a, Q.source a≠Q.target a) : SimpleGraph U where
  Adj u v := ∃ a, Q.source a=u.val ∧ Q.target a=v.val
  symm := ⟨by
    rintro u v ⟨a,hs,ht⟩
    exact ⟨Q.reverse a,(Q.source_reverse a).trans ht,(Q.target_reverse a).trans hs⟩⟩
  loopless := ⟨by
    rintro u ⟨a,hs,ht⟩
    exact hloop a (hs.trans ht.symm)⟩

variable (hloop : ∀ a, Q.source a≠Q.target a)

noncomputable def meshChosenArrow {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) : A :=
  h.choose

lemma meshChosenArrow_source {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) :
    Q.source (meshChosenArrow Q U hloop h)=u.val := h.choose_spec.1

lemma meshChosenArrow_target {u v : U} (h : (meshQuiverGraph Q U hloop).Adj u v) :
    Q.target (meshChosenArrow Q U hloop h)=v.val := h.choose_spec.2

lemma meshChosenArrow_eq (hsimple : QuiverSimpleOn Q U) {u v : U}
    (h : (meshQuiverGraph Q U hloop).Adj u v) (a : A)
    (hs : Q.source a=u.val) (ht : Q.target a=v.val) : meshChosenArrow Q U hloop h=a :=
  hsimple _ a ((meshChosenArrow_source Q U hloop h).symm ▸ u.property)
    ((meshChosenArrow_target Q U hloop h).symm ▸ v.property)
    ((meshChosenArrow_source Q U hloop h).trans hs.symm)
    ((meshChosenArrow_target Q U hloop h).trans ht.symm)

lemma meshChosenArrow_reverse (hsimple : QuiverSimpleOn Q U) {u v : U}
    (h : (meshQuiverGraph Q U hloop).Adj u v) :
    meshChosenArrow Q U hloop h.symm=Q.reverse (meshChosenArrow Q U hloop h) := by
  apply meshChosenArrow_eq Q U hloop hsimple
  · rw [Q.source_reverse,meshChosenArrow_target]
  · rw [Q.target_reverse,meshChosenArrow_source]

noncomputable def meshQuiverNeighborEquiv (hsimple : QuiverSimpleOn Q U) (v : U) :
    {u : U // (meshQuiverGraph Q U hloop).Adj u v} ≃
      {a : A // Q.source a=v.val ∧ Q.target a∈U} where
  toFun u := ⟨meshChosenArrow Q U hloop u.property.symm,
    meshChosenArrow_source Q U hloop u.property.symm,
    (meshChosenArrow_target Q U hloop u.property.symm).symm ▸ u.val.property⟩
  invFun a := ⟨⟨Q.target a.val,a.property.2⟩,
    ⟨Q.reverse a.val,Q.source_reverse a.val,(Q.target_reverse a.val).trans a.property.1⟩⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    exact meshChosenArrow_target Q U hloop u.property.symm
  right_inv a := by
    apply Subtype.ext
    apply meshChosenArrow_eq Q U hloop hsimple
    · exact a.property.1
    · rfl

end HarmonicArtin.ParabolicIntersections

end OAI
