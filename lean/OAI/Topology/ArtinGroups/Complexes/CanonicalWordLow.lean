import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseWordAction
import OAI.Topology.ArtinGroups.Complexes.TargetLow

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def canonicalWordLow (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K)) :
    FiniteHomotopyClass Q (K:=K) :=
  positiveWordAction Q w (classLowerTruncation Q (q-1) (inverseWordAction Q w x))

lemma canonicalWordLow_floor (hn:∀ a,Q.source a≠Q.target a)
    (w:List V) (q:ℤ) (x:FiniteHomotopyClass Q (K:=K))
    (hx:ClassLowerBound Q q x) : ClassLowerBound Q q (canonicalWordLow Q w q x) := by
  apply classLowerBound_of_placed_vanishing Q _ q
  intro p hp
  let P:=classOfComplex Q (placedProjective Q (K:=K) p)
  let R:=inverseWordAction Q w P
  let N:=inverseWordAction Q w x
  have hP:ClassUpperBound Q p.level P:=
    classUpperBound_of_representative Q _ (fun _=>le_rfl)
  have hR:ClassUpperBound Q ((q-1)+1) R := by
    have hb:=inverseWord_upper_bound Q w P hP
    intro i
    exact le_trans (hb i) (by omega)
  have hz:classHomDimension Q 0 0 R N=0 := by
    rw [← positiveWord_homDimension Q hn w R N 0 0]
    change classHomDimension Q 0 0
      (positiveWordAction Q w (inverseWordAction Q w P))
      (positiveWordAction Q w (inverseWordAction Q w x))=0
    rw [positive_inverseWord Q hn,positive_inverseWord Q hn]
    exact classHomDimension_zero_of_layer_gap Q P x p.level q hP hx hp
  have ht:=classLowerTruncation_homDimension_zero Q R N (q-1) hR hz
  have ht':classHomDimension Q 0 0 (positiveWordAction Q w R)
      (positiveWordAction Q w (classLowerTruncation Q (q-1) N))=0 := by
    rw [positiveWord_homDimension Q hn]
    exact ht
  change classHomDimension Q 0 0 P (canonicalWordLow Q w q x)=0
  simpa only [R,N,positive_inverseWord Q hn,canonicalWordLow] using ht'

theorem canonicalReducedWordLow_pure (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (q:ℤ)
    (hlo:ClassLowerBound Q q x) (hhi:ClassUpperBound Q q x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q q (canonicalWordLow Q w q x) ∧
      ClassUpperBound Q q (canonicalWordLow Q w q x) := by
  refine ⟨canonicalWordLow_floor Q hn w q x hlo,?_⟩
  have hN:ClassLowerBound Q (q-1) (inverseWordAction Q w x):=
    (inverseReducedWord_layer_bounds Q hn U hU x q q hlo hhi w hw hr).1
  have hlow:=classLowerTruncation_floor Q (q-1) (q-1) (inverseWordAction Q w x) hN
  have hcap:=classLowerTruncation_cap Q (q-1) (inverseWordAction Q w x)
  have h:= (reducedWord_layer_bounds Q hn U hU
    (classLowerTruncation Q (q-1) (inverseWordAction Q w x)) (q-1) (q-1)
      hlow hcap w hw hr).2
  have he:q-1+1=q:=by omega
  rw [he] at h
  exact h

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
