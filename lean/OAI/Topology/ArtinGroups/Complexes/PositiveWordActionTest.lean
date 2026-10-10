import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma positiveWordAction_testUpper (hn:∀a,Q.source a≠Q.target a)
    (w:List V) (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (hw:∀s∈w,s∈U)
    (t:ℤ) (hx:ClassTestUpper Q x U t) :
    ClassTestUpper Q (positiveWordAction Q w x) U (t+w.length) := by
  induction w with
  | nil=>simpa only [positiveWordAction,List.length_nil,Int.natCast_zero,add_zero] using hx
  | cons α w ih=>
    have h:=classPositiveTwist_testUpper Q hn (positiveWordAction Q w x) U α (hw α (by simp))
      (ih (fun β hβ=>hw β (List.mem_cons_of_mem _ hβ)))
    simpa only [positiveWordAction,List.length_cons,Int.natCast_add,Int.natCast_one,add_assoc] using h

lemma exists_top_test (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (t:ℤ)
    (hex:∃n:ℕ,ClassTestUpper Q x U (t+n)) (hnot:¬ClassTestUpper Q x U t) :
    ∃l:ℤ,t<l ∧ ClassTestUpper Q x U l ∧ ∃α∈U,∃c,¬ClassTestExact Q α l c x := by
  let n:=Nat.find hex
  have hn:ClassTestUpper Q x U (t+n):=Nat.find_spec hex
  have hpos:0<n:=by
    by_contra hh
    have :n=0:=by omega
    apply hnot
    simpa only [this,Int.natCast_zero,add_zero] using hn
  have hprev:¬ClassTestUpper Q x U (t+n-1):=by
    intro hh
    have he:t+((n-1:ℕ):ℤ)=t+n-1:=by omega
    have :=Nat.find_min hex (show n-1<n by omega)
    exact this (by rw [he]; exact hh)
  refine ⟨t+n,by omega,hn,?_⟩
  by_contra hh
  apply hprev
  intro α hα l hl c
  by_cases he:l=t+n
  · subst l
    by_contra hc
    exact hh ⟨α,hα,c,hc⟩
  · exact hn α hα l (by omega) c

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
