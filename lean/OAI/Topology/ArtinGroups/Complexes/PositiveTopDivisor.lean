import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRel

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

theorem positive_top_divisor (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t)
    (w:List V) :
    (∀ s∈w,s∈U)→∀ β∈U,∀ l:ℤ,t<l→
      ClassTestUpper Q (positiveWordAction Q w x) U l→
      ∀ c:ℤ,¬ClassTestExact Q β l c (positiveWordAction Q w x)→
        ∃ v,PositiveBraidRel Q w (β::v) := by
  refine (measure (fun w:List V=>w.length)).wf.induction
    (C := fun w => (∀ s∈w,s∈U)→∀ β∈U,∀ l:ℤ,t<l→
      ClassTestUpper Q (positiveWordAction Q w x) U l→
      ∀ c:ℤ,¬ClassTestExact Q β l c (positiveWordAction Q w x)→
        ∃ v,PositiveBraidRel Q w (β::v)) w (fun w ih=>?_)
  intro hw β hβ l hl hout c htop
  cases w with
  | nil => exact (htop (hx β hβ l hl c)).elim
  | cons α w =>
    have hα:α∈U:=hw α (by simp)
    have hw':∀ s∈w,s∈U:=fun s hs=>hw s (List.mem_cons_of_mem _ hs)
    by_cases he:β=α
    · subst β
      exact ⟨w,PositiveBraidRel.refl _⟩
    have htail:ClassTestUpper Q (positiveWordAction Q w x) U l :=
      classPositiveTwist_testUpper_reflect Q hn _ U α hα hout
    have ha:∀ c,ClassTestExact Q α l c (positiveWordAction Q w x) :=
      (classPositiveTwist_testUpper_iff Q hn _ U α hα htail).mp hout
    have hb:¬ClassTestExact Q β l c (positiveWordAction Q w x) := by
      intro hz
      exact htop (classTestExact_positive_other Q _ α β he l c (ha (c+1)) hz)
    obtain ⟨v,hv⟩:=ih w (by change w.length<(α::w).length; simp) hw' β hβ l hl htail c hb
    rcases hU α hα β hβ with heq | hrest
    · exact (he heq.symm).elim
    rcases hrest with ho | hedge
    · exact ⟨α::v,PositiveBraidRel.trans (PositiveBraidRel.cons α hv)
        (PositiveBraidRel.orthogonal ho v)⟩
    obtain ⟨edge⟩ := hedge
    have hvU:∀ s∈v,s∈U := by
      have hh:=PositiveBraidRel.mem_set Q hv U hw'
      exact fun s hs=>hh s (List.mem_cons_of_mem _ hs)
    have hvlen:v.length<(α::w).length := by
      have hh:=PositiveBraidRel.length_eq Q hv
      simp only [List.length_cons] at *
      omega
    have htail':ClassTestUpper Q (classPositiveTwist Q β (positiveWordAction Q v x)) U l := by
      change ClassTestUpper Q (positiveWordAction Q (β::v) x) U l
      rw [← PositiveBraidRel.action_eq Q hn hv x]
      exact htail
    have hvbound:ClassTestUpper Q (positiveWordAction Q v x) U l :=
      classPositiveTwist_testUpper_reflect Q hn _ U β hβ htail'
    have htop':¬ClassTestExact Q β l c
        (classPositiveTwist Q α (classPositiveTwist Q β (positiveWordAction Q v x))) := by
      intro hz
      apply htop
      change ClassTestExact Q β l c (classPositiveTwist Q α (positiveWordAction Q w x))
      rw [PositiveBraidRel.action_eq Q hn hv x]
      exact hz
    have hαtop:¬ClassTestExact Q α l (c+1) (positiveWordAction Q v x) :=
      fun hz=>htop' ((classTestExact_positive_adjacent Q hn _ edge l c).mpr hz)
    obtain ⟨z,hz⟩:=ih v hvlen hvU α hα l hl hvbound (c+1) hαtop
    exact ⟨α::β::z,PositiveBraidRel.trans (PositiveBraidRel.cons α hv)
      (PositiveBraidRel.trans (PositiveBraidRel.cons α (PositiveBraidRel.cons β hz))
        (PositiveBraidRel.adjacent edge z))⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
