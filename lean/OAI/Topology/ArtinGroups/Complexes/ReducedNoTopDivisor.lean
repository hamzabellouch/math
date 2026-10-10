import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTopDivisor
import OAI.Topology.ArtinGroups.Coxeter.OrdinaryCoxeterMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

omit [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] in
lemma reduced_no_top_divisor {α:V} {w v:List V}
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced (α::w))
    (h:PositiveBraidRel Q w (α::v)) : False := by
  let cs := (ordinaryCoxeterMatrix Q).toCoxeterSystem
  have he:cs.wordProd (α::w)=cs.wordProd v := by
    rw [CoxeterSystem.wordProd_cons,PositiveBraidRel.coxeter_eq Q h,
      CoxeterSystem.wordProd_cons,CoxeterSystem.simple_mul_simple_cancel_left]
  have hh:=cs.length_wordProd_le v
  have hl:=PositiveBraidRel.length_eq Q h
  change cs.length (cs.wordProd (α::w))=(α::w).length at hr
  rw [he] at hr
  simp only [List.length_cons] at hr hl
  omega

theorem reducedWord_testUpper (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (t:ℤ) (hx:ClassTestUpper Q x U t)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassTestUpper Q (positiveWordAction Q w x) U (t+1) := by
  induction w with
  | nil => exact fun α hα l hl c=>hx α hα l (by omega) c
  | cons α w ih =>
    have hα:α∈U:=hw α (by simp)
    have hw':∀ s∈w,s∈U:=fun s hs=>hw s (List.mem_cons_of_mem _ hs)
    have hr':(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w:=by
      simpa only [List.drop_succ_cons,List.drop_zero] using hr.drop 1
    have ht:=ih hw' hr'
    apply (classPositiveTwist_testUpper_iff Q hn _ U α hα ht).mpr
    intro c
    by_contra htop
    obtain ⟨v,hv⟩:=positive_top_divisor Q hn U hU x t hx w hw' α hα (t+1)
      (by omega) ht c htop
    exact reduced_no_top_divisor Q hr hv

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
