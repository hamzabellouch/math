import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistLowerBound
import OAI.Topology.ArtinGroups.Complexes.ReducedNoTopDivisor
import OAI.Topology.ArtinGroups.Complexes.OutsideCap

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

lemma positiveWord_lower_bound (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    {d:ℤ} (hx:ClassLowerBound Q d x) : ClassLowerBound Q d (positiveWordAction Q w x) := by
  induction w with
  | nil => exact hx
  | cons α w ih => exact classPositiveTwist_lower_bound Q α _ ih

lemma positiveWord_outside_cap (w:List V) (x:FiniteHomotopyClass Q (K:=K))
    (U:Set V) (d:ℤ) (hw:∀ s∈w,s∈U) (hx:ClassOutsideCap Q x U d) :
    ClassOutsideCap Q (positiveWordAction Q w x) U d := by
  induction w with
  | nil => exact hx
  | cons α w ih =>
    exact classPositiveTwist_outside_cap Q _ U d α (hw α (by simp))
      (ih (fun s hs=>hw s (List.mem_cons_of_mem _ hs)))

theorem reducedWord_layer_bounds (hn:∀ a,Q.source a≠Q.target a)
    (U:Set V)
    (hU:∀ α∈U,∀ β∈U,α=β ∨ OrthogonalVertices Q α β ∨ Nonempty (SimpleEdge Q α β))
    (x:FiniteHomotopyClass Q (K:=K)) (a b:ℤ)
    (hlo:ClassLowerBound Q a x) (hhi:ClassUpperBound Q b x)
    (w:List V) (hw:∀ s∈w,s∈U)
    (hr:(ordinaryCoxeterMatrix Q).toCoxeterSystem.IsReduced w) :
    ClassLowerBound Q a (positiveWordAction Q w x) ∧
      ClassUpperBound Q (b+1) (positiveWordAction Q w x) := by
  refine ⟨positiveWord_lower_bound Q w x hlo,?_⟩
  apply classUpperBound_of_test_and_outside Q _ U (b+1)
  · have he : b+2+1=(b+1)+2 := by omega
    rw [← he]
    exact reducedWord_testUpper Q hn U hU x (b+2)
      (classTestUpper_of_generator_cap Q x b hhi U) w hw hr
  · have hh:=positiveWord_outside_cap Q w x U b hw (classOutsideCap_of_upper Q x U b hhi)
    intro i hi
    have hb:=hh i hi
    omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
