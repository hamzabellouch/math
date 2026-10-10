import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ColorBoundary

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]
attribute [local instance] Classical.decEq Classical.propDecidable

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma colorRestriction_top_zero (E:BasedComplex Q (K:=K) I) (q:ℤ) (U:Set V)
    (hp:∀ i,(E.placement i).level=q)
    (hb:∀ i,(E.placement i).color∉colorBoundary Q U)
    (α:V) (hα:α∈U) (c:ℤ)
    (hz:coefficientTopDual Q (colorRestriction Q E U hp hb) α c=⊥) :
    coefficientTopDual Q E α c=⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x=0
  let y:{i:I // (E.placement i).color∈U}→K:=fun i=>x i
  have hxo (i:I) (hi:(E.placement i).color∉U):x i=0 := by
    apply hx.1 i
    left
    intro h
    exact hi (h ▸ hα)
  have hy:y∈coefficientTopDual Q (colorRestriction Q E U hp hb) α c := by
    constructor
    · intro i hi
      exact hx.1 i hi
    · intro i a
      change (∑ j:{i:I //(E.placement i).color∈U},(E.differential i.val j.val).arrow a*x j.val)=0
      rw [← Finset.sum_subtype (Finset.univ.filter fun j:I=>(E.placement j).color∈U)
        (by simp) (fun j:I=>(E.differential i.val j).arrow a*x j),Finset.sum_filter]
      convert hx.2 i.val a using 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj:(E.placement j).color∈U
      · rw [ite_eq_left hj]
      · rw [ite_eq_right hj,hxo j hj,MulZeroClass.mul_zero]
  rw [hz] at hy
  have hy0:y=0:=(Submodule.mem_bot K).mp hy
  funext i
  by_cases hi:(E.placement i).color∈U
  · exact congrFun hy0 ⟨i,hi⟩
  · exact hxo i hi

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
