import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.Intermediate

namespace OAI

/-! Capacity Dichotomy. -/

section

noncomputable section
namespace UniversalTensorSquare
open Saxl

theorem capacity_dichotomy (μ : YoungDiagram) {M r : ℕ}
    (hM : 9 ≤ M) (hr : 0 < r)
    (hbound : if M % 2 = 1 then 2*r ≤ M-1 else 2*r ≤ 3*M+4)
    (hexc : ¬exceptionalPair M r)
    (hn : μ.card = (staircase M).card + 2*r) :
    colPrefix μ 4 ≤ 2*M-2 ∨ colPrefix μ.transpose 4 ≤ 2*M-2 ∨
      BandTest M r μ ∨ BandTest M r μ.transpose := by
  by_cases hs : colPrefix μ 4 ≤ 2*M-2
  · exact Or.inl hs
  apply Or.inr
  by_cases ht : colPrefix μ.transpose 4 ≤ 2*M-2
  · exact Or.inl ht
  apply Or.inr
  have hH : 2*M-1 ≤ colPrefix μ 4 := by omega
  have hW : 2*M-1 ≤ rowPrefix μ 4 := by
    simp only [colPrefix, YoungDiagram.transpose_transpose] at ht
    omega
  by_cases hlarge : 22 ≤ M
  · apply capacity_large μ M r hlarge _ hn hH hW
    split_ifs at hbound <;> omega
  · exact capacity_intermediate μ hM (by omega) ⟨hr,hbound,hexc⟩ hn hH hW

theorem fixed_degree_capacity_dichotomy (n : ℕ) (hn : 64 < n)
    (hr : 0 < remainderPairs n)
    (hexc : ¬exceptionalPair (staircaseIndex n) (remainderPairs n))
    (μ : YoungDiagram) (hμ : μ.card = n) :
    colPrefix μ 4 ≤ 2*staircaseIndex n-2 ∨
      colPrefix μ.transpose 4 ≤ 2*staircaseIndex n-2 ∨
      BandTest (staircaseIndex n) (remainderPairs n) μ ∨
      BandTest (staircaseIndex n) (remainderPairs n) μ.transpose := by
  have hM : 9 ≤ staircaseIndex n := by
    by_contra h
    have := degree_le_64_of_small_index n (by omega)
    omega
  apply capacity_dichotomy μ hM hr _ hexc
    (hμ.trans (degree_eq n).symm)
  split_ifs with ho
  · exact remainderPairs_bound_odd n ho
  · exact remainderPairs_bound_even n (by omega)

end UniversalTensorSquare
end
end

end OAI
