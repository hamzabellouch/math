import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LayerVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem bottomSocle_zero_of_test_cycle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (hzero:∀ y:TestIndex Q E.placement α→K,
      (∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
        ((E.testComplex Q α).placement i).cochain=c)→y i=0)→
      Matrix.vecMul y ((E.testComplex Q α).differential.map (vertexHom Q α))=0→y=0) :
    coefficientSocle Q (E.pureLayer Q hE d) α c=⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  change x=0
  let y:=layerVector Q E d x
  have hy:y∈coefficientSocle Q E α c:=layerVector_socle Q E hE d α c hx
  have hs:∀ i,(E.placement i).level≠d→y i=0:=layerVector_support Q E d x
  have hts:∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
      ((E.testComplex Q α).placement i).cochain=c)→
      unitTestVector Q E.placement α y i=0 := by
    intro i hi
    change y i.1 * pathCoordinates Q (vertexId Q α) i.2.val=0
    by_cases hp:Sum.inl α=i.2.val
    · rw [vertex_coordinates,ite_eq_left hp,_root_.mul_one]
      by_cases hl:(E.placement i.1).level=d
      · apply hy.1
        right
        intro hc
        apply hi
        constructor
        · change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d
          rw [← hp]
          simpa [Path.length,GeneratorPlacement.level] using hl
        · exact hc
      · exact hs i.1 hl
    · rw [vertex_coordinates,ite_eq_right hp,MulZeroClass.mul_zero]
  have hz:=hzero (unitTestVector Q E.placement α y) hts
    (unitTestVector_bottom_cycle Q E hE d hfloor α c hy hs)
  have hy0:y=0 := by
    have hh:=congrArg (sumUnitTest Q E.placement α) hz
    rw [sumUnitTest_unit Q E.placement α y (fun i h=>hy.1 i (Or.inl h)),map_zero] at hh
    exact hh
  funext i
  have hh:=congrFun hy0 i.val
  change (if h:(E.placement i.val).level=d then x ⟨i.val,h⟩ else 0)=0 at hh
  split_ifs at hh with hi
  · exact hh
  · exact (hi i.property).elim

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
