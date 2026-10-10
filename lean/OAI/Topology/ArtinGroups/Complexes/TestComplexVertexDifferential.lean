import Mathlib
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Complexes.CoefficientSocleRestrictLayer

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I]

lemma testComplex_vertex_differential (E:BasedComplex Q (K:=K) I) (α:V) :
    (E.testComplex Q α).differential.map (vertexHom Q α)=
      testMatrix Q E.placement E.placement α E.differential := by
  apply Matrix.ext
  intro i j
  change ((testMatrix Q E.placement E.placement α E.differential i j) • vertexId Q α).vertex α = _
  simp

lemma test_bottom_length_zero (E:BasedComplex Q (K:=K) I) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V)
    (i:TestIndex Q E.placement α) (hi:((E.testComplex Q α).placement i).level=d) :
    Path.length i.2.val=0 ∧ (E.placement i.1).level=d := by
  have hh:=hfloor i.1
  have hl:0≤Path.length i.2.val := by
    rcases i.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
  omega

theorem bottom_test_cycle_zero_of_socle
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α:V) (c:ℤ)
    (hS:coefficientSocle Q (E.pureLayer Q hE d) α c=⊥)
    (y:TestIndex Q E.placement α→K)
    (hs:∀ i,¬ (((E.testComplex Q α).placement i).level=d ∧
      ((E.testComplex Q α).placement i).cochain=c)→y i=0)
    (hd:Matrix.vecMul y ((E.testComplex Q α).differential.map (vertexHom Q α))=0) : y=0 := by
  have hy: y∈socleTestCycles Q E α c := by
    constructor
    · intro i hi
      apply hs
      rintro ⟨hl,hc⟩
      exact hi ⟨hc,(test_bottom_length_zero Q E hfloor α i hl).1⟩
    · rwa [testComplex_vertex_differential Q E α] at hd
  let x:=sumUnitTest Q E.placement α y
  have hx:x∈coefficientSocle Q E α c:=sumUnitTest_socle Q E α c hy
  have hxs:∀ i,(E.placement i).level≠d→x i=0 := by
    intro i hi
    apply Finset.sum_eq_zero
    intro z hz
    apply hs
    intro hh
    exact hi (test_bottom_length_zero Q E hfloor α ⟨i,z⟩ hh.1).2
  have hxr:=coefficientSocle_restrict_layer Q E hE d α c hx hxs
  rw [hS] at hxr
  have hzr:(fun i:{i // (E.placement i).level=d}=>x i.val)=0:=hxr
  have hx0:x=0 := by
    funext i
    by_cases hi:(E.placement i).level=d
    · exact congrFun hzr ⟨i,hi⟩
    · exact hxs i hi
  rw [← unitTestVector_sum Q E.placement α c y hy.1]
  change unitTestVector Q E.placement α x=0
  rw [hx0,map_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
