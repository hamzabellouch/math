import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TestComplexVertexDifferential
import OAI.Topology.ArtinGroups.Complexes.TwistNewTestIndex
import OAI.Topology.ArtinGroups.Complexes.BottomScalarCycleInjective
import OAI.Topology.ArtinGroups.Complexes.BottomSocleZeroTest
import OAI.Topology.ArtinGroups.Complexes.PositiveTwistLowerBound

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] in
theorem positiveTwist_other_test_cycle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α β:V) (hne:β≠α)
    (hα:coefficientSocle Q (E.pureLayer Q hE d) α (c+1)=⊥)
    (hβ:coefficientSocle Q (E.pureLayer Q hE d) β c=⊥)
    (y:TestIndex Q (E.positiveTwist Q α).placement β→K)
    (hs:∀ i,¬ ((((E.positiveTwist Q α).testComplex Q β).placement i).level=d ∧
      (((E.positiveTwist Q α).testComplex Q β).placement i).cochain=c)→y i=0)
    (hd:Matrix.vecMul y (((E.positiveTwist Q α).testComplex Q β).differential.map
      (vertexHom Q β))=0) : y=0 := by
  have hn:∀ p:Zigzag.CornerPath Q β α,∀ u:TestIndex Q E.placement α,
      y (twistNewTestIndex Q E α β p u)=0 := by
    intro p
    have hl:=corner_other_length Q hne p
    have hx:(fun u=>y (twistNewTestIndex Q E α β p u))=0 := by
      apply bottom_test_cycle_zero_of_socle Q E hE hfloor α (c+1) hα
      · intro i hi
        apply hs
        intro hh
        apply hi
        change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=d ∧
          (E.placement i.1).cochain=c+1
        change (E.placement i.1).cochain-1+
          ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=d ∧
          (E.placement i.1).cochain-1=c at hh
        omega
      · rw [testComplex_vertex_differential Q E α]
        funext v
        have hh:=congrFun hd (twistNewTestIndex Q E α β p v)
        rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
          twistTest_new_differential Q E α β y p v] at hh
        exact neg_eq_zero.mp hh
    exact fun u=>congrFun hx u
  have ho:(fun u=>y (twistOldTestIndex Q E α β u))=0 := by
    apply bottom_test_cycle_zero_of_socle Q E hE hfloor β c hβ
    · intro i hi
      exact hs _ hi
    · rw [testComplex_vertex_differential Q E β]
      funext v
      have hh:=congrFun hd (twistOldTestIndex Q E α β v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β y hn v] at hh
      exact hh
  funext i
  obtain ⟨i,p⟩:=i
  rcases i with i|i
  · exact hn p i
  · exact congrFun ho ⟨i,p⟩

theorem positiveTwist_other_bottom_socle_zero
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (F:BasedComplex Q (K:=K) J) (hF:F.IsMinimal Q) {d c:ℤ}
    (hfloor:∀ i,d≤(E.placement i).level) (α β:V) (hne:β≠α)
    (hα:coefficientSocle Q (E.pureLayer Q hE d) α (c+1)=⊥)
    (hβ:coefficientSocle Q (E.pureLayer Q hE d) β c=⊥)
    (e:HomotopyEquivalence Q (E.positiveTwist Q α) F) :
    coefficientSocle Q (F.pureLayer Q hF d) β c=⊥ := by
  have hFl:=positiveTwist_lower_bound Q E F hfloor α hF e
  apply bottomSocle_zero_of_test_cycle_zero Q F hF hFl β
  intro y hs hd
  apply bottom_scalar_cycle_transport Q (F.testComplex Q β)
    ((E.positiveTwist Q α).testComplex Q β) ((e.symm Q).test Q β) β
    (fun _=>rfl) _ (positiveTwist_other_test_cycle_zero Q E hE hfloor α β hne hα hβ) y hs hd
  intro i
  have hi:=hFl i.1
  have hl:0≤Path.length i.2.val := by
    rcases i.2.val with v|a|v <;> norm_num [Path.length]
  dsimp only [testComplex,testPlacement,GeneratorPlacement.level] at *
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
