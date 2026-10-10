import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector
import OAI.Topology.ArtinGroups.Complexes.TestComplexVertexDifferential
import OAI.Topology.ArtinGroups.Complexes.ScalarSupported

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

def generatorTokenTest (E:BasedComplex Q (K:=K) I) (i:I) :
    TestIndex Q E.placement (E.placement i).color :=
  ⟨i,Sum.inr (Sum.inr (E.placement i).color),rfl,rfl⟩

omit [DecidableEq I] in
lemma test_token_row_zero (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (α:V) (i j:TestIndex Q E.placement α) (hi:Path.length i.2.val=2) :
    testMatrix Q E.placement E.placement α E.differential i j=0 := by
  have hp:=corner_length_two Q i.2 hi
  change pathCoordinates Q (pathBasis Q i.2.val * E.differential i.1 j.1) j.2.val=0
  rw [hp,pathBasis_token,coordinates_tokenBasis_mul]
  change (E.differential i.1 j.1).vertex α *
    (pathBasis Q (Path.dual Q j.2.val)).vertex α=0
  rw [congrFun (hE i.1 j.1) α,Pi.zero_apply,MulZeroClass.zero_mul]

omit [DecidableEq I] in
theorem highest_generator_test_not_exact
    (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q) (i:I)
    (hcap:∀ j,(E.placement j).level≤(E.placement i).level)
    (hfirst:∀ j,(E.placement j).level=(E.placement i).level→
      (E.placement i).cochain≤(E.placement j).cochain) :
    ¬ ScalarExactAt Q (E.testComplex Q (E.placement i).color) (E.placement i).color
      ((E.placement i).level+2) (E.placement i).cochain := by
  classical
  let α:=(E.placement i).color
  let T:=E.testComplex Q α
  let t:TestIndex Q E.placement α:=generatorTokenTest Q E i
  let D:=testMatrix Q E.placement E.placement α E.differential
  have ht:Path.length t.2.val=2:=rfl
  have hcol:∀ u,D u t=0 := by
    intro u
    by_contra hm
    have hm':(T.differential u t).vertex α≠0 := by
      change ((D u t) • vertexId Q (K:=K) α).vertex α≠0
      simpa [vertexId_eval] using hm
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q T.entries T.degree u t α hm'
    change (E.placement i).cochain=(E.placement u.1).cochain+1 at hc
    change (E.placement i).internal+2=
      (E.placement u.1).internal+Path.length u.2.val+0 at hu
    have hh:=hcap u.1
    rcases hp:u.2.val with v|a|v
    · have hl:Path.length u.2.val=0:=by rw [hp]; rfl
      dsimp only [GeneratorPlacement.level] at hh
      omega
    · have hl:Path.length u.2.val=1:=by rw [hp]; rfl
      have he:(E.placement u.1).level=(E.placement i).level := by
        dsimp only [GeneratorPlacement.level]; omega
      have hm:=hfirst u.1 he
      omega
    · exact hm (test_token_row_zero Q E hE α u t (by rw [hp]; rfl))
  intro he
  change ScalarExactAt Q T α ((E.placement i).level+2) (E.placement i).cochain at he
  let x:TestIndex Q E.placement α→K:=Pi.single t 1
  have hxs:ScalarSupported Q T ((E.placement i).level+2) (E.placement i).cochain x := by
    intro u hu
    have hut:u≠t := by
      intro hh
      subst u
      apply hu
      constructor
      · change (E.placement i).cochain+((E.placement i).internal+2)=
          (E.placement i).cochain+(E.placement i).internal+2
        omega
      · rfl
    exact Pi.single_eq_of_ne hut _
  have hxd:Matrix.vecMul x (T.differential.map (vertexHom Q α))=0 := by
    rw [testComplex_vertex_differential Q E α]
    funext u
    change (∑ v,x v * D v u)=0
    rw [Finset.sum_eq_single t]
    · exact mul_eq_zero.mpr (Or.inr (test_token_row_zero Q E hE α t u ht))
    · intro v hv hvt
      rw [show x v=0 from Pi.single_eq_of_ne hvt _,MulZeroClass.zero_mul]
    · simp
  obtain ⟨z,hzs,hzd⟩:=he x hxs hxd
  have hh:=congrFun hzd t
  rw [testComplex_vertex_differential Q E α] at hh
  have hz:Matrix.vecMul z D t=0 := by
    apply Finset.sum_eq_zero
    intro u hu
    exact mul_eq_zero.mpr (Or.inr (hcol u))
  change Matrix.vecMul z D t=x t at hh
  rw [hz] at hh
  have hx:x t=1:=Pi.single_eq_same _ _
  rw [hx] at hh
  exact zero_ne_one hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
