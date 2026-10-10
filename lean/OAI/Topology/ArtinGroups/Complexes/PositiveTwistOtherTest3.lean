import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TestComplexVertexDifferential
import OAI.Topology.ArtinGroups.Complexes.TwistNewTestIndex
import OAI.Topology.ArtinGroups.Complexes.ScalarSupported

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
theorem positiveTwist_other_test_exact_reflect
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α (l-1) c)
    (hT:ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c) :
    ScalarExactAt Q (E.testComplex Q β) β l c := by
  classical
  intro x hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  let X:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>x ⟨i,p⟩
  have hXn:∀ p u,X (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hXs:ScalarSupported Q T l c X := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hs ⟨i,p⟩ hi
  have hXd:Matrix.vecMul X D=0 := by
    funext v
    obtain ⟨i,p⟩:=v
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β X p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul X (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=0
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β X hXn ⟨i,p⟩]
      have hh:=congrFun hd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  obtain ⟨z,hzs,hzd⟩:=hT X hXs hXd
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ a:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1-1) (c-1) a ∧
      Matrix.vecMul a ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>z (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    apply hα
    · intro i hi
      apply hzs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l-1 ∧
        (E.placement i.1).cochain=c
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l-1 ∧
        (E.placement i.1).cochain-1=c-1 at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hzd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β z p v,hXn p v] at hh
      exact neg_eq_zero.mp hh
  choose a has had using hx
  let B:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -a p u
    | .inr _=>0
  have hBs:ScalarSupported Q T (l-1-1) (c-1-1) B := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -a p u=0
      rw [has p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1-1 ∧
        (E.placement u.1).cochain-1=c-1-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1-1 ∧
        (E.placement u.1).cochain=c-1 at hh
      omega
    · rfl
  have hBn:∀ p u,Matrix.vecMul B D (twistNewTestIndex Q E α β p u)=
      z (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β B p u]
    change -Matrix.vecMul (-(a p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (had p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=z-Matrix.vecMul B D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change z _-Matrix.vecMul B D _=0
    rw [hBn,sub_self]
  have hrs:ScalarSupported Q T (l-1) (c-1) r := by
    apply scalarSupported_sub Q T hzs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hBs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=X := by
    change Matrix.vecMul (z-Matrix.vecMul B D) D=X
    rw [Matrix.sub_vecMul,hzd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_zero]
  refine ⟨fun u=>r (twistOldTestIndex Q E α β u),fun u hu=>hrs _ hu,?_⟩
  rw [testComplex_vertex_differential Q E β]
  funext v
  have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
  change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=x v at hh
  rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
    twistTest_old_differential Q E α β r hrn v] at hh
  exact hh

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
