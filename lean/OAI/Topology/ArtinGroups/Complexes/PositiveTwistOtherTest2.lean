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
theorem positiveTwist_other_test_exact
    (E:BasedComplex Q (K:=K) I) (α β:V) (hne:β≠α) (l c:ℤ)
    (hα:ScalarExactAt Q (E.testComplex Q α) α l (c+1))
    (hβ:ScalarExactAt Q (E.testComplex Q β) β l c) :
    ScalarExactAt Q ((E.positiveTwist Q α).testComplex Q β) β l c := by
  classical
  intro y hs hd
  let T:=(E.positiveTwist Q α).testComplex Q β
  let D:=T.differential.map (vertexHom Q β)
  have hx:∀ p:Zigzag.CornerPath Q β α,∃ z:TestIndex Q E.placement α→K,
      ScalarSupported Q (E.testComplex Q α) (l-1) c z ∧
      Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
        fun u=>y (twistNewTestIndex Q E α β p u) := by
    intro p
    have hl:=corner_other_length Q hne p
    suffices hh:∃ z:TestIndex Q E.placement α→K,
        ScalarSupported Q (E.testComplex Q α) (l-1) (c+1-1) z ∧
        Matrix.vecMul z ((E.testComplex Q α).differential.map (vertexHom Q α))=
          fun u=>y (twistNewTestIndex Q E α β p u) from by
      simpa only [add_sub_cancel_right] using hh
    apply hα
    · intro i hi
      apply hs
      intro hh
      apply hi
      change (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)=l ∧
        (E.placement i.1).cochain=c+1
      change (E.placement i.1).cochain-1+
        ((E.placement i.1).internal+Path.length i.2.val+Path.length p.val)=l ∧
        (E.placement i.1).cochain-1=c at hh
      omega
    · rw [testComplex_vertex_differential Q E α]
      funext v
      have hh:=congrFun hd (twistNewTestIndex Q E α β p v)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β y p v] at hh
      exact neg_eq_zero.mp hh
  choose z hzs hzd using hx
  let Z:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl u=> -z p u
    | .inr _=>0
  have hZs:ScalarSupported Q T (l-1) (c-1) Z := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · change -z p u=0
      rw [hzs p u,neg_zero]
      intro hh
      apply hi
      have hl:=corner_other_length Q hne p
      change (E.placement u.1).cochain-1+
        ((E.placement u.1).internal+Path.length u.2.val+Path.length p.val)=l-1 ∧
        (E.placement u.1).cochain-1=c-1
      change (E.placement u.1).cochain+
        ((E.placement u.1).internal+Path.length u.2.val)=l-1 ∧
        (E.placement u.1).cochain=c at hh
      omega
    · rfl
  have hZn:∀ p u,Matrix.vecMul Z D (twistNewTestIndex Q E α β p u)=
      y (twistNewTestIndex Q E α β p u) := by
    intro p u
    dsimp only [D,T]
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_new_differential Q E α β Z p u]
    change -Matrix.vecMul (-(z p)) (testMatrix Q E.placement E.placement α E.differential) u=_
    rw [Matrix.neg_vecMul,Pi.neg_apply,neg_neg]
    have hh:=congrFun (hzd p) u
    rwa [testComplex_vertex_differential Q E α] at hh
  let r:=y-Matrix.vecMul Z D
  have hrn:∀ p u,r (twistNewTestIndex Q E α β p u)=0 := by
    intro p u
    change y _-Matrix.vecMul Z D _=0
    rw [hZn,sub_self]
  have hrs:ScalarSupported Q T l c r := by
    apply scalarSupported_sub Q T hs
    convert scalarSupported_map Q T T β T.differential T.entries T.degree hZs using 1 <;>
      omega
  have hrd:Matrix.vecMul r D=0 := by
    change Matrix.vecMul (y-Matrix.vecMul Z D) D=0
    rw [Matrix.sub_vecMul,hd,Matrix.vecMul_vecMul,scalarDifferential_square Q T β,
      Matrix.vecMul_zero,sub_self]
  have hro:Matrix.vecMul (fun u=>r (twistOldTestIndex Q E α β u))
      ((E.testComplex Q β).differential.map (vertexHom Q β))=0 := by
    rw [testComplex_vertex_differential Q E β]
    funext v
    have hh:=congrFun hrd (twistOldTestIndex Q E α β v)
    change Matrix.vecMul r (T.differential.map (vertexHom Q β)) _=0 at hh
    rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
      twistTest_old_differential Q E α β r hrn v] at hh
    exact hh
  obtain ⟨w,hws,hwd⟩:=hβ (fun u=>r (twistOldTestIndex Q E α β u))
    (fun u hu=>hrs _ hu) hro
  let W:TestIndex Q (E.positiveTwist Q α).placement β→K :=
    fun ⟨i,p⟩=>match i with
    | .inl _=>0
    | .inr i=>w ⟨i,p⟩
  have hWn:∀ p u,W (twistNewTestIndex Q E α β p u)=0:=fun _ _=>rfl
  have hWs:ScalarSupported Q T (l-1) (c-1) W := by
    rintro ⟨i,p⟩ hi
    rcases i with u|i
    · rfl
    · exact hws ⟨i,p⟩ hi
  have hWd:Matrix.vecMul W D=r := by
    funext i
    obtain ⟨i,p⟩:=i
    rcases i with u|i
    · change Zigzag.CornerPath Q β α at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistNewTestIndex Q E α β p u)=r (twistNewTestIndex Q E α β p u)
      rw [hrn,testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_new_differential Q E α β W p u]
      change -Matrix.vecMul (0:TestIndex Q E.placement α→K) _ u=0
      rw [Matrix.zero_vecMul,Pi.zero_apply,neg_zero]
    · change Zigzag.CornerPath Q β (E.placement i).color at p
      change Matrix.vecMul W (T.differential.map (vertexHom Q β))
        (twistOldTestIndex Q E α β ⟨i,p⟩)=r (twistOldTestIndex Q E α β ⟨i,p⟩)
      rw [testComplex_vertex_differential Q (E.positiveTwist Q α) β,
        twistTest_old_differential Q E α β W hWn ⟨i,p⟩]
      have hh:=congrFun hwd ⟨i,p⟩
      rwa [testComplex_vertex_differential Q E β] at hh
  refine ⟨Z+W,?_,?_⟩
  · intro i hi
    change Z i+W i=0
    rw [hZs i hi,hWs i hi,add_zero]
  · change Matrix.vecMul (Z+W) D=y
    rw [Matrix.add_vecMul,hWd]
    change Matrix.vecMul Z D+(y-Matrix.vecMul Z D)=y
    abel

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
