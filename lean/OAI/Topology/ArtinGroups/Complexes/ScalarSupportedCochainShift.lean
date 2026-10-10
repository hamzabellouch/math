import Mathlib
import OAI.Topology.ArtinGroups.Complexes.TestComplexVertexDifferential
import OAI.Topology.ArtinGroups.Complexes.ScalarSupported
import OAI.Topology.ArtinGroups.Complexes.ArrowShift

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarSupported_cochainShift (E F:BasedComplex Q (K:=K) I)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (l c:ℤ) (x:I→K) : ScalarSupported Q F l c x ↔ ScalarSupported Q E l (c+1) x := by
  constructor <;> intro h i hi <;> apply h i <;> intro hh <;> apply hi
  · rw [hl,hc] at hh
    exact ⟨hh.1,by omega⟩
  · rw [hl,hc]
    exact ⟨hh.1,by omega⟩

omit [Fintype V] [DecidableEq A] [DecidableEq I] in
lemma scalarExact_cochainShift_iff (E F:BasedComplex Q (K:=K) I) (α β:V)
    (hl:∀ i,(F.placement i).level=(E.placement i).level)
    (hc:∀ i,(F.placement i).cochain=(E.placement i).cochain-1)
    (hd:F.differential.map (vertexHom Q β) = -E.differential.map (vertexHom Q α))
    (l c:ℤ) : ScalarExactAt Q F β l c ↔ ScalarExactAt Q E α l (c+1) := by
  constructor
  · intro h x hx hd0
    have hxs:ScalarSupported Q F l c x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mpr hx
    have hdx:Matrix.vecMul x (F.differential.map (vertexHom Q β))=0 := by
      rw [hd,Matrix.vecMul_neg,hd0,neg_zero]
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · have hh:ScalarSupported Q E (l-1) (c-1+1) y :=
        (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) y).mp hy
      intro i hi
      change -y i=0
      rw [hh i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg] at hyb
      simpa only [Matrix.neg_vecMul] using hyb
  · intro h x hx hd0
    have hxs:ScalarSupported Q E l (c+1) x :=
      (scalarSupported_cochainShift Q E F hl hc l c x).mp hx
    have hdx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0 := by
      rw [hd,Matrix.vecMul_neg] at hd0
      exact neg_eq_zero.mp hd0
    obtain ⟨y,hy,hyb⟩:=h x hxs hdx
    refine ⟨-y,?_,?_⟩
    · apply (scalarSupported_cochainShift Q E F hl hc (l-1) (c-1) (-y)).mpr
      intro i hi
      change -y i=0
      rw [hy i,neg_zero]
      simpa only [sub_add_cancel,add_sub_cancel_right] using hi
    · rw [hd,Matrix.vecMul_neg,Matrix.neg_vecMul,neg_neg,hyb]

theorem positiveTwist_adjacent_test_exact_iff (hn:∀ a,Q.source a≠Q.target a)
    (E:BasedComplex Q (K:=K) I) {α β:V} (e:SimpleEdge Q α β) (l c:ℤ) :
    ScalarExactAt Q (((E.positiveTwist Q β).positiveTwist Q α).testComplex Q β) β l c ↔
      ScalarExactAt Q (E.testComplex Q α) α l (c+1) := by
  let F:=(adjacentTestSecondPivot Q hn E e).reduced Q
  have hl:∀ i,(F.placement i).level=((E.testComplex Q α).placement i).level := by
    intro i
    change (E.placement i.1).cochain-1+
      ((E.placement i.1).internal+Path.length i.2.val+1)=
      (E.placement i.1).cochain+((E.placement i.1).internal+Path.length i.2.val)
    omega
  have hc:∀ i,(F.placement i).cochain=((E.testComplex Q α).placement i).cochain-1:=fun _=>rfl
  have hd:F.differential.map (vertexHom Q β)=
      -(E.testComplex Q α).differential.map (vertexHom Q α) := by
    rw [testComplex_vertex_differential]
    apply Matrix.ext
    intro i j
    change (vertexHom Q β) (F.differential i j)= -testMatrix Q E.placement E.placement α E.differential i j
    rw [adjacentTest_second_reduced_differential]
    rw [map_neg]
    congr 1
    change (testMatrix Q E.placement E.placement α E.differential i j • vertexId Q (K:=K) β).vertex β=_
    simp
  rw [← scalarExact_cochainShift_iff Q (E.testComplex Q α) F α β hl hc hd l c]
  have h:=adjacentTestReduction Q hn E e
  constructor
  · exact fun h0=>scalarExact_transport Q _ _ (h.symm Q) β (fun _=>rfl) h0
  · exact fun h0=>scalarExact_transport Q _ _ h β (fun _=>rfl) h0

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
