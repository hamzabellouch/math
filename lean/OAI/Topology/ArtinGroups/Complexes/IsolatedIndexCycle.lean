import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomDetector
import OAI.Topology.ArtinGroups.Complexes.DiagonalVertex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I:Type*} (Q:ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A] [Fintype I] [DecidableEq I]

lemma isolated_index_cycle (E:BasedComplex Q (K:=K) I) (i:I)
    (hr:∀j,E.differential i j=0) (hc:∀j,E.differential j i=0) :
    Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)∈homCycles Q E E 0 0 := by
  let f:=Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)
  have h₁:E.differential*f=0 := by
    apply Matrix.ext; intro j k
    change (∑l,E.differential j l*f l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hc,zero_mul]
    · simp [f,hli]
  have h₂:f*E.differential=0 := by
    apply Matrix.ext; intro j k
    change (∑l,f j l*E.differential l k)=0
    apply Finset.sum_eq_zero
    intro l hl
    by_cases hli:i=l
    · subst l
      rw [hr,mul_zero]
    · simp [f,hli]
  refine ⟨⟨?_,?_⟩,?_⟩
  · apply projectiveEntries_single Q
    · exact vertexId_mul_self Q _
    · exact vertexId_mul_self Q _
  · apply mapDegree_single Q _ _ _ _ _ 0 0 (by omega)
    simpa only [zero_add,sub_self,Path.length,pathBasis_vertex] using pathBasis_homogeneous Q (K:=K) (Sum.inl (E.placement i).color)
  · change E.differential*f-cochainSign (K:=K) 0 • (f*E.differential)=0
    rw [h₁,h₂,smul_zero,sub_zero]

lemma eq_isolated_index (E:BasedComplex Q (K:=K) I) (hE:E.IsMinimal Q)
    (hd:homDimension Q E E 0 0≤1) (i:I)
    (hr:∀j,E.differential i j=0) (hc:∀j,E.differential j i=0) (j:I) : j=i := by
  by_contra hji
  let f:=Matrix.single i i (vertexId Q (K:=K) (E.placement i).color)
  have hf:=isolated_index_cycle Q E i hr hc
  have hb:f∈homBoundaries Q E E 0 0 := by
    apply boundary_of_homDimension_le_one Q E E 0 0 hd (diagonalVertex Q E j)
      (fun _ h=>diagonalVertex_boundary Q E hE j 0 0 h) (identity_mem_homCycles Q E)
    · rw [diagonalVertex_identity]; exact one_ne_zero
    · exact hf
    · change (f j j).vertex (E.placement j).color=0
      simp [f,Ne.symm hji]
  have hz:=diagonalVertex_boundary Q E hE i 0 0 hb
  change (f i i).vertex (E.placement i).color=0 at hz
  simp only [f,Matrix.single_apply_same,vertexId_eval] at hz
  exact one_ne_zero hz

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
