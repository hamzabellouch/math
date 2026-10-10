import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Harmonic.Level
import OAI.Topology.ArtinGroups.Quivers.CornerScalar

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J : Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem bottom_scalar_cycle_injective
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) {l:ℤ}
    (hcolor:∀ i,(E.placement i).color=α)
    (hE:∀ i,l≤(E.placement i).level)
    (x:I→K) (hs:∀ i,(E.placement i).level≠l → x i=0)
    (hx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0)
    (hxf:Matrix.vecMul x (e.forward.matrix.map (vertexHom Q α))=0) : x=0 := by
  have hxh:Matrix.vecMul x (e.sourceHomotopy.map (vertexHom Q α))=0 := by
    funext j
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.sourceHomotopy i j).vertex α = 0
    by_cases hxi:x i=0
    · rw [hxi,MulZeroClass.zero_mul]
    by_cases hm:(e.sourceHomotopy i j).vertex α=0
    · exact mul_eq_zero.mpr (Or.inr hm)
    have hp: (E.placement i).level=l := Classical.not_not.mp (fun h=>hxi (hs i h))
    obtain ⟨_,_,hc,hu⟩:=degree_vertex_support Q e.sourceEntries e.sourceDegree i j α hm
    have hh:=hE j
    dsimp only [GeneratorPlacement.level] at hp hh
    omega
  have hid:(projectiveIdentity Q (K:=K) E.placement).map (vertexHom Q α)=1 := by
    apply Matrix.ext
    intro i j
    by_cases he:i=j
    · subst j
      simp only [Matrix.one_apply,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply]
      change (vertexId Q (K:=K) (E.placement i).color).vertex α = 1
      simp [hcolor i,vertexId_eval]
    · simp [projectiveIdentity,Matrix.map_apply,he,vertexHom]
  have he:=congrArg (fun M:Matrix I I (Q.Zigzag K)=>M.map (vertexHom Q α)) e.sourceEquation
  simp only [Matrix.map_mul,Matrix.map_add _ (map_add _),hid] at he
  have he':=congrArg (Matrix.vecMul x) he
  simp only [Matrix.vecMul_add,← Matrix.vecMul_vecMul,hxf,hx,hxh,
    Matrix.zero_vecMul,Matrix.vecMul_one,add_zero] at he'
  exact he'.symm

theorem bottom_scalar_cycle_transport
    (E:BasedComplex Q (K:=K) I) (F:BasedComplex Q (K:=K) J)
    (e:HomotopyEquivalence Q E F) (α:V) {l c:ℤ}
    (hcolor:∀ i,(E.placement i).color=α)
    (hE:∀ i,l≤(E.placement i).level)
    (hF:∀ y:J→K,
      (∀ j,¬ ((F.placement j).level=l ∧ (F.placement j).cochain=c)→y j=0)→
      Matrix.vecMul y (F.differential.map (vertexHom Q α))=0→y=0)
    (x:I→K) (hs:∀ i,¬ ((E.placement i).level=l ∧ (E.placement i).cochain=c)→x i=0)
    (hx:Matrix.vecMul x (E.differential.map (vertexHom Q α))=0) : x=0 := by
  apply bottom_scalar_cycle_injective Q E F e α hcolor hE x
    (fun i hi=>hs i (fun h=>hi h.1)) hx
  apply hF
  · intro j hj
    apply Finset.sum_eq_zero
    intro i hi
    change x i * (e.forward.matrix i j).vertex α=0
    by_cases hx0:x i=0
    · rw [hx0,MulZeroClass.zero_mul]
    by_cases hm:(e.forward.matrix i j).vertex α=0
    · rw [hm,MulZeroClass.mul_zero]
    have hp:= (reduction_support Q e.forward.entries e.forward.degree i j α hm).1
    have hi':(E.placement i).level=l ∧ (E.placement i).cochain=c :=
      Classical.not_not.mp (fun h=>hx0 (hs i h))
    exact (hj (by simpa only [← hp] using hi')).elim
  · have hc:=congrArg (fun M:Matrix I J (Q.Zigzag K)=>M.map (vertexHom Q α)) e.forward.commute
    simp only [Matrix.map_mul] at hc
    rw [Matrix.vecMul_vecMul,← hc,← Matrix.vecMul_vecMul,hx,Matrix.zero_vecMul]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
