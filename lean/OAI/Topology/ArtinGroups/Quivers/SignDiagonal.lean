import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul
import OAI.Topology.ArtinGroups.Quivers.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
universe u
open Matrix

variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  {I J:Type u} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

noncomputable def signDiagonal (p:I→GeneratorPlacement V) (ε:I→Bool) : Matrix I I (Q.Zigzag K) :=
  Matrix.diagonal (fun i=>if ε i then -vertexId Q (p i).color else vertexId Q (p i).color)

omit [Fintype I] in
lemma signDiagonal_entries (p:I→GeneratorPlacement V) (ε:I→Bool) :
    ProjectiveEntries Q p p (signDiagonal Q (K:=K) p ε) := by
  constructor <;> intro i j <;> by_cases h:i=j
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [mul_neg,vertexId_mul_self]
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h,mul_zero]
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs <;> simp only [neg_mul,vertexId_mul_self]
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h,zero_mul]

omit [Fintype I] in
lemma signDiagonal_degree (p:I→GeneratorPlacement V) (ε:I→Bool) :
    MapDegree Q p p 0 0 (signDiagonal Q (K:=K) p ε) := by
  intro i j
  by_cases h:i=j
  · subst j
    simp only [signDiagonal,Matrix.diagonal_apply_eq]
    split_ifs
    · simpa only [Matrix.neg_apply,projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_neg Q (mapDegree_identity Q (K:=K) (p:=p)) i i)
    · simpa only [projectiveIdentity,Matrix.diagonal_apply_eq] using
        (mapDegree_identity Q (K:=K) (p:=p) i i)
  · simp only [signDiagonal,Matrix.diagonal_apply_ne _ h]
    constructor
    · intro; trivial
    · exact homogeneous_zero Q _

lemma signDiagonal_square (p:I→GeneratorPlacement V) (ε:I→Bool) :
    signDiagonal Q (K:=K) p ε*signDiagonal Q p ε=projectiveIdentity Q p := by
  rw [signDiagonal,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp only [neg_mul_neg,vertexId_mul_self]

omit [Fintype J] [DecidableEq J] in
lemma signDiagonal_mul {p:I→GeneratorPlacement V} {q:J→GeneratorPlacement V}
    (ε:I→Bool) (M:Matrix I J (Q.Zigzag K)) (hM:ProjectiveEntries Q p q M) (i:I) (j:J) :
    (signDiagonal Q (K:=K) p ε * M) i j=if ε i then -M i j else M i j := by
  rw [signDiagonal,Matrix.diagonal_mul]
  split_ifs <;> simp only [neg_mul,hM.1]

omit [Fintype I] [DecidableEq I] in
lemma mul_signDiagonal {p:I→GeneratorPlacement V} {q:J→GeneratorPlacement V}
    (ε:J→Bool) (M:Matrix I J (Q.Zigzag K)) (hM:ProjectiveEntries Q p q M) (i:I) (j:J) :
    (M * signDiagonal Q (K:=K) q ε) i j=if ε j then -M i j else M i j := by
  rw [signDiagonal,Matrix.mul_diagonal]
  split_ifs <;> simp only [mul_neg,hM.2]

namespace BasedComplex
noncomputable def signChainIsomorphism (E F:BasedComplex Q (K:=K) I) (ε:I→Bool)
    (hp:F.placement=E.placement)
    (hd:∀ i j,(if ε j then -E.differential i j else E.differential i j)=
      (if ε i then -F.differential i j else F.differential i j)) :
    ChainIsomorphism Q E F := by
  let s:=signDiagonal Q (K:=K) E.placement ε
  have he:ProjectiveEntries Q E.placement F.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hdeg:MapDegree Q E.placement F.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  let f:Map Q E F:=⟨s,he,hdeg,by
    apply Matrix.ext
    intro i j
    have hF:ProjectiveEntries Q E.placement F.placement F.differential := by
      rw [← hp]; exact F.entries
    exact (mul_signDiagonal Q ε E.differential E.entries i j).trans
      ((hd i j).trans (signDiagonal_mul Q ε F.differential hF i j).symm)⟩
  have hg:ProjectiveEntries Q F.placement E.placement s := by
    rw [hp]; exact signDiagonal_entries Q _ _
  have hgd:MapDegree Q F.placement E.placement 0 0 s := by
    rw [hp]; exact signDiagonal_degree Q _ _
  have hs:f.matrix*s=projectiveIdentity Q E.placement := signDiagonal_square Q _ _
  have ht:s*f.matrix=projectiveIdentity Q F.placement := by
    rw [hp]; exact signDiagonal_square Q _ _
  refine ⟨f,⟨s,hg,hgd,?_⟩,hs,ht⟩
  calc
    F.differential*s=(projectiveIdentity Q F.placement*F.differential)*s := by
      exact congrArg (fun matrix=>matrix*s) (projectiveIdentity_mul Q F.entries).symm
    _=((s*f.matrix)*F.differential)*s := by rw [ht]
    _=(s*(f.matrix*F.differential))*s := by simp only [Matrix.mul_assoc]
    _=(s*(E.differential*f.matrix))*s := by rw [f.commute]
    _=(s*E.differential)*(f.matrix*s) := by simp only [Matrix.mul_assoc]
    _=(s*E.differential)*projectiveIdentity Q E.placement := by rw [hs]
    _=s*E.differential := mul_projectiveIdentity Q (projectiveEntries_mul Q hg E.entries)

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
