import Mathlib
import OAI.Topology.ArtinGroups.Complexes.ConeMap
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Complexes.Reindex
import OAI.Topology.ArtinGroups.Quivers.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I J L N : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]
  [Fintype I] [Fintype J] [Fintype L] [Fintype N]
  [DecidableEq I] [DecidableEq J] [DecidableEq L] [DecidableEq N]

noncomputable def ChainIsomorphism.refl (E : BasedComplex Q (K := K) I) :
    ChainIsomorphism Q E E where
  forward := Map.identity Q E
  backward := Map.identity Q E
  sourceEquation := projectiveIdentity_mul Q (projectiveEntries_identity Q)
  targetEquation := projectiveIdentity_mul Q (projectiveEntries_identity Q)

noncomputable def ChainIsomorphism.symm {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (a : ChainIsomorphism Q E F) :
    ChainIsomorphism Q F E where
  forward := a.backward
  backward := a.forward
  sourceEquation := a.targetEquation
  targetEquation := a.sourceEquation

noncomputable def ChainIsomorphism.trans {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} {G : BasedComplex Q (K := K) L}
    (a : ChainIsomorphism Q E F) (b : ChainIsomorphism Q F G) :
    ChainIsomorphism Q E G where
  forward := Map.comp Q a.forward b.forward
  backward := Map.comp Q b.backward a.backward
  sourceEquation := by
    change (a.forward.matrix*b.forward.matrix)*(b.backward.matrix*a.backward.matrix)=_
    calc
      _ = a.forward.matrix*(b.forward.matrix*b.backward.matrix)*a.backward.matrix := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [b.sourceEquation]
        exact (congrArg (fun z => z*a.backward.matrix)
          (mul_projectiveIdentity Q a.forward.entries)).trans a.sourceEquation
  targetEquation := by
    change (b.backward.matrix*a.backward.matrix)*(a.forward.matrix*b.forward.matrix)=_
    calc
      _ = b.backward.matrix*(a.backward.matrix*a.forward.matrix)*b.forward.matrix := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [a.targetEquation]
        exact (congrArg (fun z => z*b.forward.matrix)
          (mul_projectiveIdentity Q b.backward.entries)).trans b.targetEquation

noncomputable def ChainIsomorphism.toHomotopyEquivalence {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (a : ChainIsomorphism Q E F) :
    HomotopyEquivalence Q E F where
  forward := a.forward
  backward := a.backward
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by simpa only [Matrix.mul_zero,Matrix.zero_mul,add_zero] using a.sourceEquation
  targetEquation := by simpa only [Matrix.mul_zero,Matrix.zero_mul,add_zero] using a.targetEquation

noncomputable def reindexChainIsomorphism (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    ChainIsomorphism Q E (E.reindex Q e) where
  forward := E.reindexForward Q e
  backward := E.reindexBackward Q e
  sourceEquation := by
    have h := (E.reindexHomotopyEquivalence Q e).sourceEquation
    simpa only [reindexHomotopyEquivalence,Matrix.mul_zero,Matrix.zero_mul,add_zero] using h
  targetEquation := by
    have h := (E.reindexHomotopyEquivalence Q e).targetEquation
    simpa only [reindexHomotopyEquivalence,Matrix.mul_zero,Matrix.zero_mul,add_zero] using h

noncomputable def Map.reindex {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) (e : L ≃ I) (d : N ≃ J) :
    Map Q (E.reindex Q e) (F.reindex Q d) where
  matrix := f.matrix.submatrix e d
  entries := ⟨fun i j => f.entries.1 (e i) (d j), fun i j => f.entries.2 (e i) (d j)⟩
  degree := fun i j => f.degree (e i) (d j)
  commute := by
    change E.differential.submatrix e e * f.matrix.submatrix e d =
      f.matrix.submatrix e d * F.differential.submatrix d d
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv,f.commute]

lemma Map.coneIdentity {E : BasedComplex Q (K := K) I}
    {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Matrix.fromBlocks (projectiveIdentity Q (K := K) E.placement) 0 0
      (projectiveIdentity Q F.placement) = projectiveIdentity Q (f.cone Q).placement := by
  unfold projectiveIdentity
  rw [Matrix.fromBlocks_diagonal]
  congr 1
  funext i
  rcases i with i|i <;> rfl

noncomputable def ChainIsomorphism.cone
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J}
    {G : BasedComplex Q (K := K) L} {H : BasedComplex Q (K := K) N}
    (f : Map Q E F) (g : Map Q G H)
    (a : ChainIsomorphism Q E G) (b : ChainIsomorphism Q F H)
    (comm : a.forward.matrix * g.matrix = f.matrix * b.forward.matrix) :
    ChainIsomorphism Q (f.cone Q) (g.cone Q) := by
  have hc : a.backward.matrix * f.matrix = g.matrix * b.backward.matrix := by
    calc
      _ = a.backward.matrix * (f.matrix * (b.forward.matrix*b.backward.matrix)) := by
        rw [b.sourceEquation]
        exact congrArg (fun z => a.backward.matrix*z) (mul_projectiveIdentity Q f.entries).symm
      _ = a.backward.matrix * ((a.forward.matrix*g.matrix)*b.backward.matrix) := by
        rw [← Matrix.mul_assoc f.matrix,← comm]
      _ = (a.backward.matrix*a.forward.matrix)*g.matrix*b.backward.matrix := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [a.targetEquation]
        exact congrArg (fun z => z*b.backward.matrix) (projectiveIdentity_mul Q g.entries)
  exact {
    forward := f.coneMap Q g a.forward b.forward comm
    backward := g.coneMap Q f a.backward b.backward hc
    sourceEquation := by
      change Matrix.fromBlocks a.forward.matrix 0 0 b.forward.matrix *
        Matrix.fromBlocks a.backward.matrix 0 0 b.backward.matrix = _
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,a.sourceEquation,b.sourceEquation]
      exact f.coneIdentity Q
    targetEquation := by
      change Matrix.fromBlocks a.backward.matrix 0 0 b.backward.matrix *
        Matrix.fromBlocks a.forward.matrix 0 0 b.forward.matrix = _
      rw [Matrix.fromBlocks_multiply]
      simp only [Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,a.targetEquation,b.targetEquation]
      exact g.coneIdentity Q }

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
