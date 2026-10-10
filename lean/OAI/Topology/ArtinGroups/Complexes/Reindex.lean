import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Quivers.SmulMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I J : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [Fintype J]

noncomputable def reindex (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    BasedComplex Q (K := K) J where
  placement := E.placement ∘ e
  differential := E.differential.submatrix e e
  entries := ⟨fun i j => E.entries.1 (e i) (e j), fun i j => E.entries.2 (e i) (e j)⟩
  degree i j := E.degree (e i) (e j)
  square_zero := by
    rw [Matrix.submatrix_mul_equiv, E.square_zero]
    rfl

variable [DecidableEq I] [DecidableEq J]

noncomputable def reindexForward (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    Map Q E (E.reindex Q e) where
  matrix := (projectiveIdentity Q E.placement).submatrix id e
  entries := ⟨fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).1 i (e j),
    fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).2 i (e j)⟩
  degree i j := mapDegree_identity Q (p := E.placement) i (e j)
  commute := by
    change E.differential.submatrix id (Equiv.refl I) *
        (projectiveIdentity Q E.placement).submatrix (Equiv.refl I) e =
      (projectiveIdentity Q E.placement).submatrix id e * E.differential.submatrix e e
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix id e)
      ((mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm)

noncomputable def reindexBackward (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    Map Q (E.reindex Q e) E where
  matrix := (projectiveIdentity Q E.placement).submatrix e id
  entries := ⟨fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).1 (e i) j,
    fun i j => (projectiveEntries_identity Q (K := K) (p := E.placement)).2 (e i) j⟩
  degree i j := mapDegree_identity Q (p := E.placement) (e i) j
  commute := by
    change E.differential.submatrix e e * (projectiveIdentity Q E.placement).submatrix e id =
      (projectiveIdentity Q E.placement).submatrix e (Equiv.refl I) *
        E.differential.submatrix (Equiv.refl I) id
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    exact congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix e id)
      ((mul_projectiveIdentity Q E.entries).trans (projectiveIdentity_mul Q E.entries).symm)

lemma reindexIdentity (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    (projectiveIdentity Q (K := K) E.placement).submatrix e e =
      projectiveIdentity Q (E.reindex Q e).placement := by
  apply Matrix.ext
  intro i j
  change (if e i = e j then vertexId Q (E.placement (e i)).color else 0) =
    if i = j then vertexId Q (E.placement (e i)).color else 0
  simp only [e.injective.eq_iff]

noncomputable def reindexHomotopyEquivalence (E : BasedComplex Q (K := K) I) (e : J ≃ I) :
    HomotopyEquivalence Q E (E.reindex Q e) where
  forward := E.reindexForward Q e
  backward := E.reindexBackward Q e
  sourceHomotopy := 0
  targetHomotopy := 0
  sourceEntries := projectiveEntries_zero Q
  targetEntries := projectiveEntries_zero Q
  sourceDegree := mapDegree_zero Q (-1) 0
  targetDegree := mapDegree_zero Q (-1) 0
  sourceEquation := by
    change (projectiveIdentity Q E.placement).submatrix id e *
        (projectiveIdentity Q E.placement).submatrix e id = _
    rw [Matrix.submatrix_mul_equiv]
    simp only [Matrix.submatrix_id_id, Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact projectiveIdentity_mul Q (projectiveEntries_identity Q (K := K) (p := E.placement))
  targetEquation := by
    change (projectiveIdentity Q E.placement).submatrix e (Equiv.refl I) *
        (projectiveIdentity Q E.placement).submatrix (Equiv.refl I) e = _
    rw [Matrix.submatrix_mul_equiv]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
    exact (congrArg (fun M : Matrix I I (Q.Zigzag K) => M.submatrix e e)
      (projectiveIdentity_mul Q (projectiveEntries_identity Q (K := K) (p := E.placement)))).trans
        (reindexIdentity Q E e)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
