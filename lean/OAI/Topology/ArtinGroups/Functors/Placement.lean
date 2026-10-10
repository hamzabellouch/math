import Mathlib
import OAI.Topology.ArtinGroups.Quivers.Reduction
import OAI.Topology.ArtinGroups.Quivers.Iso

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Iso
open Zigzag Zigzag.BasedComplex

variable {V A W B K : Type*} {Q : ReversibleQuiver V A} {R : ReversibleQuiver W B}
  (e : Iso Q R) [Field K] [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq W]
  {I J L : Type*}

def placement (p : GeneratorPlacement V) : GeneratorPlacement W :=
  ⟨e.vertex p.color,p.cochain,p.internal⟩

noncomputable def matrix (M : Matrix I J (Q.Zigzag K)) : Matrix I J (R.Zigzag K) :=
  M.map e.zigzag

@[simp] lemma matrix_apply (M : Matrix I J (Q.Zigzag K)) (i:I) (j:J) :
    e.matrix M i j = e.zigzagLinear (M i j) := rfl

@[simp] lemma matrix_zero : e.matrix (0 : Matrix I J (Q.Zigzag K)) = 0 := by
  apply Matrix.ext; intro i j; exact map_zero (e.zigzag (K := K))
@[simp] lemma matrix_add (M N : Matrix I J (Q.Zigzag K)) :
    e.matrix (M+N) = e.matrix M + e.matrix N := by
  apply Matrix.ext; intro i j; exact map_add (e.zigzag (K := K)) _ _
@[simp] lemma matrix_mul [Fintype J] (M : Matrix I J (Q.Zigzag K)) (N : Matrix J L (Q.Zigzag K)) :
    e.matrix (M*N) = e.matrix M * e.matrix N := by
  exact Matrix.map_mul (f := (e.zigzag (K := K)).toRingHom)

lemma matrix_entries {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} (h : ProjectiveEntries Q p q M) :
    ProjectiveEntries R (e.placement ∘ p) (e.placement ∘ q) (e.matrix M) := by
  constructor
  · intro i j
    change vertexId R (e.vertex (p i).color) * e.zigzagLinear (M i j) = _
    rw [← e.zigzag_vertexId,← e.zigzagLinear_mul,h.1]
    rfl
  · intro i j
    change e.zigzagLinear (M i j) * vertexId R (e.vertex (q j).color) = _
    rw [← e.zigzag_vertexId,← e.zigzagLinear_mul,h.2]
    rfl

lemma matrix_degree {p:I → GeneratorPlacement V} {q:J → GeneratorPlacement V}
    {M : Matrix I J (Q.Zigzag K)} {n v:ℤ} (h : MapDegree Q p q n v M) :
    MapDegree R (e.placement ∘ p) (e.placement ∘ q) n v (e.matrix M) := by
  intro i j
  refine ⟨?_,e.zigzag_homogeneous (h i j).2⟩
  intro hn
  change e.zigzag (M i j) = 0
  rw [(h i j).1 hn,map_zero]

@[simp] lemma matrix_identity [DecidableEq I] (p : I → GeneratorPlacement V) :
    e.matrix (projectiveIdentity Q (K := K) p) = projectiveIdentity R (e.placement ∘ p) := by
  apply Matrix.ext
  intro i j
  by_cases h:i=j
  · subst j
    simp only [matrix,Matrix.map_apply,projectiveIdentity,Matrix.diagonal_apply_eq]
    change e.zigzagLinear (vertexId Q (p i).color) = vertexId R (e.vertex (p i).color)
    exact e.zigzag_vertexId (K := K) (p i).color
  · simp [matrix,projectiveIdentity,h]

noncomputable def complex [Fintype I] (E : BasedComplex Q (K := K) I) : BasedComplex R (K := K) I where
  placement := e.placement ∘ E.placement
  differential := e.matrix E.differential
  entries := e.matrix_entries E.entries
  degree := e.matrix_degree E.degree
  square_zero := by rw [← matrix_mul,E.square_zero,matrix_zero]

lemma complex_minimal [Fintype I] {E : BasedComplex Q (K := K) I} (h:E.IsMinimal Q) :
    (e.complex E).IsMinimal R := by
  intro i j
  ext v
  change (E.differential i j).vertex (e.vertex.symm v)=0
  rw [h i j]; rfl

noncomputable def chainMap [Fintype I] [Fintype J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : Map Q E F) :
    Map R (e.complex E) (e.complex F) where
  matrix := e.matrix f.matrix
  entries := e.matrix_entries f.entries
  degree := e.matrix_degree f.degree
  commute := by
    change e.matrix E.differential * e.matrix f.matrix = e.matrix f.matrix * e.matrix F.differential
    rw [← matrix_mul,← matrix_mul,f.commute]

noncomputable def homotopyEquivalence [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {E : BasedComplex Q (K := K) I} {F : BasedComplex Q (K := K) J} (f : HomotopyEquivalence Q E F) :
    HomotopyEquivalence R (e.complex E) (e.complex F) where
  forward := e.chainMap f.forward
  backward := e.chainMap f.backward
  sourceHomotopy := e.matrix f.sourceHomotopy
  targetHomotopy := e.matrix f.targetHomotopy
  sourceEntries := e.matrix_entries f.sourceEntries
  targetEntries := e.matrix_entries f.targetEntries
  sourceDegree := e.matrix_degree f.sourceDegree
  targetDegree := e.matrix_degree f.targetDegree
  sourceEquation := by
    change e.matrix f.forward.matrix * e.matrix f.backward.matrix = _
    rw [← matrix_mul,f.sourceEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl
  targetEquation := by
    change e.matrix f.backward.matrix * e.matrix f.forward.matrix = _
    rw [← matrix_mul,f.targetEquation,matrix_add,matrix_add,matrix_mul,matrix_mul,matrix_identity]
    rfl

end HarmonicArtin.ReversibleQuiver.Iso

end OAI
