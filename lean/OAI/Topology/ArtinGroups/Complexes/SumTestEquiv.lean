import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.FiniteSum
import OAI.Topology.ArtinGroups.Complexes.Refl
import OAI.Topology.ArtinGroups.Quivers.UnitTestVector
import OAI.Topology.ArtinGroups.Quivers.TokenTestVector

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T : I → Type*} [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_minimal (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) : (finiteSum Q E).IsMinimal Q := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  change (Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨j,y⟩).vertex=0
  by_cases h : i=j
  · subst j; rw [Matrix.blockDiagonal'_apply_eq]; exact hE i x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]; rfl

def sumTestEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (α : V) :
    (Σ i, TestIndex Q (E i).placement α) ≃ TestIndex Q (finiteSum Q E).placement α where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumTest_differential (E : (i:I) → BasedComplex Q (K := K) (T i)) (α : V) :
    (testMatrix Q (finiteSum Q E).placement (finiteSum Q E).placement α (finiteSum Q E).differential).submatrix
      (sumTestEquiv Q E α) (sumTestEquiv Q E α) =
      Matrix.blockDiagonal' (fun i => testMatrix Q (E i).placement (E i).placement α (E i).differential) := by
  apply Matrix.ext
  rintro ⟨i,x,p⟩ ⟨j,y,q⟩
  by_cases h : i=j
  · subst j
    change pathCoordinates Q (pathBasis Q p.val * Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨i,y⟩) q.val = _
    rw [Matrix.blockDiagonal'_apply_eq,Matrix.blockDiagonal'_apply_eq]
    rfl
  · change pathCoordinates Q (pathBasis Q p.val * Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x⟩ ⟨j,y⟩) q.val = _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h,
      MulZeroClass.mul_zero,coordinates_zero]

noncomputable def finiteSumSocleTestEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    (α : V) (c : ℤ) :
    socleTestCycles Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → socleTestCycles Q (E i) α c) := by
  let e := ScalarCycles.reindexEquiv
    (testMatrix Q (finiteSum Q E).placement (finiteSum Q E).placement α (finiteSum Q E).differential)
    (fun x => ((finiteSum Q E).placement x.1).cochain=c ∧ Path.length x.2.val=0)
    (sumTestEquiv Q E α)
  rw [sumTest_differential] at e
  exact e.trans (ScalarCycles.blockEquiv
    (fun i => testMatrix Q (E i).placement (E i).placement α (E i).differential)
    (fun i x => ((E i).placement x.1).cochain=c ∧ Path.length x.2.val=0))

noncomputable def finiteSumTopTestEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    (α : V) (c : ℤ) :
    topTestCycles Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → topTestCycles Q (E i) α c) := by
  let e := ScalarCycles.reindexEquiv
    (testMatrix Q (finiteSum Q E).placement (finiteSum Q E).placement α (finiteSum Q E).differential).transpose
    (fun x => ((finiteSum Q E).placement x.1).cochain=c ∧ Path.length x.2.val=2)
    (sumTestEquiv Q E α)
  have ht : (Matrix.blockDiagonal' (fun i =>
      testMatrix Q (E i).placement (E i).placement α (E i).differential)).transpose =
      Matrix.blockDiagonal' (fun i => (testMatrix Q (E i).placement (E i).placement α (E i).differential).transpose) := by
    apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_eq]
    · simp only [Matrix.transpose_apply,Matrix.blockDiagonal'_apply_ne _ _ _ h,
        Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm h)]
  rw [← Matrix.transpose_submatrix,sumTest_differential,ht] at e
  exact e.trans (ScalarCycles.blockEquiv
    (fun i => (testMatrix Q (E i).placement (E i).placement α (E i).differential).transpose)
    (fun i x => ((E i).placement x.1).cochain=c ∧ Path.length x.2.val=2))

noncomputable def coefficientSocleSumEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    {l:ℤ} (hE : ∀ i x, ((E i).placement x).level=l) (α : V) (c : ℤ) :
    coefficientSocle Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → coefficientSocle Q (E i) α c) :=
  ((coefficientSocleTestEquiv Q (finiteSum Q E) (fun x => hE x.1 x.2) α c).trans
    (finiteSumSocleTestEquiv Q E α c)).trans
    (LinearEquiv.piCongrRight (fun i => (coefficientSocleTestEquiv Q (E i) (hE i) α c).symm))

noncomputable def coefficientTopSumEquiv (E : (i:I) → BasedComplex Q (K := K) (T i))
    {l:ℤ} (hE : ∀ i x, ((E i).placement x).level=l) (α : V) (c : ℤ) :
    coefficientTopDual Q (finiteSum Q E) α c ≃ₗ[K] ((i:I) → coefficientTopDual Q (E i) α c) :=
  ((coefficientTopTestEquiv Q (finiteSum Q E) (fun x => hE x.1 x.2) α c).trans
    (finiteSumTopTestEquiv Q E α c)).trans
    (LinearEquiv.piCongrRight (fun i => (coefficientTopTestEquiv Q (E i) (hE i) α c).symm))

def sumLayerEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (d : ℤ) :
    (Σ i, {x // ((E i).placement x).level=d}) ≃
      {x : Sigma T // ((finiteSum Q E).placement x).level=d} where
  toFun x := ⟨⟨x.1,x.2.val⟩,x.2.property⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma sumLayer_eq (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) (d : ℤ) :
    ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d).reindex Q (sumLayerEquiv Q E d) =
      finiteSum Q (fun i => (E i).pureLayer Q (hE i) d) := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    change Matrix.blockDiagonal' (fun i => (E i).differential) ⟨i,x.val⟩ ⟨j,y.val⟩ =
      Matrix.blockDiagonal' (fun i => ((E i).pureLayer Q (hE i) d).differential) ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j; simp only [Matrix.blockDiagonal'_apply_eq]; rfl
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,Matrix.blockDiagonal'_apply_ne _ _ _ h]

noncomputable def sumLayerComparison (E : (i:I) → BasedComplex Q (K := K) (T i))
    (hE : ∀ i, (E i).IsMinimal Q) (d : ℤ) :
    ChainIsomorphism Q ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d)
      (finiteSum Q (fun i => (E i).pureLayer Q (hE i) d)) := by
  have e := reindexChainIsomorphism Q
    ((finiteSum Q E).pureLayer Q (finiteSum_minimal Q E hE) d) (sumLayerEquiv Q E d)
  rw [sumLayer_eq] at e
  exact e

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
