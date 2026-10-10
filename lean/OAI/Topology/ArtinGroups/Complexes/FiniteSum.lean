import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul
import OAI.Topology.ArtinGroups.Quivers.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V] [Fintype I] [DecidableEq I]
  {T R : I → Type*} [∀ i, Fintype (T i)] [∀ i, Fintype (R i)]

noncomputable def finiteSum (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    BasedComplex Q (K := K) (Sigma T) where
  placement := fun x => (E x.1).placement x.2
  differential := Matrix.blockDiagonal' (fun i => (E i).differential)
  entries := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (E i).entries.1 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (E i).entries.2 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]
  degree := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      exact (E i).degree x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact ⟨fun _ => rfl,homogeneous_zero Q _⟩
  square_zero := by
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(E _).square_zero]
    exact Matrix.blockDiagonal'_zero

noncomputable def Map.finiteSum
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)} (f : (i:I) → Map Q (E i) (F i)) :
    Map Q (finiteSum Q E) (finiteSum Q F) where
  matrix := Matrix.blockDiagonal' (fun i => (f i).matrix)
  entries := by
    constructor
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (f i).entries.1 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,mul_zero]
    · rintro ⟨i,x⟩ ⟨j,y⟩
      by_cases h : i=j
      · subst j
        rw [Matrix.blockDiagonal'_apply_eq]
        exact (f i).entries.2 x y
      · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h,zero_mul]
  degree := by
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      exact (f i).degree x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      exact ⟨fun _ => rfl,homogeneous_zero Q _⟩
  commute := by
    change Matrix.blockDiagonal' (fun i => (E i).differential) * Matrix.blockDiagonal' (fun i => (f i).matrix) =
      Matrix.blockDiagonal' (fun i => (f i).matrix) * Matrix.blockDiagonal' (fun i => (F i).differential)
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul]
    congr 1
    funext i
    exact (f i).commute

lemma finiteSum_identity [∀ i, DecidableEq (T i)]
    (E : (i:I) → BasedComplex Q (K := K) (T i)) :
    Matrix.blockDiagonal' (fun i => projectiveIdentity Q (K := K) (E i).placement) =
      projectiveIdentity Q (finiteSum Q E).placement := by
  classical
  apply Matrix.ext
  rintro ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    simp only [projectiveIdentity,Matrix.diagonal_apply,Sigma.mk.inj_iff,heq_eq_eq,
      true_and,finiteSum]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    have he : (⟨i,x⟩ : Sigma T) ≠ ⟨j,y⟩ := fun he => h (congrArg Sigma.fst he)
    simp only [projectiveIdentity,Matrix.diagonal_apply,ite_eq_right he]

noncomputable def ChainIsomorphism.finiteSum [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)]
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)}
    (f : (i:I) → ChainIsomorphism Q (E i) (F i)) :
    ChainIsomorphism Q (finiteSum Q E) (finiteSum Q F) where
  forward := Map.finiteSum Q (fun i => (f i).forward)
  backward := Map.finiteSum Q (fun i => (f i).backward)
  sourceEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).forward.matrix) * Matrix.blockDiagonal' (fun i => (f i).backward.matrix) = _
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).sourceEquation]
    exact finiteSum_identity Q E
  targetEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).backward.matrix) * Matrix.blockDiagonal' (fun i => (f i).forward.matrix) = _
    rw [← Matrix.blockDiagonal'_mul]
    simp only [(f _).targetEquation]
    exact finiteSum_identity Q F

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
