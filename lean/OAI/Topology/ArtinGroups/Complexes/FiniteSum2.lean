import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Complexes.FiniteSum

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]
  {T R : I → Type*} [∀ i, Fintype (T i)] [∀ i, Fintype (R i)]
  [∀ i, DecidableEq (T i)] [∀ i, DecidableEq (R i)]

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_entries (E : (i:I) → BasedComplex Q (K := K) (T i))
    (M : (i:I) → Matrix (T i) (T i) (Zigzag Q K))
    (hM : ∀ i, ProjectiveEntries Q (E i).placement (E i).placement (M i)) :
    ProjectiveEntries Q (finiteSum Q E).placement (finiteSum Q E).placement
      (Matrix.blockDiagonal' M) := by
  constructor
  all_goals
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases h : i=j
    · subst j
      rw [Matrix.blockDiagonal'_apply_eq]
      first | exact (hM i).1 x y | exact (hM i).2 x y
    · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
      first | exact MulZeroClass.mul_zero _ | exact MulZeroClass.zero_mul _

omit [Fintype V] [DecidableEq A] [∀ i, DecidableEq (T i)] in
lemma finiteSum_degree (E : (i:I) → BasedComplex Q (K := K) (T i))
    (M : (i:I) → Matrix (T i) (T i) (Zigzag Q K)) {n v : ℤ}
    (hM : ∀ i, MapDegree Q (E i).placement (E i).placement n v (M i)) :
    MapDegree Q (finiteSum Q E).placement (finiteSum Q E).placement n v
      (Matrix.blockDiagonal' M) := by
  rintro ⟨i,x⟩ ⟨j,y⟩
  by_cases h : i=j
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    exact hM i x y
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ h]
    exact ⟨fun _ => rfl,homogeneous_zero Q _⟩

noncomputable def HomotopyEquivalence.finiteSum
    {E : (i:I) → BasedComplex Q (K := K) (T i)}
    {F : (i:I) → BasedComplex Q (K := K) (R i)}
    (f : (i:I) → HomotopyEquivalence Q (E i) (F i)) :
    HomotopyEquivalence Q (finiteSum Q E) (finiteSum Q F) where
  forward := Map.finiteSum Q (fun i => (f i).forward)
  backward := Map.finiteSum Q (fun i => (f i).backward)
  sourceHomotopy := Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy)
  targetHomotopy := Matrix.blockDiagonal' (fun i => (f i).targetHomotopy)
  sourceEntries := finiteSum_entries Q E _ (fun i => (f i).sourceEntries)
  targetEntries := finiteSum_entries Q F _ (fun i => (f i).targetEntries)
  sourceDegree := finiteSum_degree Q E _ (fun i => (f i).sourceDegree)
  targetDegree := finiteSum_degree Q F _ (fun i => (f i).targetDegree)
  sourceEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).forward.matrix) * Matrix.blockDiagonal' (fun i => (f i).backward.matrix) = _
    rw [← finiteSum_identity Q E]
    change _ = Matrix.blockDiagonal' (fun i => projectiveIdentity Q (E i).placement) +
      (Matrix.blockDiagonal' (fun i => (E i).differential) * Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy) +
       Matrix.blockDiagonal' (fun i => (f i).sourceHomotopy) * Matrix.blockDiagonal' (fun i => (E i).differential))
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_add,← Matrix.blockDiagonal'_add]
    congr 1
    funext i
    exact (f i).sourceEquation
  targetEquation := by
    change Matrix.blockDiagonal' (fun i => (f i).backward.matrix) * Matrix.blockDiagonal' (fun i => (f i).forward.matrix) = _
    rw [← finiteSum_identity Q F]
    change _ = Matrix.blockDiagonal' (fun i => projectiveIdentity Q (F i).placement) +
      (Matrix.blockDiagonal' (fun i => (F i).differential) * Matrix.blockDiagonal' (fun i => (f i).targetHomotopy) +
       Matrix.blockDiagonal' (fun i => (f i).targetHomotopy) * Matrix.blockDiagonal' (fun i => (F i).differential))
    rw [← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,← Matrix.blockDiagonal'_mul,
      ← Matrix.blockDiagonal'_add,← Matrix.blockDiagonal'_add]
    congr 1
    funext i
    exact (f i).targetEquation

def sumTwistEquiv (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    (Σ i, TestIndex Q (E i).placement α ⊕ T i) ≃
      (TestIndex Q (finiteSum Q E).placement α ⊕ Sigma T) where
  toFun
    | ⟨i,.inl ⟨x,p⟩⟩ => .inl ⟨⟨i,x⟩,p⟩
    | ⟨i,.inr x⟩ => .inr ⟨i,x⟩
  invFun
    | .inl ⟨⟨i,x⟩,p⟩ => ⟨i,.inl ⟨x,p⟩⟩
    | .inr ⟨i,x⟩ => ⟨i,.inr x⟩
  left_inv z := by rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  right_inv z := by rcases z with ⟨⟨i,x⟩,p⟩|⟨i,x⟩ <;> rfl

lemma sumTwist_eq (E : (i:I) → BasedComplex Q (K := K) (T i)) (α:V) :
    ((finiteSum Q E).positiveTwist Q α).reindex Q (sumTwistEquiv Q E α) =
      finiteSum Q (fun i => (E i).positiveTwist Q α) := by
  classical
  apply ext_placement_differential Q
  · funext z
    rcases z with ⟨i,⟨x,p⟩|x⟩ <;> rfl
  · apply Matrix.ext
    rintro ⟨i,x⟩ ⟨j,y⟩
    by_cases hij : i=j
    · subst j
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_eq,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,Sigma.mk.inj_iff,heq_eq_eq,true_and]
    · have hs (x:T i) (y:T j) : (⟨i,x⟩ : Sigma T) ≠ ⟨j,y⟩ := fun h => hij (congrArg Sigma.fst h)
      rcases x with ⟨x,p⟩|x <;> rcases y with ⟨y,q⟩|y
      all_goals dsimp only [reindex,Matrix.submatrix_apply,sumTwistEquiv,Equiv.coe_fn_mk]
      all_goals simp only [finiteSum,positiveTwist_differential,Matrix.blockDiagonal'_apply_ne _ _ _ hij,
        Matrix.fromBlocks,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,testTransform,scalarCornerMatrix,testMatrix,
        evaluationMatrix,Matrix.neg_apply,Matrix.zero_apply,ite_eq_right (hs _ _),MulZeroClass.mul_zero,
        coordinates_zero,zero_smul,neg_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
