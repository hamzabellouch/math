import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.InverseTwistPlacement
import OAI.Topology.ArtinGroups.Diagrams.Index

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

lemma inverseTwistProjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistDifferential Q E α * inverseTwistProjection Q E α =
      inverseTwistProjection Q E α * E.differential := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistDifferential,
    inverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, Finset.sum_neg_distrib, add_zero, zero_add]
  · exact (congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (evaluation_entries Q E.placement α)) u) j)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (evaluation_entries Q E.placement α)) u) j)).trans (neg_add_cancel _)
  · exact congrFun (congrFun (evaluation_natural Q α E.entries) u) j
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j

lemma inverseTwistInjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    E.differential * inverseTwistInjection Q E α =
      inverseTwistInjection Q E α * inverseTwistDifferential Q E α := by
  apply Matrix.ext
  intro i j
  rcases j with u | u | u | j | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistDifferential,
    inverseTwistInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, Finset.sum_neg_distrib,
    add_zero, zero_add, neg_zero]
  · exact congrArg Neg.neg (congrFun (congrFun (coevaluation_natural Q α E.entries).symm i) u)
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j
  · exact ((congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (coevaluation_entries Q E.placement α)) i) u)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (coevaluation_entries Q E.placement α)) i) u)).trans (neg_add_cancel _)).symm

omit [DecidableEq A] in
lemma inverseTwist_targetEquation (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistInjection Q E α * inverseTwistProjection Q E α =
      projectiveIdentity Q (K := K) E.placement := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, inverseTwistInjection,
    inverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact congrFun (congrFun (projectiveIdentity_mul Q
    (projectiveEntries_identity Q (K := K) (p := E.placement))) i) j

noncomputable def inverseTwistIdentity (E : BasedComplex Q (K := K) I) (α : V) :
    Matrix (InverseTwistIndex Q E α) (InverseTwistIndex Q E α) (Q.Zigzag K)
  | .inl u, .inl v => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inl u), .inr (.inl v) => projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inl u)), .inr (.inr (.inl v)) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | .inr (.inr (.inr (.inl i))), .inr (.inr (.inr (.inl j))) =>
      projectiveIdentity Q E.placement i j
  | .inr (.inr (.inr (.inr u))), .inr (.inr (.inr (.inr v))) =>
      projectiveIdentity Q (testPlacement Q E.placement α) u v
  | _, _ => 0

omit [Fintype V] [DecidableEq A] in
lemma inverseTwistIdentity_eq (E : BasedComplex Q (K := K) I) (α : V) :
    projectiveIdentity Q (K := K) (inverseTwistPlacement Q E α) =
      inverseTwistIdentity Q E α := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v
  all_goals simp [projectiveIdentity, Matrix.diagonal_apply,
    inverseTwistIdentity, inverseTwistPlacement, testPlacement]

omit [DecidableEq A] in
lemma unitContraction_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (testPlacement Q E.placement α) (testPlacement Q E.placement α)
      (unitContraction Q E.placement α (K := K)) := by
  constructor
  · intro u v
    dsimp only [unitContraction, testPlacement]
    split_ifs <;> simp only [mul_smul, vertexId_mul_self, MulZeroClass.mul_zero]
  · intro u v
    dsimp only [unitContraction, testPlacement]
    split_ifs <;> simp only [smul_mul, vertexId_mul_self, MulZeroClass.zero_mul]

lemma testToken_entries (E : BasedComplex Q (K := K) I) (α : V) :
    ProjectiveEntries Q (testPlacement Q E.placement α) (testPlacement Q E.placement α)
      (testToken Q E.placement α (K := K)) := by
  have hl : vertexId Q (K := K) α * tokenBasis Q α = tokenBasis Q α := by
    simpa only [Path.source, pathBasis_token] using
      (pathBasis_left Q (K := K) (.inr (.inr α)))
  have hr : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr α)))
  constructor
  · intro u v
    dsimp only [testToken, Matrix.diagonal_apply, testPlacement]
    split_ifs <;> simp only [hl, MulZeroClass.mul_zero]
  · intro u v
    dsimp only [testToken, Matrix.diagonal_apply, testPlacement]
    split_ifs <;> simp only [hr, MulZeroClass.zero_mul]

lemma inverseTwist_sourceEquation (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    inverseTwistProjection Q E α * inverseTwistInjection Q E α =
      projectiveIdentity Q (inverseTwistPlacement Q E α) +
      (inverseTwistDifferential Q E α * inverseTwistHomotopy Q E α +
       inverseTwistHomotopy Q E α * inverseTwistDifferential Q E α) := by
  rw [inverseTwistIdentity_eq]
  let t := testTransform Q E.placement E.placement α E.differential
  let r := unitContraction Q E.placement α (K := K)
  let θ := testToken Q E.placement α (K := K)
  let ι := projectiveIdentity Q (K := K) (testPlacement Q E.placement α)
  let e := evaluationMatrix Q E.placement α (K := K)
  let η := projectiveIdentity Q (K := K) E.placement
  let c := coevaluationMatrix Q E.placement α (K := K)
  have hf : inverseTwistProjection Q E α = FiveBlock.projection e η := by
    funext i j
    rcases i with u | u | u | i | u <;> rfl
  have hg : inverseTwistInjection Q E α = FiveBlock.injection c η := by
    funext i j
    rcases j with v | v | v | j | v <;> rfl
  have hh : inverseTwistHomotopy Q E α = FiveBlock.homotopy ι := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hd : inverseTwistDifferential Q E α =
      FiveBlock.differential t r θ ι e E.differential c := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hId : inverseTwistIdentity Q E α = FiveBlock.identity ι η := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  rw [hf, hg, hh, hd, hId]
  apply FiveBlock.contraction
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (E.testComplex Q α).entries
  · exact projectiveIdentity_mul Q (unitContraction_entries Q E α)
  · exact mul_projectiveIdentity Q (testToken_entries Q E α)
  · exact projectiveIdentity_mul Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (coevaluation_entries Q E.placement α)
  · exact projectiveIdentity_mul Q (coevaluation_entries Q E.placement α)
  · exact evaluation_coevaluation Q hn E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
