import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InverseTwistIdentity
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistDifferential
import OAI.Topology.ArtinGroups.Complexes.ReverseTwistProjection
import OAI.Topology.ArtinGroups.Diagrams.ReverseDifferential

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

lemma reverseTwistProjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistDifferential Q E α * reverseTwistProjection Q E α =
      reverseTwistProjection Q E α * E.differential := by
  apply Matrix.ext
  intro i j
  rcases i with u | u | u | i | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistDifferential,
    reverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.neg_mul, _root_.mul_neg, Finset.sum_neg_distrib, add_zero, zero_add, neg_zero]
  · exact (congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (evaluation_entries Q E.placement α)) u) j)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (evaluation_entries Q E.placement α)) u) j)).trans (neg_add_cancel _)
  · exact congrArg Neg.neg (congrFun (congrFun (evaluation_natural Q α E.entries) u) j)
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j

lemma reverseTwistInjection_commute (E : BasedComplex Q (K := K) I) (α : V) :
    E.differential * reverseTwistInjection Q E α =
      reverseTwistInjection Q E α * reverseTwistDifferential Q E α := by
  apply Matrix.ext
  intro i j
  rcases j with u | u | u | j | u
  all_goals simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistDifferential,
    reverseTwistInjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, _root_.mul_neg, Finset.sum_neg_distrib,
    add_zero, zero_add, neg_zero]
  · exact congrFun (congrFun (coevaluation_natural Q α E.entries).symm i) u
  · exact congrFun (congrFun ((mul_projectiveIdentity Q E.entries).trans
      (projectiveIdentity_mul Q E.entries).symm) i) j
  · exact ((congrArg₂ (fun a b : Q.Zigzag K => -a + b)
      (congrFun (congrFun (mul_projectiveIdentity Q
        (coevaluation_entries Q E.placement α)) i) u)
      (congrFun (congrFun (projectiveIdentity_mul Q
        (coevaluation_entries Q E.placement α)) i) u)).trans (neg_add_cancel _)).symm

omit [DecidableEq A] in
lemma reverseTwist_targetEquation (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistInjection Q E α * reverseTwistProjection Q E α =
      projectiveIdentity Q (K := K) E.placement := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.mul_apply, Fintype.sum_sum_type, reverseTwistInjection,
    reverseTwistProjection, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
    Finset.sum_const_zero, add_zero, zero_add]
  exact congrFun (congrFun (projectiveIdentity_mul Q
    (projectiveEntries_identity Q (K := K) (p := E.placement))) i) j

lemma reverseTwist_sourceEquation (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    reverseTwistProjection Q E α * reverseTwistInjection Q E α =
      projectiveIdentity Q (inverseTwistPlacement Q E α) +
      (reverseTwistDifferential Q E α * reverseTwistHomotopy Q E α +
       reverseTwistHomotopy Q E α * reverseTwistDifferential Q E α) := by
  rw [inverseTwistIdentity_eq]
  let t := testTransform Q E.placement E.placement α E.differential
  let r := unitContraction Q E.placement α (K := K)
  let θ := testToken Q E.placement α (K := K)
  let ι := projectiveIdentity Q (K := K) (testPlacement Q E.placement α)
  let e := evaluationMatrix Q E.placement α (K := K)
  let η := projectiveIdentity Q (K := K) E.placement
  let c := coevaluationMatrix Q E.placement α (K := K)
  have hf : reverseTwistProjection Q E α = FiveBlock.reverseProjection e η := by
    funext i j
    rcases i with u | u | u | i | u <;> rfl
  have hg : reverseTwistInjection Q E α = FiveBlock.reverseInjection c η := by
    funext i j
    rcases j with v | v | v | j | v <;> rfl
  have hh : reverseTwistHomotopy Q E α = FiveBlock.reverseHomotopy ι := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;>
      simp only [reverseTwistHomotopy, inverseTwistHomotopy, FiveBlock.reverseHomotopy,
        Matrix.neg_apply, neg_zero, neg_neg]
    all_goals rfl
  have hd : reverseTwistDifferential Q E α =
      FiveBlock.reverseDifferential t r θ ι e E.differential c := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  have hId : inverseTwistIdentity Q E α = FiveBlock.identity ι η := by
    funext i j
    rcases i with u | u | u | i | u <;> rcases j with v | v | v | j | v <;> rfl
  rw [hf, hg, hh, hd, hId]
  apply FiveBlock.reverseContraction
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (projectiveEntries_identity Q)
  · exact projectiveIdentity_mul Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (E.testComplex Q α).entries
  · exact mul_projectiveIdentity Q (unitContraction_entries Q E α)
  · exact projectiveIdentity_mul Q (testToken_entries Q E α)
  · exact projectiveIdentity_mul Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (evaluation_entries Q E.placement α)
  · exact mul_projectiveIdentity Q (coevaluation_entries Q E.placement α)
  · exact projectiveIdentity_mul Q (coevaluation_entries Q E.placement α)
  · exact evaluation_coevaluation Q hn E.placement α

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
