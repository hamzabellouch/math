import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential2
import OAI.Topology.ArtinGroups.Coxeter.BraidFirstPivot
import OAI.Topology.ArtinGroups.Quivers.EdgeContraction
import OAI.Topology.ArtinGroups.Coxeter.BraidCoreFirstTarget

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable instance braidCoreDecidable (E : BasedComplex Q (K := K) I) (α β : V) :
    DecidableEq (BraidCoreIndex Q E α β) := Classical.decEq _

noncomputable instance braidFirstReducedDecidable (E : BasedComplex Q (K := K) I) (α β : V) :
    DecidableEq (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕
      BraidCoreIndex Q E α β) := fun a b => instDecidableEqSum a b

noncomputable def braidSecondPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BlockPivot Q ((braidFirstPivot Q hn E e).reduced Q) where
  coefficient := -1
  nonzero := neg_ne_zero.mpr one_ne_zero
  color _ := rfl
  cochain u := by
    change (E.placement u.1).cochain - 1 - 1 =
      (E.placement u.1).cochain - 1 - 1 - 1 + 1
    omega
  internal u := by
    change (E.placement u.1).internal + Path.length u.2.val + 2 =
      (E.placement u.1).internal + Path.length u.2.val + 1 + 1
    omega
  entry u v := by
    rw [BlockPivot.reduced_differential]
    simp only [braidSecondSource_to_secondTarget, braidSecondSource_to_firstTarget,
      smul_zero, MulZeroClass.zero_mul, Finset.sum_const_zero, sub_zero, neg_one_smul]
    rfl

lemma braidFirstReduction_core (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i j : BraidCoreIndex Q E α β) :
    ((braidFirstPivot Q hn E e).reduced Q).differential
      (.inr (.inr i)) (.inr (.inr j)) = braidCoreDifferential Q E e i j := by
  rw [BlockPivot.reduced_differential, normalizedBraidTwist_core]
  simp only [braidFirstPivot, inv_one, one_smul, braidCore_to_firstTarget,
    braidFirstSource_to_core]
  rcases i with u | u | u | u | i <;> rcases j with v | v | v | v | j
  all_goals simp only [braidRawCoreDifferential, braidCoreDifferential,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, Finset.sum_const_zero, sub_zero]
  simp only [ite_mul, MulZeroClass.zero_mul,
    projectiveIdentity, Matrix.diagonal_apply, testPlacement, _root_.mul_neg,
    mul_ite, MulZeroClass.mul_zero, zero_sub]
  rw [simpleEdge_arrow_right Q (e.reverse Q)]
  simp

omit [DecidableEq I] in
lemma braidFirstReduction_core_to_secondTarget (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β)
    (i : BraidCoreIndex Q E α β) (v : TestIndex Q E.placement α) :
    ((braidFirstPivot Q hn E e).reduced Q).differential
      (.inr (.inr i)) (.inr (.inl v)) = 0 := by
  rw [BlockPivot.reduced_differential, braidCore_to_secondTarget]
  simp only [braidFirstSource_to_secondTarget, MulZeroClass.mul_zero,
    Finset.sum_const_zero, sub_zero]

noncomputable def reducedBraidTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    BasedComplex Q (K := K) (BraidCoreIndex Q E α β) :=
  (braidSecondPivot Q hn E e).reduced Q

lemma reducedBraidTwist_differential (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) {α β : V} (e : SimpleEdge Q α β) :
    (reducedBraidTwist Q hn E e).differential = braidCoreDifferential Q E e := by
  apply Matrix.ext
  intro i j
  change ((braidSecondPivot Q hn E e).reduced Q).differential i j = _
  rw [BlockPivot.reduced_differential, braidFirstReduction_core]
  simp only [braidFirstReduction_core_to_secondTarget, smul_zero,
    MulZeroClass.zero_mul, Finset.sum_const_zero, sub_zero]

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
