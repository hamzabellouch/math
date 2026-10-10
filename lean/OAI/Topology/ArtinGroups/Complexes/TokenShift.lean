import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Cancellation.ReducedDifferential2
import OAI.Topology.ArtinGroups.Complexes.Identity

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

variable {V A K I : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
  [Fintype I] [DecidableEq I]

noncomputable def tokenShift (E : BasedComplex Q (K := K) I) :
    BasedComplex Q (K := K) I where
  placement i := ⟨(E.placement i).color, (E.placement i).cochain - 1,
    (E.placement i).internal + 2⟩
  differential := -E.differential
  entries := projectiveEntries_neg Q E.entries
  degree i j := by
    constructor
    · intro h
      change -E.differential i j = 0
      rw [(E.degree i j).1 (by dsimp only at h; omega), neg_zero]
    · change Homogeneous Q (0 + ((E.placement i).internal + 2) -
        ((E.placement j).internal + 2)) (-E.differential i j)
      convert homogeneous_neg Q (E.degree i j).2 using 1; omega
  square_zero := by rw [Matrix.neg_mul, Matrix.mul_neg, neg_neg, E.square_zero]

def testShiftIndexEquiv (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (TestIndex Q E.placement α ⊕ TestIndex Q E.placement α ⊕ TestIndex Q E.placement α) ≃
      TestIndex Q (E.positiveTwist Q α).placement α where
  toFun
    | .inl u => ⟨.inl u, selfCornerEquiv Q hn α false⟩
    | .inr (.inl u) => ⟨.inr u.1, u.2⟩
    | .inr (.inr u) => ⟨.inl u, selfCornerEquiv Q hn α true⟩
  invFun
    | ⟨.inl u, p⟩ => if (selfCornerEquiv Q hn α).symm p then .inr (.inr u) else .inl u
    | ⟨.inr i, p⟩ => .inr (.inl ⟨i, p⟩)
  left_inv u := by rcases u with u | u | u <;> rfl
  right_inv u := by
    rcases u with ⟨u | i, p⟩
    · have he := (selfCornerEquiv Q hn α).apply_symm_apply p
      cases h : (selfCornerEquiv Q hn α).symm p
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α false : CornerPath Q α α) = p
        simpa only [h] using he
      · simp only [h, ↓reduceIte]
        congr 1
        change (selfCornerEquiv Q hn α true : CornerPath Q α α) = p
        simpa only [h] using he
    · rfl

noncomputable def normalizedTestTwist (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :=
  ((E.positiveTwist Q α).testComplex Q α).reindex Q (testShiftIndexEquiv Q hn E α)

lemma normalizedTestTwist_pivot_entry (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inl v)) =
      projectiveIdentity Q (testPlacement Q E.placement α) u v := by
  classical
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    evaluationMatrix Q E.placement α u v.1) v.2.val) • vertexId Q (K := K) α = _
  rw [pathBasis_vertex]
  simp only [evaluationMatrix]
  by_cases h : u.1 = v.1
  · rcases u with ⟨i, p⟩
    rcases v with ⟨j, q⟩
    dsimp only at h
    subst j
    simp only [ite_true, cornerPath_left, pathBasis_coordinates, projectiveIdentity,
      Matrix.diagonal_apply, testPlacement, Sigma.mk.inj_iff, heq_eq_eq, true_and]
    simp only [Subtype.val_inj, ite_smul, one_smul, zero_smul]
  · have huv : u ≠ v := fun he => h (congrArg Sigma.fst he)
    simp only [ite_eq_right h, MulZeroClass.mul_zero, coordinates_zero, zero_smul,
      projectiveIdentity, Matrix.diagonal_apply, ite_eq_right huv]

noncomputable def testShiftPivot (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    BlockPivot Q (normalizedTestTwist Q hn E α) where
  coefficient := 1
  nonzero := one_ne_zero
  color _ := rfl
  cochain i := by
    change (E.placement i.1).cochain = (E.placement i.1).cochain - 1 + 1
    omega
  internal i := by
    change (E.placement i.1).internal + Path.length i.2.val =
      ((E.placement i.1).internal + Path.length i.2.val) + 0
    omega
  entry i j := by
    rw [normalizedTestTwist_pivot_entry]
    simp only [one_smul]
    rfl

omit [DecidableEq I] in
lemma normalizedTestTwist_unit_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inl u) (.inr (.inr v)) = 0 := by
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inl α) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α = 0
  rw [pathBasis_vertex, _root_.mul_neg, mul_smul, vertexId_mul_self]
  rw [map_neg, Pi.neg_apply, coordinates_smul, pathCoordinates_token, token_vertexId]
  simp only [Pi.zero_apply, MulZeroClass.mul_zero, neg_zero, zero_smul]

omit [DecidableEq I] in
lemma normalizedTestTwist_token_token (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) (u v : TestIndex Q E.placement α) :
    (normalizedTestTwist Q hn E α).differential (.inr (.inr u)) (.inr (.inr v)) =
      -(E.testComplex Q α).differential u v := by
  have ht : tokenBasis Q (K := K) α * vertexId Q α = tokenBasis Q α := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr α)))
  change (pathCoordinates Q (K := K) (pathBasis Q (K := K) (.inr (.inr α)) *
    (-((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)))
      (.inr (.inr α))) • vertexId Q (K := K) α =
    -((testMatrix Q E.placement E.placement α E.differential) u v • vertexId Q (K := K) α)
  rw [pathBasis_token, _root_.mul_neg, mul_smul, ht]
  simp only [map_neg, Pi.neg_apply, coordinates_smul, ← pathBasis_token,
    pathBasis_coordinates, ite_true, _root_.mul_one, neg_smul]

lemma testShift_reduced_eq (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    (testShiftPivot Q hn E α).reduced Q = (E.testComplex Q α).tokenShift Q := by
  apply ext_placement_differential Q
  · rfl
  · apply Matrix.ext
    intro u v
    rw [BlockPivot.reduced_differential, normalizedTestTwist_token_token]
    simp only [normalizedTestTwist_unit_token, MulZeroClass.mul_zero,
      Finset.sum_const_zero, sub_zero]
    rfl

noncomputable def positiveTwist_testShift (hn : ∀ a, Q.source a ≠ Q.target a)
    (E : BasedComplex Q (K := K) I) (α : V) :
    HomotopyEquivalence Q ((E.positiveTwist Q α).testComplex Q α)
      ((E.testComplex Q α).tokenShift Q) := by
  let e := ((E.positiveTwist Q α).testComplex Q α).reindexHomotopyEquivalence Q
    (testShiftIndexEquiv Q hn E α)
  let f := (testShiftPivot Q hn E α).reductionEquivalence Q
  rw [testShift_reduced_eq] at f
  exact e.trans Q f

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
