import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerScalar
import OAI.Topology.ArtinGroups.Quivers.SmulMul
import OAI.Topology.ArtinGroups.Cancellation.CornerRemainder

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma homogeneous_smul {a : ℤ} {x : Q.Zigzag K} (hx : Homogeneous Q a x) (r : K) :
    Homogeneous Q a (r • x) := by
  exact ⟨fun h => by simp [hx.1 h], fun h => by simp [hx.2.1 h],
    fun h => by simp [hx.2.2 h]⟩

variable {I J : Type*} [DecidableEq I] [DecidableEq J]

lemma projectiveEntries_single (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (i : I) (j : J) (x : Q.Zigzag K)
    (hl : vertexId Q (p i).color * x = x)
    (hr : x * vertexId Q (q j).color = x) :
    ProjectiveEntries Q p q (Matrix.single i j x) := by
  constructor <;> intro k l <;> by_cases hk : i = k <;> by_cases hl' : j = l
  all_goals subst_vars
  all_goals simp_all [Matrix.single]

lemma mapDegree_single (p : I → GeneratorPlacement V)
    (q : J → GeneratorPlacement V) (i : I) (j : J) (x : Q.Zigzag K)
    (n v : ℤ) (hc : (q j).cochain = (p i).cochain + n)
    (hx : Homogeneous Q (v + (p i).internal - (q j).internal) x) :
    MapDegree Q p q n v (Matrix.single i j x) := by
  intro k l
  by_cases hk : k = i
  · subst k
    by_cases hl : l = j
    · subst l
      simp only [Matrix.single_apply_same]
      exact ⟨fun h => (h hc).elim, hx⟩
    · have hz : Matrix.single i j x i l = 0 := by simp [Matrix.single, Ne.symm hl]
      rw [hz]
      exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
  · have hz : Matrix.single i j x k l = 0 := by simp [Matrix.single, Ne.symm hk]
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

namespace BasedComplex

variable [Fintype I]

structure ScalarPivot (E : BasedComplex Q (K := K) I) where
  source : I
  target : I
  coefficient : K
  distinct : source ≠ target
  nonzero : coefficient ≠ 0
  color : (E.placement target).color = (E.placement source).color
  cochain : (E.placement target).cochain = (E.placement source).cochain + 1
  internal : (E.placement target).internal = (E.placement source).internal
  entry : E.differential source target = coefficient • vertexId Q (E.placement source).color

omit [DecidableEq I] in
lemma scalarPivot_of_not_minimal (E : BasedComplex Q (K := K) I) (hE : ¬E.IsMinimal Q) :
    Nonempty (ScalarPivot Q E) := by
  obtain ⟨i, j, a, hij, ha, hc, hn, hu, he⟩ := E.exists_pivot_of_not_minimal Q hE
  exact ⟨⟨i, j, a, hij, ha, hc, hn, hu, he⟩⟩

namespace ScalarPivot

variable {E : BasedComplex Q (K := K) I} (p : ScalarPivot Q E)

def inverseValue : Q.Zigzag K :=
  p.coefficient⁻¹ • vertexId Q (E.placement p.source).color

def homotopy : Matrix I I (Q.Zigzag K) :=
  Matrix.single p.target p.source (p.inverseValue Q)

omit [DecidableEq I] in
lemma inverseValue_left : vertexId Q (E.placement p.target).color * p.inverseValue Q =
    p.inverseValue Q := by
  dsimp only [inverseValue]
  rw [p.color, mul_smul_comm, vertexId_mul_self]

omit [DecidableEq I] in
lemma inverseValue_right : p.inverseValue Q * vertexId Q (E.placement p.source).color =
    p.inverseValue Q := by
  dsimp only [inverseValue]
  rw [smul_mul_assoc, vertexId_mul_self]

omit [DecidableEq I] in
lemma inverseValue_entry : p.inverseValue Q * E.differential p.source p.target =
    vertexId Q (E.placement p.target).color := by
  rw [inverseValue, p.entry, smul_mul_assoc, mul_smul_comm, vertexId_mul_self,
    smul_smul, inv_mul_cancel₀ p.nonzero, one_smul, p.color]

omit [DecidableEq I] in
lemma entry_inverseValue : E.differential p.source p.target * p.inverseValue Q =
    vertexId Q (E.placement p.source).color := by
  rw [inverseValue, p.entry, smul_mul_assoc, mul_smul_comm, vertexId_mul_self,
    smul_smul, mul_inv_cancel₀ p.nonzero, one_smul]

lemma homotopy_entries : ProjectiveEntries Q E.placement E.placement (p.homotopy Q) :=
  projectiveEntries_single Q _ _ _ _ _ (p.inverseValue_left Q) (p.inverseValue_right Q)

lemma homotopy_degree : MapDegree Q E.placement E.placement (-1) 0 (p.homotopy Q) := by
  apply mapDegree_single Q
  · have hc := p.cochain
    omega
  · have hh := homogeneous_smul Q
      (homogeneous_vertexId Q (K := K) (E.placement p.source).color) p.coefficient⁻¹
    simpa only [inverseValue, p.internal, zero_add, sub_self] using hh

lemma homotopy_square : p.homotopy Q * p.homotopy Q = 0 := by
  exact Matrix.single_mul_single_of_ne _ _ _ _ p.distinct _

lemma homotopy_retract : p.homotopy Q * E.differential * p.homotopy Q = p.homotopy Q := by
  rw [homotopy, Matrix.single_mul_mul_single, p.inverseValue_entry Q,
    p.inverseValue_left Q]

noncomputable def remainder : Matrix I I (Q.Zigzag K) :=
  GaussianCancellation.cornerRemainder (projectiveIdentity Q E.placement)
    E.differential (p.homotopy Q)

lemma remainder_entries : ProjectiveEntries Q E.placement E.placement (p.remainder Q) := by
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact projectiveEntries_add Q
    (projectiveEntries_add Q (projectiveEntries_identity Q)
      (projectiveEntries_neg Q (projectiveEntries_mul Q E.entries (p.homotopy_entries Q))))
    (projectiveEntries_neg Q (projectiveEntries_mul Q (p.homotopy_entries Q) E.entries))

lemma remainder_degree : MapDegree Q E.placement E.placement 0 0 (p.remainder Q) := by
  have h₁ := mapDegree_mul Q E.degree (p.homotopy_degree Q)
  have h₂ := mapDegree_mul Q (p.homotopy_degree Q) E.degree
  norm_num at h₁ h₂
  unfold remainder GaussianCancellation.cornerRemainder
  simp only [sub_eq_add_neg]
  exact mapDegree_add Q (mapDegree_add Q (mapDegree_identity Q) (mapDegree_neg Q h₁))
    (mapDegree_neg Q h₂)

lemma remainder_commutes : p.remainder Q * E.differential = E.differential * p.remainder Q :=
  GaussianCancellation.cornerRemainder_commutes _ _ _
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries) E.square_zero

lemma remainder_square : p.remainder Q * p.remainder Q = p.remainder Q :=
  GaussianCancellation.cornerRemainder_idempotent _ _ _
    (projectiveIdentity_mul Q (projectiveEntries_identity Q))
    (projectiveIdentity_mul Q E.entries) (mul_projectiveIdentity Q E.entries)
    (projectiveIdentity_mul Q (p.homotopy_entries Q))
    (mul_projectiveIdentity Q (p.homotopy_entries Q))
    E.square_zero (p.homotopy_square Q) (p.homotopy_retract Q)

lemma remainder_source_row (k : I) : p.remainder Q p.source k = 0 := by
  change (projectiveIdentity Q E.placement) p.source k -
      (E.differential * p.homotopy Q) p.source k -
      (p.homotopy Q * E.differential) p.source k = 0
  rw [homotopy, Matrix.single_mul_apply_of_ne _ _ _ _ _ p.distinct]
  by_cases hk : k = p.source
  · subst k
    rw [Matrix.mul_single_apply_same, p.entry_inverseValue Q]
    simp [projectiveIdentity]
  · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hk]
    simp [projectiveIdentity, Ne.symm hk]

lemma remainder_target_column (k : I) : p.remainder Q k p.target = 0 := by
  change (projectiveIdentity Q E.placement) k p.target -
      (E.differential * p.homotopy Q) k p.target -
      (p.homotopy Q * E.differential) k p.target = 0
  rw [homotopy, Matrix.mul_single_apply_of_ne _ _ _ _ _ (Ne.symm p.distinct)]
  by_cases hk : k = p.target
  · subst k
    rw [Matrix.single_mul_apply_same, p.inverseValue_entry Q]
    simp [projectiveIdentity]
  · rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ hk]
    simp [projectiveIdentity, hk]

lemma remainder_retained (k l : I) (hk : k ≠ p.target) (hl : l ≠ p.source) :
    p.remainder Q k l = (projectiveIdentity Q E.placement) k l := by
  change (projectiveIdentity Q E.placement) k l -
      (E.differential * p.homotopy Q) k l -
      (p.homotopy Q * E.differential) k l = _
  rw [homotopy, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl,
    Matrix.single_mul_apply_of_ne _ _ _ _ _ hk, sub_zero, sub_zero]

end ScalarPivot
end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
