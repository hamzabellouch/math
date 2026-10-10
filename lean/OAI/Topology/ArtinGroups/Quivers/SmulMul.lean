import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Level

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K : Type*} (Q : ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

theorem smul_mul (a : K) (x y : Q.Zigzag K) :
    (a • x) * y = a • (x * y) := by
  apply Zigzag.ext
  · ext v
    simp only [vertex_mul, vertex_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext e
    simp only [arrow_mul, arrow_smul, vertex_smul, leftScale, rightScale,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext v
    simp only [token_mul, token_smul, vertex_smul, arrow_smul, backtrack,
      Pi.mul_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, _root_.mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring

theorem mul_smul (a : K) (x y : Q.Zigzag K) :
    x * (a • y) = a • (x * y) := by
  apply Zigzag.ext
  · ext v
    simp only [vertex_mul, vertex_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext e
    simp only [arrow_mul, arrow_smul, vertex_smul, leftScale, rightScale,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · ext v
    simp only [token_mul, token_smul, vertex_smul, arrow_smul, backtrack,
      Pi.mul_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, _root_.mul_add]
    congr 1
    · ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> ring

instance : Algebra K (Q.Zigzag K) :=
  Algebra.ofModule (smul_mul Q) (mul_smul Q)

lemma homogeneous_zero (a : ℤ) : Homogeneous Q a (0 : Q.Zigzag K) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

lemma homogeneous_add {a : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q a y) :
    Homogeneous Q a (x + y) := by
  exact ⟨fun h => by simp [hx.1 h, hy.1 h],
    fun h => by simp [hx.2.1 h, hy.2.1 h],
    fun h => by simp [hx.2.2 h, hy.2.2 h]⟩

omit [Fintype A] [DecidableEq V] in
lemma homogeneous_neg {a : ℤ} {x : Q.Zigzag K}
    (hx : Homogeneous Q a x) : Homogeneous Q a (-x) := by
  exact ⟨fun h => by change -x.vertex = 0; simp [hx.1 h],
    fun h => by change -x.arrow = 0; simp [hx.2.1 h],
    fun h => by change -x.token = 0; simp [hx.2.2 h]⟩

lemma homogeneous_sum {T : Type*} (t : Finset T) {a : ℤ}
    {f : T → Q.Zigzag K} (h : ∀ i ∈ t, Homogeneous Q a (f i)) :
    Homogeneous Q a (∑ i ∈ t, f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using homogeneous_zero Q a
  | @insert i t hi iht =>
    rw [Finset.sum_insert hi]
    exact homogeneous_add Q (h i (Finset.mem_insert_self _ _))
      (iht fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma homogeneous_mul {a b : ℤ} {x y : Q.Zigzag K}
    (hx : Homogeneous Q a x) (hy : Homogeneous Q b y) :
    Homogeneous Q (a + b) (x * y) := by
  by_cases hx0 : x = 0
  · subst x
    rw [MulZeroClass.zero_mul]
    exact homogeneous_zero Q _
  by_cases hy0 : y = 0
  · subst y
    rw [MulZeroClass.mul_zero]
    exact homogeneous_zero Q _
  rcases homogeneous_nonzero_degree Q hx hx0 with ha | ha | ha <;>
    rcases homogeneous_nonzero_degree Q hy hy0 with hb | hb | hb <;>
    subst a <;> subst b <;>
    simp_all [Homogeneous]
  all_goals
    ext e
    simp [leftScale, rightScale]

variable {I J L : Type*} {p : I → GeneratorPlacement V}
  {q : J → GeneratorPlacement V} {r : L → GeneratorPlacement V}

lemma projectiveEntries_zero :
    ProjectiveEntries Q p q (0 : Matrix I J (Q.Zigzag K)) := by
  constructor <;> intro i j <;> simp

lemma projectiveEntries_add {M N : Matrix I J (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) (hN : ProjectiveEntries Q p q N) :
    ProjectiveEntries Q p q (M + N) := by
  constructor
  · intro i j
    change vertexId Q _ * (M i j + N i j) = _
    rw [_root_.mul_add, hM.1, hN.1]
    rfl
  · intro i j
    change (M i j + N i j) * vertexId Q _ = _
    rw [_root_.add_mul, hM.2, hN.2]
    rfl

lemma projectiveEntries_neg {M : Matrix I J (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) : ProjectiveEntries Q p q (-M) := by
  constructor
  · intro i j
    change vertexId Q _ * (-M i j) = _
    rw [mul_neg, hM.1]
    rfl
  · intro i j
    change (-M i j) * vertexId Q _ = _
    rw [neg_mul, hM.2]
    rfl

lemma projectiveEntries_mul [Fintype J]
    {M : Matrix I J (Q.Zigzag K)} {N : Matrix J L (Q.Zigzag K)}
    (hM : ProjectiveEntries Q p q M) (hN : ProjectiveEntries Q q r N) :
    ProjectiveEntries Q p r (M * N) := by
  constructor
  · intro i k
    simp only [Matrix.mul_apply, Finset.mul_sum, ← _root_.mul_assoc, hM.1]
  · intro i k
    simp only [Matrix.mul_apply, Finset.sum_mul, _root_.mul_assoc, hN.2]

lemma projectiveEntries_identity [DecidableEq I] :
    ProjectiveEntries Q p p (projectiveIdentity Q (K := K) p) := by
  constructor <;> intro i j <;> by_cases h : i = j
  all_goals simp [projectiveIdentity, h, vertexId_mul_self]

lemma projectiveIdentity_mul [Fintype I] [DecidableEq I]
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    projectiveIdentity Q p * M = M := by
  apply Matrix.ext
  intro i j
  exact (Matrix.diagonal_mul (fun i => vertexId Q (K := K) (p i).color) M i j).trans
    (hM.1 i j)

lemma mul_projectiveIdentity [Fintype J] [DecidableEq J]
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M) :
    M * projectiveIdentity Q q = M := by
  apply Matrix.ext
  intro i j
  exact (Matrix.mul_diagonal (fun j => vertexId Q (K := K) (q j).color) M i j).trans
    (hM.2 i j)

lemma mapDegree_zero (n v : ℤ) :
    MapDegree Q p q n v (0 : Matrix I J (Q.Zigzag K)) :=
  fun _ _ => ⟨fun _ => rfl, homogeneous_zero Q _⟩

lemma mapDegree_add {n v : ℤ} {M N : Matrix I J (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) (hN : MapDegree Q p q n v N) :
    MapDegree Q p q n v (M + N) := by
  intro i j
  exact ⟨fun h => by simp [(hM i j).1 h, (hN i j).1 h],
    homogeneous_add Q (hM i j).2 (hN i j).2⟩

lemma mapDegree_neg {n v : ℤ} {M : Matrix I J (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) : MapDegree Q p q n v (-M) := by
  intro i j
  exact ⟨fun h => by simp [(hM i j).1 h], homogeneous_neg Q (hM i j).2⟩

lemma mapDegree_mul [Fintype J] {n v m w : ℤ}
    {M : Matrix I J (Q.Zigzag K)} {N : Matrix J L (Q.Zigzag K)}
    (hM : MapDegree Q p q n v M) (hN : MapDegree Q q r m w N) :
    MapDegree Q p r (n + m) (v + w) (M * N) := by
  intro i k
  constructor
  · intro h
    simp only [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hc : (q j).cochain = (p i).cochain + n
    · have he : (r k).cochain ≠ (q j).cochain + m := by omega
      rw [(hN j k).1 he, MulZeroClass.mul_zero]
    · rw [(hM i j).1 hc, MulZeroClass.zero_mul]
  · rw [Matrix.mul_apply]
    apply homogeneous_sum Q
    intro j _
    convert homogeneous_mul Q (hM i j).2 (hN j k).2 using 1
    ring

omit [Fintype A] in
lemma homogeneous_vertexId (v : V) : Homogeneous Q 0 (vertexId Q (K := K) v) :=
  ⟨fun h => (h rfl).elim, fun _ => rfl, fun _ => rfl⟩

lemma mapDegree_identity [DecidableEq I] :
    MapDegree Q p p 0 0 (projectiveIdentity Q (K := K) p) := by
  intro i j
  by_cases h : i = j
  · subst j
    constructor
    · intro hn
      exact (hn (by omega)).elim
    · simpa only [projectiveIdentity, Matrix.diagonal_apply_eq, zero_add, sub_self]
        using homogeneous_vertexId Q (K := K) (p i).color
  · have hz : projectiveIdentity Q (K := K) p i j = 0 :=
      Matrix.diagonal_apply_ne _ h
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
