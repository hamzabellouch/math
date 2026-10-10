import Mathlib
import OAI.Topology.ArtinGroups.Cancellation.ScalarPivot
import OAI.Topology.ArtinGroups.Quivers.TestIndex

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def testPlacement (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    TestIndex Q p α → HarmonicArtin.GeneratorPlacement V :=
  fun u => ⟨α, (p u.1).cochain, (p u.1).internal + Path.length u.2.val⟩

lemma testMatrix_degree {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V} (α : V)
    {n v : ℤ} {M : Matrix I J (Q.Zigzag K)} (hM : MapDegree Q p q n v M) :
    MapDegree Q (testPlacement Q p α) (testPlacement Q q α) n v
      (scalarCornerMatrix Q α (testMatrix Q p q α M)) := by
  intro a b
  constructor
  · intro hc
    change (pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val) • vertexId Q α = 0
    rw [(hM a.1 b.1).1 hc, MulZeroClass.mul_zero, coordinates_zero, zero_smul]
  · change Homogeneous Q (v + ((p a.1).internal + Path.length a.2.val) -
      ((q b.1).internal + Path.length b.2.val))
      ((pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val) • vertexId Q α)
    by_cases hz : pathCoordinates Q (pathBasis Q a.2.val * M a.1 b.1) b.2.val = 0
    · rw [hz, zero_smul]
      exact homogeneous_zero Q _
    · have he := coordinates_mul_degree Q (pathBasis_homogeneous Q a.2.val)
        (hM a.1 b.1).2 hz
      have hd : v + ((p a.1).internal + Path.length a.2.val) -
          ((q b.1).internal + Path.length b.2.val) = 0 := by omega
      rw [hd]
      exact homogeneous_smul Q (homogeneous_vertexId Q α) _

noncomputable def evaluationMatrix (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    Matrix (TestIndex Q p α) I (Q.Zigzag K) := by
  classical
  exact fun u i => if u.1 = i then pathBasis Q u.2.val else 0

lemma evaluation_entries (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    ProjectiveEntries Q (testPlacement Q p α) p (evaluationMatrix Q p α (K := K)) := by
  classical
  constructor
  · intro u i
    dsimp only [evaluationMatrix, testPlacement]
    split_ifs
    · exact cornerPath_left Q u.2
    · exact MulZeroClass.mul_zero _
  · intro u i
    dsimp only [evaluationMatrix]
    split_ifs with h
    · subst i
      exact cornerPath_right Q u.2
    · exact MulZeroClass.zero_mul _

lemma evaluation_degree (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    MapDegree Q (testPlacement Q p α) p 0 0 (evaluationMatrix Q p α (K := K)) := by
  classical
  intro u i
  by_cases hi : u.1 = i
  · subst i
    have hev : evaluationMatrix Q p α (K := K) u u.1 = pathBasis Q u.2.val := ite_eq_left rfl
    rw [hev]
    constructor
    · intro h
      exact (h (by simp [testPlacement])).elim
    · convert pathBasis_homogeneous Q (K := K) u.2.val using 1
      dsimp [testPlacement]
      omega
  · have hev : evaluationMatrix Q p α (K := K) u i = 0 := ite_eq_right hi
    rw [hev]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq A] in
lemma evaluation_mul [Fintype I]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (α : V)
    (M : Matrix I J (Q.Zigzag K)) (u : TestIndex Q p α) (j : J) :
    (evaluationMatrix Q p α (K := K) * M) u j = pathBasis Q u.2.val * M u.1 j := by
  classical
  rw [Matrix.mul_apply]
  simp only [evaluationMatrix, ite_mul, MulZeroClass.zero_mul]
  simp

lemma testMatrix_evaluation [Fintype J]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (u : TestIndex Q p α) (j : J) :
    (scalarCornerMatrix Q α (testMatrix Q p q α M) * evaluationMatrix Q q α (K := K)) u j =
      pathBasis Q u.2.val * M u.1 j := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_sigma, evaluationMatrix, scalarCornerMatrix,
    testMatrix, mul_ite, MulZeroClass.mul_zero]
  rw [Finset.sum_eq_single j]
  · simp only [smul_mul, cornerPath_left]
    apply sum_cornerPath Q
    · rw [← _root_.mul_assoc, cornerPath_left]
    · rw [_root_.mul_assoc, hM.2 u.1 j]
  · intro b _ hbj
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right hbj
  · simp

namespace BasedComplex

variable [Fintype I]

noncomputable def testComplex (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α) where
  placement := testPlacement Q E.placement α
  differential := scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α E.differential)
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := testMatrix_degree Q α E.degree
  square_zero := by
    rw [scalarCornerMatrix_mul, testMatrix_mul Q α _ E.entries, E.square_zero,
      testMatrix_zero, scalarCornerMatrix_zero]

noncomputable def evaluation (E : BasedComplex Q (K := K) I) (α : V) :
    Map Q (E.testComplex Q α) E where
  matrix := evaluationMatrix Q E.placement α
  entries := evaluation_entries Q _ α
  degree := evaluation_degree Q _ α
  commute := by
    apply Matrix.ext
    intro u i
    exact (testMatrix_evaluation Q _ _ α E.entries u i).trans
      (evaluation_mul Q _ α E.differential u i).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
