import Mathlib
import OAI.Topology.ArtinGroups.Quivers.TestPlacement
import OAI.Topology.ArtinGroups.Quivers.Dual

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

def cotestPlacement (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    TestIndex Q p α → HarmonicArtin.GeneratorPlacement V :=
  fun u => ⟨α, (p u.1).cochain, (p u.1).internal + Path.length u.2.val - 2⟩

lemma cotestMatrix_degree {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V} (α : V)
    {n v : ℤ} {M : Matrix I J (Q.Zigzag K)} (hM : MapDegree Q p q n v M) :
    MapDegree Q (cotestPlacement Q p α) (cotestPlacement Q q α) n v
      (scalarCornerMatrix Q α (testMatrix Q p q α M)) := by
  intro a b
  have he := testMatrix_degree Q α hM a b
  constructor
  · exact he.1
  · convert he.2 using 1
    dsimp [cotestPlacement, testPlacement]
    ring

noncomputable def coevaluationMatrix (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    Matrix I (TestIndex Q p α) (Q.Zigzag K) := by
  classical
  exact fun i u => if i = u.1 then pathBasis Q (Path.dual Q u.2.val) else 0

lemma coevaluation_entries (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    ProjectiveEntries Q p (cotestPlacement Q p α)
      (coevaluationMatrix Q p α (K := K)) := by
  classical
  constructor
  · intro i u
    dsimp only [coevaluationMatrix]
    split_ifs with h
    · subst i
      exact cornerPath_left Q ((cornerDual Q α (p u.1).color) u.2)
    · exact MulZeroClass.mul_zero _
  · intro i u
    dsimp only [coevaluationMatrix, cotestPlacement]
    split_ifs
    · exact cornerPath_right Q ((cornerDual Q α (p u.1).color) u.2)
    · exact MulZeroClass.zero_mul _

lemma coevaluation_degree (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :
    MapDegree Q p (cotestPlacement Q p α) 0 0
      (coevaluationMatrix Q p α (K := K)) := by
  classical
  intro i u
  by_cases hi : i = u.1
  · subst i
    have hev : coevaluationMatrix Q p α (K := K) u.1 u =
        pathBasis Q (Path.dual Q u.2.val) := ite_eq_left rfl
    rw [hev]
    constructor
    · intro h
      exact (h (by simp [cotestPlacement])).elim
    · convert pathBasis_homogeneous Q (K := K) (Path.dual Q u.2.val) using 1
      dsimp [cotestPlacement]
      rw [Path.length_dual]
      omega
  · have hev : coevaluationMatrix Q p α (K := K) i u = 0 := ite_eq_right hi
    rw [hev]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

omit [DecidableEq A] in
lemma mul_coevaluation [Fintype J]
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    (M : Matrix I J (Q.Zigzag K)) (i : I) (u : TestIndex Q q α) :
    (M * coevaluationMatrix Q q α (K := K)) i u =
      M i u.1 * pathBasis Q (Path.dual Q u.2.val) := by
  classical
  rw [Matrix.mul_apply]
  simp only [coevaluationMatrix, mul_ite, MulZeroClass.mul_zero]
  simp

lemma coevaluation_testMatrix [Fintype I]
    (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    {M : Matrix I J (Q.Zigzag K)} (hM : ProjectiveEntries Q p q M)
    (i : I) (u : TestIndex Q q α) :
    (coevaluationMatrix Q p α (K := K) * scalarCornerMatrix Q α (testMatrix Q p q α M)) i u =
      M i u.1 * pathBasis Q (Path.dual Q u.2.val) := by
  classical
  simp only [Matrix.mul_apply, Fintype.sum_sigma, coevaluationMatrix, scalarCornerMatrix,
    testMatrix, ite_mul, MulZeroClass.zero_mul]
  rw [Finset.sum_eq_single i]
  · simp only [ite_true, mul_smul]
    have hright (p' : CornerPath Q α (p i).color) :
        pathBasis Q (K := K) (Path.dual Q p'.val) * vertexId Q α =
          pathBasis Q (Path.dual Q p'.val) :=
      cornerPath_right Q ((cornerDual Q α (p i).color) p')
    simp only [hright]
    exact dual_right_action Q (M i u.1) (hM.1 i u.1) u.2
  · intro b _ hbi
    apply Finset.sum_eq_zero
    intro c _
    exact ite_eq_right (Ne.symm hbi)
  · simp

namespace BasedComplex

variable [Fintype I]

noncomputable def cotestComplex (E : BasedComplex Q (K := K) I) (α : V) :
    BasedComplex Q (K := K) (TestIndex Q E.placement α) where
  placement := cotestPlacement Q E.placement α
  differential := scalarCornerMatrix Q α (testMatrix Q E.placement E.placement α E.differential)
  entries := scalarCornerMatrix_entries Q α _ _ (fun _ => rfl) (fun _ => rfl) _
  degree := cotestMatrix_degree Q α E.degree
  square_zero := by
    rw [scalarCornerMatrix_mul, testMatrix_mul Q α _ E.entries, E.square_zero,
      testMatrix_zero, scalarCornerMatrix_zero]

noncomputable def coevaluation (E : BasedComplex Q (K := K) I) (α : V) :
    Map Q E (E.cotestComplex Q α) where
  matrix := coevaluationMatrix Q E.placement α
  entries := coevaluation_entries Q _ α
  degree := coevaluation_degree Q _ α
  commute := by
    apply Matrix.ext
    intro i u
    exact (mul_coevaluation Q _ α E.differential i u).trans
      (coevaluation_testMatrix Q _ _ α E.entries i u).symm

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
