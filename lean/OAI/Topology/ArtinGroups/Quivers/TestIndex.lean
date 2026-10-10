import Mathlib
import OAI.Topology.ArtinGroups.Quivers.CornerPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag

variable {V A K I J L : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

abbrev TestIndex (p : I → HarmonicArtin.GeneratorPlacement V) (α : V) :=
  (i : I) × CornerPath Q α (p i).color

noncomputable def testMatrix (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V)
    (M : Matrix I J (Q.Zigzag K)) : Matrix (TestIndex Q p α) (TestIndex Q q α) K :=
  fun u v => pathCoordinates Q (pathBasis Q u.2.val * M u.1 v.1) v.2.val

omit [DecidableEq A] in
lemma testMatrix_zero (p : I → HarmonicArtin.GeneratorPlacement V)
    (q : J → HarmonicArtin.GeneratorPlacement V) (α : V) :
    testMatrix Q p q α (0 : Matrix I J (Q.Zigzag K)) = 0 := by
  apply Matrix.ext
  intro u v
  exact (congrArg (fun x => pathCoordinates Q x v.2.val)
    (MulZeroClass.mul_zero (pathBasis Q u.2.val))).trans (coordinates_zero Q v.2.val)

lemma testMatrix_mul [Fintype J]
    {p : I → HarmonicArtin.GeneratorPlacement V}
    {q : J → HarmonicArtin.GeneratorPlacement V}
    {r : L → HarmonicArtin.GeneratorPlacement V} (α : V)
    {M : Matrix I J (Q.Zigzag K)} (N : Matrix J L (Q.Zigzag K))
    (hM : ProjectiveEntries Q p q M) :
    testMatrix Q p q α M * testMatrix Q q r α N = testMatrix Q p r α (M * N) := by
  apply Matrix.ext
  intro u v
  simp only [Matrix.mul_apply, Fintype.sum_sigma, testMatrix]
  rw [Finset.mul_sum, coordinates_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hl : vertexId Q α * (pathBasis Q u.2.val * M u.1 j) =
      pathBasis Q u.2.val * M u.1 j := by
    rw [← _root_.mul_assoc, cornerPath_left Q u.2]
  have hr : (pathBasis Q u.2.val * M u.1 j) * vertexId Q (q j).color =
      pathBasis Q u.2.val * M u.1 j := by
    rw [_root_.mul_assoc, hM.2 u.1 j]
  exact (coordinates_mul_expansion Q _ (N j v.1) hl hr v.2.val).trans
    (congrArg (fun x => pathCoordinates Q x v.2.val) (_root_.mul_assoc _ _ _))

def scalarCornerMatrix (α : V) (M : Matrix I J K) : Matrix I J (Q.Zigzag K) :=
  fun i j => M i j • vertexId Q α

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_zero (α : V) :
    scalarCornerMatrix Q α (0 : Matrix I J K) = 0 := by
  apply Matrix.ext
  intro i j
  exact zero_smul _ _

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_mul [Fintype J] (α : V) (M : Matrix I J K) (N : Matrix J L K) :
    scalarCornerMatrix Q α M * scalarCornerMatrix Q α N =
      scalarCornerMatrix Q α (M * N) := by
  apply Matrix.ext
  intro i k
  simp only [Matrix.mul_apply, scalarCornerMatrix, smul_mul, mul_smul, vertexId_mul_self,
    smul_smul, Finset.sum_smul, mul_comm]

omit [Fintype V] [DecidableEq A] in
lemma scalarCornerMatrix_entries (α : V)
    (p : I → HarmonicArtin.GeneratorPlacement V) (q : J → HarmonicArtin.GeneratorPlacement V)
    (hp : ∀ i, (p i).color = α) (hq : ∀ j, (q j).color = α) (M : Matrix I J K) :
    ProjectiveEntries Q p q (scalarCornerMatrix Q α M) := by
  constructor
  · intro i j
    change vertexId Q (p i).color * (M i j • vertexId Q α) = _
    rw [hp i, mul_smul, vertexId_mul_self]
    rfl
  · intro i j
    change (M i j • vertexId Q α) * vertexId Q (q j).color = _
    rw [hq j, smul_mul, vertexId_mul_self]
    rfl

end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
