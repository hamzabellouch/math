import Mathlib
import OAI.Topology.ArtinGroups.Complexes.Identity
import OAI.Topology.ArtinGroups.Quivers.Path
import OAI.Topology.ArtinGroups.Complexes.HomSpaceMul

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V]

omit [Fintype V] in
lemma tokenBasis_mul_positive (α : V) (x : Q.Zigzag K) (hx : x.vertex = 0) :
    tokenBasis Q α * x = 0 := by
  apply ext
  · change (tokenBasis Q α * x).vertex = 0
    rw [vertex_mul]
    change (0 : V → K) * x.vertex = 0
    exact MulZeroClass.zero_mul _
  · change (tokenBasis Q α * x).arrow = 0
    rw [arrow_mul]
    change Q.leftScale 0 x.arrow + Q.rightScale 0 x.vertex = 0
    ext a
    simp [leftScale, rightScale]
  · change (tokenBasis Q α * x).token = 0
    rw [token_mul]
    change (0 : V → K) * x.token + (Pi.single α (1 : K)) * x.vertex + Q.backtrack 0 x.arrow = 0
    rw [hx]
    ext a
    simp

omit [Fintype V] in
lemma positive_mul_tokenBasis (α : V) (x : Q.Zigzag K) (hx : x.vertex = 0) :
    x * tokenBasis Q α = 0 := by
  apply ext
  · change (x * tokenBasis Q α).vertex = 0
    rw [vertex_mul]
    change x.vertex * (0 : V → K) = 0
    exact MulZeroClass.mul_zero _
  · change (x * tokenBasis Q α).arrow = 0
    rw [arrow_mul]
    change Q.leftScale x.vertex 0 + Q.rightScale x.arrow 0 = 0
    ext a
    simp [leftScale, rightScale]
  · change (x * tokenBasis Q α).token = 0
    rw [token_mul]
    change x.vertex * (Pi.single α (1 : K)) + x.token * (0 : V → K) + Q.backtrack x.arrow 0 = 0
    rw [hx]
    ext a
    simp

omit [Fintype A] in
lemma trace_tokenBasis (α : V) : trace Q (tokenBasis Q (K := K) α) = 1 := by
  change (∑ j, (Pi.single α (1 : K)) j) = 1
  simp

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

omit [Fintype V] in
lemma homBoundary_positive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hf : f ∈ homBoundaries Q E F n v) :
    PositiveMatrix Q f := by
  obtain ⟨g, _, rfl⟩ := hf
  have hl := positiveMatrix_mul_right Q hE g
  have hr := positiveMatrix_mul_left Q g hF
  intro i j
  change ((E.differential * g) i j - cochainSign (K := K) (n - 1) • (g * F.differential) i j).vertex = 0
  change ((E.differential * g) i j).vertex - cochainSign (K := K) (n - 1) •
    ((g * F.differential) i j).vertex = 0
  rw [hl, hr, smul_zero, sub_zero]

def diagonalVertex (E : BasedComplex Q (K := K) I) (i : I) :
    Matrix I I (Q.Zigzag K) →ₗ[K] K where
  toFun f := (f i i).vertex (E.placement i).color
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fintype V] in
lemma diagonalVertex_boundary (E : BasedComplex Q (K := K) I) (hE : E.IsMinimal Q)
    (i : I) (n v : ℤ) {f : Matrix I I (Q.Zigzag K)}
    (hf : f ∈ homBoundaries Q E E n v) : diagonalVertex Q E i f = 0 := by
  exact congrFun (homBoundary_positive Q E E hE hE n v hf i i) (E.placement i).color

variable [DecidableEq I]

omit [Fintype V] in
lemma identity_mem_homCycles (E : BasedComplex Q (K := K) I) :
    projectiveIdentity Q E.placement ∈ homCycles Q E E 0 0 := by
  exact map_mem_homCycles Q (HomotopyEquivalence.refl Q E).forward

omit [Fintype V] in
lemma diagonalVertex_identity (E : BasedComplex Q (K := K) I) (i : I) :
    diagonalVertex Q E i (projectiveIdentity Q E.placement) = 1 := by
  change (projectiveIdentity Q (K := K) E.placement i i).vertex (E.placement i).color = 1
  rw [projectiveIdentity, Matrix.diagonal_apply_eq, vertexId_eval, ite_eq_left rfl]

def diagonalToken (E : BasedComplex Q (K := K) I) (i : I) : Matrix I I (Q.Zigzag K) :=
  Matrix.diagonal (fun j => if j = i then tokenBasis Q (E.placement i).color else 0)

lemma diagonalToken_entries (E : BasedComplex Q (K := K) I) (i : I) :
    ProjectiveEntries Q E.placement E.placement (diagonalToken Q E i) := by
  classical
  have hl : vertexId Q (K := K) (E.placement i).color * tokenBasis Q (E.placement i).color =
      tokenBasis Q (E.placement i).color := by
    simpa only [Path.source, pathBasis_token] using
      (pathBasis_left Q (K := K) (.inr (.inr (E.placement i).color)))
  have hr : tokenBasis Q (K := K) (E.placement i).color * vertexId Q (E.placement i).color =
      tokenBasis Q (E.placement i).color := by
    simpa only [Path.target, pathBasis_token] using
      (pathBasis_right Q (K := K) (.inr (.inr (E.placement i).color)))
  constructor <;> intro j k
  · by_cases hjk : j = k
    · subst k
      by_cases hji : j = i
      · subst j; simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, hl]
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, MulZeroClass.mul_zero]
    · simp only [diagonalToken, Matrix.diagonal_apply_ne _ hjk, MulZeroClass.mul_zero]
  · by_cases hjk : j = k
    · subst k
      by_cases hji : j = i
      · subst j; simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, hr]
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, MulZeroClass.zero_mul]
    · simp only [diagonalToken, Matrix.diagonal_apply_ne _ hjk, MulZeroClass.zero_mul]

omit [Fintype V] in
lemma diagonalToken_degree (E : BasedComplex Q (K := K) I) (i : I) :
    MapDegree Q E.placement E.placement 0 2 (diagonalToken Q E i) := by
  intro j k
  by_cases hjk : j = k
  · subst k
    constructor
    · intro h; exact (h (by omega)).elim
    · by_cases hji : j = i
      · subst j
        simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true]
        rw [add_sub_cancel_right]
        exact ⟨fun _ => rfl, fun _ => rfl, fun h => (h rfl).elim⟩
      · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji]
        exact homogeneous_zero Q _
  · have hz : diagonalToken Q E i j k = 0 := Matrix.diagonal_apply_ne _ hjk
    rw [hz]
    exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

lemma diagonalToken_mem_homCycles (E : BasedComplex Q (K := K) I)
    (hE : E.IsMinimal Q) (i : I) : diagonalToken Q E i ∈ homCycles Q E E 0 2 := by
  refine ⟨⟨diagonalToken_entries Q E i, diagonalToken_degree Q E i⟩, ?_⟩
  have hl : E.differential * diagonalToken Q E i = 0 := by
    apply Matrix.ext
    intro j k
    rw [diagonalToken, Matrix.mul_diagonal]
    by_cases hki : k = i
    · simp only [ite_eq_left hki, Matrix.zero_apply]
      exact positive_mul_tokenBasis Q _ _ (hE j k)
    · simp only [ite_eq_right hki, MulZeroClass.mul_zero, Matrix.zero_apply]
  have hr : diagonalToken Q E i * E.differential = 0 := by
    apply Matrix.ext
    intro j k
    rw [diagonalToken, Matrix.diagonal_mul]
    by_cases hji : j = i
    · simp only [ite_eq_left hji, Matrix.zero_apply]
      exact tokenBasis_mul_positive Q _ _ (hE j k)
    · simp only [ite_eq_right hji, MulZeroClass.zero_mul, Matrix.zero_apply]
  change E.differential * diagonalToken Q E i -
    cochainSign (K := K) 0 • (diagonalToken Q E i * E.differential) = 0
  rw [hl, hr, smul_zero, sub_zero]

lemma supertrace_diagonalToken (E : BasedComplex Q (K := K) I) (i : I) :
    supertrace Q E (diagonalToken Q E i) = cochainSign (K := K) (E.placement i).cochain := by
  change (∑ j, cochainSign (K := K) (E.placement j).cochain *
    trace Q (diagonalToken Q E i j j)) = _
  rw [Finset.sum_eq_single i]
  · simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_true, trace_tokenBasis, _root_.mul_one]
  · intro j _ hji
    simp only [diagonalToken, Matrix.diagonal_apply_eq, ite_eq_right hji, trace_zero, MulZeroClass.mul_zero]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
