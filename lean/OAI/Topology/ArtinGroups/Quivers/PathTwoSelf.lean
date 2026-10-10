import Mathlib
import OAI.Topology.ArtinGroups.Quivers.PathTwo

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma pathTwo_eq_self {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₁ : x.arrow = 0) :
    pathTwo Q x = x := by
  apply ext
  · exact h₀.symm
  · exact h₁.symm
  · rfl

lemma pathTwo_eq_zero {x : Q.Zigzag K} (h : x.token = 0) : pathTwo Q x = 0 := by
  apply ext
  · rfl
  · rfl
  · exact h

lemma pathTwo_mul_linear_left {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₂ : x.token = 0)
    (y : Q.Zigzag K) : pathTwo Q (x * y) = x * pathOne Q y := by
  apply ext
  · change (0 : V → K) = (x * pathOne Q y).vertex
    rw [vertex_mul, h₀, MulZeroClass.zero_mul]
  · change (0 : A → K) = (x * pathOne Q y).arrow
    rw [arrow_mul, h₀]
    ext a
    change (0 : K) = 0 * y.arrow a + x.arrow a * 0
    simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, zero_add]
  · change (x * y).token = (x * pathOne Q y).token
    rw [token_mul, token_mul, h₀, h₂]
    simp only [MulZeroClass.zero_mul, zero_add]
    rfl

lemma pathTwo_mul_linear_right (x : Q.Zigzag K) {y : Q.Zigzag K}
    (h₀ : y.vertex = 0) (h₂ : y.token = 0) : pathTwo Q (x * y) = pathOne Q x * y := by
  apply ext
  · change (0 : V → K) = (pathOne Q x * y).vertex
    rw [vertex_mul, h₀, MulZeroClass.mul_zero]
  · change (0 : A → K) = (pathOne Q x * y).arrow
    rw [arrow_mul, h₀]
    ext a
    change (0 : K) = 0 * y.arrow a + x.arrow a * 0
    simp only [MulZeroClass.mul_zero, MulZeroClass.zero_mul, zero_add]
  · change (x * y).token = (pathOne Q x * y).token
    rw [token_mul, token_mul, h₀, h₂]
    simp only [MulZeroClass.mul_zero, zero_add]
    rfl

variable {I J L : Type*}

lemma matrixOne_entries {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f) :
    ProjectiveEntries Q p q (matrixOne Q f) := by
  constructor
  · intro i j
    have h := congrArg (pathOne Q) (hf.1 i j)
    rw [pathOne_mul, pathZero_vertexId, pathOne_vertexId,
      MulZeroClass.zero_mul, add_zero] at h
    exact h
  · intro i j
    have h := congrArg (pathOne Q) (hf.2 i j)
    rw [pathOne_mul, pathZero_vertexId, pathOne_vertexId,
      MulZeroClass.mul_zero, zero_add] at h
    exact h

lemma matrixOne_degree {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {n v : ℤ} {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q p q n v f) :
    MapDegree Q p q n v (matrixOne Q f) := by
  intro i j
  constructor
  · intro h
    change pathOne Q (f i j) = 0
    rw [(hf i j).1 h, map_zero]
  · exact ⟨fun _ => rfl, (hf i j).2.2.1, fun _ => rfl⟩

lemma matrixTwo_mul_linear_left [Fintype J]
    {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f)
    (g : Matrix J L (Q.Zigzag K)) :
    matrixTwo Q (f * g) = f * matrixOne Q g := by
  apply Matrix.ext
  intro i k
  change pathTwo Q (∑ j, f i j * g j k) = ∑ j, f i j * pathOne Q (g j k)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathTwo_mul_linear_left Q (hf i j).1 (hf i j).2 _

lemma matrixTwo_mul_linear_right [Fintype J]
    (f : Matrix I J (Q.Zigzag K)) {g : Matrix J L (Q.Zigzag K)} (hg : LinearMatrix Q g) :
    matrixTwo Q (f * g) = matrixOne Q f * g := by
  apply Matrix.ext
  intro i k
  change pathTwo Q (∑ j, f i j * g j k) = ∑ j, pathOne Q (f i j) * g j k
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathTwo_mul_linear_right Q _ (hg j k).1 (hg j k).2

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma token_boundary_primitive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : LinearMatrix Q E.differential)
    (hF : LinearMatrix Q F.differential) (n v : ℤ)
    {f : Matrix I J (Q.Zigzag K)}
    (h₂ : ∀ i j, (f i j).vertex = 0 ∧ (f i j).arrow = 0)
    (hf : f ∈ homBoundaries Q E F n v) :
    ∃ g ∈ homSpace Q E F (n-1) v, LinearMatrix Q g ∧
      homDifferential Q E F (n-1) g = f := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨matrixOne Q g, ⟨matrixOne_entries Q hg.1, matrixOne_degree Q hg.2⟩,
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  have hfix : matrixTwo Q (homDifferential Q E F (n-1) g) = homDifferential Q E F (n-1) g := by
    apply Matrix.ext
    intro i j
    exact pathTwo_eq_self Q (h₂ i j).1 (h₂ i j).2
  rw [← hfix]
  change E.differential * matrixOne Q g -
    cochainSign (K := K) (n-1) • (matrixOne Q g * F.differential) =
    matrixTwo Q (E.differential * g - cochainSign (K := K) (n-1) • (g * F.differential))
  rw [map_sub, map_smul, matrixTwo_mul_linear_left Q hE, matrixTwo_mul_linear_right Q _ hF]

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
