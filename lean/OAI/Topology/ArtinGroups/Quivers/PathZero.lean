import Mathlib
import OAI.Topology.ArtinGroups.Quivers.LinearMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

def pathZero : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (x.vertex, 0, 0)
  map_add' x y := by
    apply ext
    · rfl
    · change (0 : A → K) = 0 + 0
      rw [add_zero]
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
  map_smul' r x := by
    apply ext
    · rfl
    · change (0 : A → K) = r • 0
      rw [smul_zero]
    · change (0 : V → K) = r • 0
      rw [smul_zero]

def pathOne : Q.Zigzag K →ₗ[K] Q.Zigzag K where
  toFun x := (0, x.arrow, 0)
  map_add' x y := by
    apply ext
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
    · rfl
    · change (0 : V → K) = 0 + 0
      rw [add_zero]
  map_smul' r x := by
    apply ext
    · change (0 : V → K) = r • 0
      rw [smul_zero]
    · rfl
    · change (0 : V → K) = r • 0
      rw [smul_zero]

lemma pathZero_mul (x y : Q.Zigzag K) :
    pathZero Q (x * y) = pathZero Q x * pathZero Q y := by
  apply ext
  · change (x * y).vertex = (pathZero Q x * pathZero Q y).vertex
    rw [vertex_mul, vertex_mul]
    rfl
  · change (0 : A → K) = (pathZero Q x * pathZero Q y).arrow
    rw [arrow_mul]
    change (0 : A → K) = Q.leftScale x.vertex 0 + Q.rightScale 0 y.vertex
    ext a
    simp [leftScale, rightScale]
  · change (0 : V → K) = (pathZero Q x * pathZero Q y).token
    rw [token_mul]
    change (0 : V → K) = x.vertex * 0 + 0 * y.vertex + Q.backtrack 0 0
    simp

lemma pathOne_mul (x y : Q.Zigzag K) :
    pathOne Q (x * y) = pathZero Q x * pathOne Q y + pathOne Q x * pathZero Q y := by
  apply ext
  · change (0 : V → K) = (pathZero Q x * pathOne Q y).vertex +
      (pathOne Q x * pathZero Q y).vertex
    rw [vertex_mul, vertex_mul]
    change (0 : V → K) = x.vertex * 0 + 0 * y.vertex
    simp
  · change (x * y).arrow = (pathZero Q x * pathOne Q y).arrow +
      (pathOne Q x * pathZero Q y).arrow
    rw [arrow_mul, arrow_mul, arrow_mul]
    change Q.leftScale x.vertex y.arrow + Q.rightScale x.arrow y.vertex =
      (Q.leftScale x.vertex y.arrow + Q.rightScale 0 0) +
        (Q.leftScale 0 0 + Q.rightScale x.arrow y.vertex)
    ext a
    simp [leftScale, rightScale]
  · change (0 : V → K) = (pathZero Q x * pathOne Q y).token +
      (pathOne Q x * pathZero Q y).token
    rw [token_mul, token_mul]
    change (0 : V → K) = (x.vertex * 0 + 0 * 0 + Q.backtrack 0 y.arrow) +
      (0 * 0 + 0 * y.vertex + Q.backtrack x.arrow 0)
    simp

lemma pathZero_vertexId (α : V) : pathZero Q (vertexId Q (K := K) α) = vertexId Q α := rfl
lemma pathOne_vertexId (α : V) : pathOne Q (vertexId Q (K := K) α) = 0 := rfl

lemma pathZero_eq_zero {x : Q.Zigzag K} (h : x.vertex = 0) : pathZero Q x = 0 := by
  apply ext
  · exact h
  · rfl
  · rfl

lemma pathOne_eq_self {x : Q.Zigzag K} (h₀ : x.vertex = 0) (h₂ : x.token = 0) :
    pathOne Q x = x := by
  apply ext
  · exact h₀.symm
  · rfl
  · exact h₂.symm

variable {I J L : Type*}

def matrixZero : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathZero Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathZero Q).map_smul' r (f i j)

def matrixOne : Matrix I J (Q.Zigzag K) →ₗ[K] Matrix I J (Q.Zigzag K) where
  toFun f i j := pathOne Q (f i j)
  map_add' f g := by apply Matrix.ext; intro i j; exact map_add _ _ _
  map_smul' r f := by apply Matrix.ext; intro i j; exact (pathOne Q).map_smul' r (f i j)

lemma matrixZero_eq_zero {f : Matrix I J (Q.Zigzag K)} (hf : PositiveMatrix Q f) :
    matrixZero Q f = 0 := by
  apply Matrix.ext
  intro i j
  exact pathZero_eq_zero Q (hf i j)

lemma matrixOne_eq_self {f : Matrix I J (Q.Zigzag K)} (hf : LinearMatrix Q f) :
    matrixOne Q f = f := by
  apply Matrix.ext
  intro i j
  exact pathOne_eq_self Q (hf i j).1 (hf i j).2

lemma matrixZero_mul [Fintype J] (f : Matrix I J (Q.Zigzag K))
    (g : Matrix J L (Q.Zigzag K)) :
    matrixZero Q (f * g) = matrixZero Q f * matrixZero Q g := by
  apply Matrix.ext
  intro i k
  change pathZero Q (∑ j, f i j * g j k) = ∑ j, pathZero Q (f i j) * pathZero Q (g j k)
  rw [map_sum]
  exact Finset.sum_congr rfl fun j _ => pathZero_mul Q _ _

lemma matrixOne_mul [Fintype J] (f : Matrix I J (Q.Zigzag K))
    (g : Matrix J L (Q.Zigzag K)) :
    matrixOne Q (f * g) = matrixZero Q f * matrixOne Q g + matrixOne Q f * matrixZero Q g := by
  apply Matrix.ext
  intro i k
  change pathOne Q (∑ j, f i j * g j k) =
    (∑ j, pathZero Q (f i j) * pathOne Q (g j k)) +
    ∑ j, pathOne Q (f i j) * pathZero Q (g j k)
  rw [map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => pathOne_mul Q _ _

lemma matrixZero_entries {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {f : Matrix I J (Q.Zigzag K)} (hf : ProjectiveEntries Q p q f) :
    ProjectiveEntries Q p q (matrixZero Q f) := by
  constructor
  · intro i j
    have h := congrArg (pathZero Q) (hf.1 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h
  · intro i j
    have h := congrArg (pathZero Q) (hf.2 i j)
    rw [pathZero_mul, pathZero_vertexId] at h
    exact h

lemma matrixZero_degree {p : I → GeneratorPlacement V} {q : J → GeneratorPlacement V}
    {n v : ℤ} {f : Matrix I J (Q.Zigzag K)} (hf : MapDegree Q p q n v f) :
    MapDegree Q p q n v (matrixZero Q f) := by
  intro i j
  constructor
  · intro h
    change pathZero Q (f i j) = 0
    rw [(hf i j).1 h, map_zero]
  · exact ⟨(hf i j).2.1, fun _ => rfl, fun _ => rfl⟩

namespace BasedComplex
variable [Fintype I] [Fintype J]

lemma matrixOne_homDifferential (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n : ℤ) (g : Matrix I J (Q.Zigzag K)) :
    matrixOne Q (homDifferential Q E F n g) =
      matrixOne Q E.differential * matrixZero Q g -
        cochainSign (K := K) n • (matrixZero Q g * matrixOne Q F.differential) := by
  change matrixOne Q (E.differential * g - cochainSign (K := K) n • (g * F.differential)) = _
  rw [map_sub, map_smul, matrixOne_mul, matrixOne_mul,
    matrixZero_eq_zero Q hE, matrixZero_eq_zero Q hF, Matrix.zero_mul, Matrix.mul_zero,
    zero_add, add_zero]

lemma linear_boundary_primitive (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (n v : ℤ) {f : Matrix I J (Q.Zigzag K)} (hlin : LinearMatrix Q f)
    (hf : f ∈ homBoundaries Q E F n v) :
    ∃ g ∈ homSpace Q E F (n - 1) v,
      (∀ i j, (g i j).arrow = 0 ∧ (g i j).token = 0) ∧
      matrixOne Q E.differential * g - cochainSign (K := K) (n - 1) •
        (g * matrixOne Q F.differential) = f := by
  obtain ⟨g, hg, rfl⟩ := hf
  refine ⟨matrixZero Q g, ⟨matrixZero_entries Q hg.1, matrixZero_degree Q hg.2⟩,
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  rw [← matrixOne_homDifferential Q E F hE hF]
  exact matrixOne_eq_self Q hlin

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
