import Mathlib
import OAI.Topology.ArtinGroups.Quivers.LinearMatrix

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]

lemma tokenOnly_mul_positive {x y : Q.Zigzag K}
    (hx : x.vertex = 0) (ha : x.arrow = 0) (hy : y.vertex = 0) : x * y = 0 := by
  apply ext
  · change (x * y).vertex = 0
    rw [vertex_mul, hx, MulZeroClass.zero_mul]
  · change (x * y).arrow = 0
    rw [arrow_mul, hx, ha]
    ext a
    simp [leftScale, rightScale]
  · change (x * y).token = 0
    rw [token_mul, hx, ha, hy, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
      backtrack_zero_left, add_zero, add_zero]

lemma positive_mul_tokenOnly {x y : Q.Zigzag K}
    (hx : x.vertex = 0) (hy : y.vertex = 0) (ha : y.arrow = 0) : x * y = 0 := by
  apply ext
  · change (x * y).vertex = 0
    rw [vertex_mul, hx, MulZeroClass.zero_mul]
  · change (x * y).arrow = 0
    rw [arrow_mul, hx, hy]
    ext a
    simp [leftScale, rightScale]
  · change (x * y).token = 0
    rw [token_mul, hx, hy, ha, MulZeroClass.zero_mul, MulZeroClass.mul_zero,
      backtrack_zero_right, add_zero, add_zero]

namespace BasedComplex
variable {I J : Type*} [Fintype I] [Fintype J]

lemma differential_arrow_level (E : BasedComplex Q (K := K) I) {i j : I}
    (h : (E.placement j).level ≠ (E.placement i).level) :
    (E.differential i j).arrow = 0 := by
  by_cases hc : (E.placement j).cochain = (E.placement i).cochain + 1
  · apply (E.degree i j).2.2.1
    dsimp only [GeneratorPlacement.level] at h
    omega
  · rw [(E.degree i j).1 hc]
    rfl

def extendLayer (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (l k : ℤ) :
    Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K) →ₗ[K]
      Matrix I J (Q.Zigzag K) where
  toFun f i j := if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0
  map_add' f g := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ + g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) +
      (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then g ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [add_zero]
  map_smul' r f := by
    apply Matrix.ext
    intro i j
    change (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then r • f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0) =
      r • (if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0)
    split_ifs <;> simp only [smul_zero]

lemma extendLayer_entry (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : I) (j : J) :
    extendLayer Q E F l k f i j = if hi : (E.placement i).level = l then
      if hj : (F.placement j).level = k then f ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := rfl

lemma extendLayer_apply (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    (f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K))
    (i : {i // (E.placement i).level = l}) (j : {j // (F.placement j).level = k}) :
    extendLayer Q E F l k f i j = f i j := by
  change (if hi : (E.placement i.val).level = l then
      if hj : (F.placement j.val).level = k then f ⟨i.val, hi⟩ ⟨j.val, hj⟩ else 0 else 0) = f i j
  rw [dite_eq_left i.property, dite_eq_left j.property]

lemma extendLayer_linear (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (l k : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : LinearMatrix Q f) : LinearMatrix Q (extendLayer Q E F l k f) := by
  intro i j
  simp only [extendLayer_entry]
  split_ifs with hi hj
  · exact hf ⟨i, hi⟩ ⟨j, hj⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

lemma extendLayer_homSpace (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (l k n v : ℤ)
    {f : Matrix {i // (E.placement i).level = l} {j // (F.placement j).level = k} (Q.Zigzag K)}
    (hf : f ∈ homSpace Q (E.pureLayer Q hE l) (F.pureLayer Q hF k) n v) :
    extendLayer Q E F l k f ∈ homSpace Q E F n v := by
  constructor
  · constructor <;> intro i j
    · simp only [extendLayer_entry]
      split_ifs with hi hj
      · exact hf.1.1 ⟨i, hi⟩ ⟨j, hj⟩
      · exact MulZeroClass.mul_zero _
      · exact MulZeroClass.mul_zero _
    · simp only [extendLayer_entry]
      split_ifs with hi hj
      · exact hf.1.2 ⟨i, hi⟩ ⟨j, hj⟩
      · exact MulZeroClass.zero_mul _
      · exact MulZeroClass.zero_mul _
  · intro i j
    simp only [extendLayer_entry]
    split_ifs with hi hj
    · exact hf.2 ⟨i, hi⟩ ⟨j, hj⟩
    · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩
    · exact ⟨fun _ => rfl, homogeneous_zero Q _⟩

end BasedComplex
end HarmonicArtin.ReversibleQuiver.Zigzag

end OAI
