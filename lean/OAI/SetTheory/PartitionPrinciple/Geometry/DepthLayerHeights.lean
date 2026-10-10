import OAI.SetTheory.PartitionPrinciple.Transfinite.InaccessibleBounds

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps
universe u v w
variable {X : Type u} {Column : Type v} {Coord : Type w} {P : MeetOrder X}
variable (C : LinearHeightOrder Column) (D : LinearHeightOrder Coord)
variable (depth : X → Nat) (columns : Nat → Column)
variable (seed : {x : X // depth x = 0} → Column × Coord)
variable (coordinate : {x : X // depth x ≠ 0} → Coord)

def depthHeightValue (x : X) : Column × Coord :=
  if h : depth x = 0 then seed ⟨x, h⟩ else (columns (depth x), coordinate ⟨x, h⟩)

theorem depthHeightValue_old (x : X) (h : depth x = 0) :
    depthHeightValue depth columns seed coordinate x = seed ⟨x, h⟩ := by
  simp only [depthHeightValue, dite_eq_left h]

theorem depthHeightValue_fresh (x : X) (h : depth x ≠ 0) :
    depthHeightValue depth columns seed coordinate x = (columns (depth x), coordinate ⟨x, h⟩) := by
  simp only [depthHeightValue, dite_eq_right h]

def depthLayerHeight
    (monotone : ∀ x y, P.le x y → depth x ≤ depth y)
    (increasing : ∀ n m, n < m → C.lt (columns n) (columns m))
    (above : ∀ x n, C.lt (seed x).1 (columns n))
    (seedStrict : ∀ x y, P.le x.val y.val → x.val ≠ y.val → (C.lex D).lt (seed x) (seed y))
    (coordinateStrict : ∀ x y, depth x.val = depth y.val → P.le x.val y.val →
      x.val ≠ y.val → D.lt (coordinate x) (coordinate y)) :
    StrictHeight P (C.lex D).toHeightOrder where
  value := depthHeightValue depth columns seed coordinate
  strict x y lower different := by
    have depths := monotone x y lower
    by_cases hx : depth x = 0
    · rw [depthHeightValue_old depth columns seed coordinate x hx]
      by_cases hy : depth y = 0
      · rw [depthHeightValue_old depth columns seed coordinate y hy]
        exact seedStrict ⟨x, hx⟩ ⟨y, hy⟩ lower different
      · rw [depthHeightValue_fresh depth columns seed coordinate y hy]
        exact Or.inl (above ⟨x, hx⟩ (depth y))
    · have hy : depth y ≠ 0 := by omega
      rw [depthHeightValue_fresh depth columns seed coordinate x hx,
        depthHeightValue_fresh depth columns seed coordinate y hy]
      by_cases same : depth x = depth y
      · exact Or.inr ⟨congrArg columns same, coordinateStrict ⟨x, hx⟩ ⟨y, hy⟩ same lower different⟩
      · exact Or.inl (increasing _ _ (by omega))

theorem depthHeightValue_column_bound (cap : Column)
    (oldBound : ∀ x, C.lt (seed x).1 cap) (columnBound : ∀ n, C.lt (columns n) cap) (x : X) :
    C.lt (depthHeightValue depth columns seed coordinate x).1 cap := by
  by_cases h : depth x = 0
  · rw [depthHeightValue_old depth columns seed coordinate x h]
    exact oldBound ⟨x, h⟩
  · rw [depthHeightValue_fresh depth columns seed coordinate x h]
    exact columnBound (depth x)

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
