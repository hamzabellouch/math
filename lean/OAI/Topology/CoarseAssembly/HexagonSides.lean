import OAI.Topology.CoarseAssembly.BoundaryWalks

namespace OAI

/-! # The six oriented sides of the lattice hexagon

These explicit vertex sequences support the boundary-walk construction.
They run counterclockwise from `(j,0)`; only the final side crosses the
half-open positive ray used by the integral charge.
-/

namespace CoarseAssembly

def hexagonPoint (s : Fin 6) (j k : ℕ) : LatticeVertex :=
  match s.val with
  | 0 => ((j : ℤ) - k, k)
  | 1 => (-(k : ℤ), j)
  | 2 => (-(j : ℤ), (j : ℤ) - k)
  | 3 => (-(j : ℤ) + k, -(k : ℤ))
  | 4 => (k, -(j : ℤ))
  | _ => (j, -(j : ℤ) + k)

theorem hexagonPoint_radius (s : Fin 6) (j k : ℕ) (hk : k ≤ j) :
    latticeRadius (hexagonPoint s j k) = j := by
  have hk' : (k : ℤ) ≤ j := by exact_mod_cast hk
  have hj : (0 : ℤ) ≤ j := by positivity
  have hn : (0 : ℤ) ≤ k := by positivity
  fin_cases s <;> simp only [hexagonPoint, latticeRadius]
  all_goals
    apply le_antisymm
    · simp only [max_le_iff, abs_le]
      omega
    · try simp only [show -(j : ℤ) + k + -(k : ℤ) = -(j : ℤ) by ring]
      try simp only [show (j : ℤ) - k + k = (j : ℤ) by ring]
      try simp only [abs_of_nonneg hj, abs_neg]
      omega

def hexagonVertex (s : Fin 6) (j k : ℕ) (hk : k ≤ j) : BoundaryComponent j :=
  ⟨⟨hexagonPoint s j k, (hexagonPoint_radius s j k hk).le⟩,
    (discDepth_eq_zero_iff _ _).mpr (hexagonPoint_radius s j k hk)⟩

theorem hexagonPoint_adj (s : Fin 6) (j k : ℕ) :
    triangularGraph.Adj (hexagonPoint s j k) (hexagonPoint s j (k + 1)) := by
  fin_cases s <;> simp only [hexagonPoint, triangularGraph, Nat.cast_add, Nat.cast_one,
    abs_le, ne_eq, Prod.mk.injEq] <;> omega

theorem hexagonVertex_adj (s : Fin 6) (j k : ℕ) (hk : k + 1 ≤ j) :
    (boundaryGraph j).Adj (hexagonVertex s j k (by omega)) (hexagonVertex s j (k + 1) hk) :=
  hexagonPoint_adj s j k

theorem hexagonPoint_charge (s : Fin 6) (j k : ℕ) (hk : k < j) :
    latticeCharge (hexagonPoint s j k) (hexagonPoint s j (k + 1)) =
      if s = 5 ∧ k + 1 = j then 1 else 0 := by
  have hk' : (k : ℤ) < j := by exact_mod_cast hk
  have hj : (0 : ℤ) < j := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hn : (0 : ℤ) ≤ k := by positivity
  fin_cases s <;> simp only [hexagonPoint, latticeCharge, Nat.cast_add, Nat.cast_one]
  all_goals split_ifs <;> norm_num at * <;> omega

def hexagonSideWalk (s : Fin 6) (j : ℕ) : (k : ℕ) → (hk : k ≤ j) →
    (boundaryGraph j).Walk (hexagonVertex s j 0 (Nat.zero_le j)) (hexagonVertex s j k hk)
  | 0, _ => .nil
  | k + 1, hk => (hexagonSideWalk s j k (by omega)).append
      (hexagonVertex_adj s j k hk).toWalk

def boundaryCharge {j : ℕ} (x y : BoundaryComponent j) : ℤ :=
  latticeCharge x.val.val y.val.val

theorem hexagonSideWalk_charge (s : Fin 6) (j k : ℕ) (hk : k ≤ j) :
    walkCharge boundaryCharge (hexagonSideWalk s j k hk) =
      if s = 5 ∧ k = j ∧ 0 < j then 1 else 0 := by
  induction k with
  | zero =>
    simp only [hexagonSideWalk, walkCharge_nil]
    split_ifs <;> omega
  | succ k ih =>
    have hklt : k < j := by omega
    rw [hexagonSideWalk, walkCharge_append, ih (by omega), walkCharge_cons,
      walkCharge_nil, add_zero]
    change (if s = 5 ∧ k = j ∧ 0 < j then (1 : ℤ) else 0) +
      latticeCharge (hexagonPoint s j k) (hexagonPoint s j (k + 1)) = _
    rw [hexagonPoint_charge s j k hklt]
    simp only [show k ≠ j by omega, and_false, false_and, ite_false, zero_add]
    split_ifs <;> omega

def hexagonCorner (s : Fin 6) (j : ℕ) : BoundaryComponent j :=
  hexagonVertex s j 0 (Nat.zero_le j)

theorem hexagonSide_end (s : Fin 6) (j : ℕ) :
    hexagonVertex s j j le_rfl = hexagonCorner (s + 1) j := by
  fin_cases s <;> apply Subtype.ext <;> apply Subtype.ext <;>
    simp [hexagonVertex, hexagonCorner, hexagonPoint]

def hexagonSide (s : Fin 6) (j : ℕ) :
    (boundaryGraph j).Walk (hexagonCorner s j) (hexagonCorner (s + 1) j) :=
  (hexagonSideWalk s j j le_rfl).copy rfl (hexagonSide_end s j)

theorem hexagonSide_charge (s : Fin 6) (j : ℕ) :
    walkCharge boundaryCharge (hexagonSide s j) = if s = 5 ∧ 0 < j then 1 else 0 := by
  have h := walkCharge_copy boundaryCharge (hexagonSideWalk s j j le_rfl)
    (show hexagonVertex s j 0 (Nat.zero_le j) = hexagonCorner s j from rfl)
    (hexagonSide_end s j)
  exact h.trans (by simpa only [and_true, true_and] using hexagonSideWalk_charge s j j le_rfl)

theorem hexagonCorner_zero (j : ℕ) : hexagonCorner 0 j = boundaryRoot j := by
  apply Subtype.ext
  apply Subtype.ext
  simp [hexagonCorner, hexagonVertex, hexagonPoint, boundaryRoot, discBoundaryBase]

def hexagonalWalk (j : ℕ) : (boundaryGraph j).Walk (boundaryRoot j) (boundaryRoot j) :=
  (((((hexagonSide 0 j).append (hexagonSide 1 j)).append (hexagonSide 2 j)).append
    (hexagonSide 3 j)).append (hexagonSide 4 j) |>.append (hexagonSide 5 j)).copy
      (hexagonCorner_zero j) (hexagonCorner_zero j)

theorem hexagonalWalk_charge (j : ℕ) (hj : 0 < j) :
    walkCharge boundaryCharge (hexagonalWalk j) = 1 := by
  simp only [hexagonalWalk, walkCharge_copy, walkCharge_append, hexagonSide_charge]
  norm_num [hj]

def hexagonalBoundaryWalks : HexagonalBoundaryWalks where
  walk := hexagonalWalk
  charge_one j hj := by
    rw [walkCharge_map]
    exact hexagonalWalk_charge j (by omega)

end CoarseAssembly

end OAI
