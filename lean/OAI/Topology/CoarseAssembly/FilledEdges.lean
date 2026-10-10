import OAI.Topology.CoarseAssembly.FilledDisc

namespace OAI

/-! # Linear edges in the filled polygon

The polygon's straight paths map to the actual barycentric Rips edges.
These identities supply the filling factorization of the boundary walk.
-/

noncomputable section

namespace CoarseAssembly

open Rips

theorem realLatticeRadius_add_le (p q : ℝ × ℝ) :
    realLatticeRadius (p + q) ≤ realLatticeRadius p + realLatticeRadius q := by
  have hp := realLatticeRadius_le_iff.mp (le_refl (realLatticeRadius p))
  have hq := realLatticeRadius_le_iff.mp (le_refl (realLatticeRadius q))
  apply realLatticeRadius_le_iff.mpr
  refine ⟨(abs_add_le _ _).trans (add_le_add hp.1 hq.1),
    (abs_add_le _ _).trans (add_le_add hp.2.1 hq.2.1), ?_⟩
  change |(p.1 + q.1) + (p.2 + q.2)| ≤ _
  rw [show (p.1 + q.1) + (p.2 + q.2) = (p.1 + p.2) + (q.1 + q.2) by ring]
  exact (abs_add_le _ _).trans (add_le_add hp.2.2 hq.2.2)

def realVertex (v : LatticeVertex) : ℝ × ℝ := (v.1, v.2)

theorem realLatticeRadius_vertex (v : LatticeVertex) :
    realLatticeRadius (realVertex v) = (latticeRadius v : ℝ) := by
  unfold realLatticeRadius realVertex latticeRadius
  push_cast
  rfl

def filledVertex {j : ℕ} (v : Disc j) : FilledDisc j :=
  ⟨realVertex v.val, by rw [realLatticeRadius_vertex]; exact_mod_cast v.property⟩

def filledSegment {j : ℕ} (p q : FilledDisc j) : Path p q where
  toFun t := ⟨(1 - (t : ℝ)) • p.val + (t : ℝ) • q.val, by
    calc
      realLatticeRadius ((1 - (t : ℝ)) • p.val + (t : ℝ) • q.val) ≤
          realLatticeRadius ((1 - (t : ℝ)) • p.val) + realLatticeRadius ((t : ℝ) • q.val) :=
        realLatticeRadius_add_le _ _
      _ = (1 - (t : ℝ)) * realLatticeRadius p.val + (t : ℝ) * realLatticeRadius q.val := by
        rw [realLatticeRadius_smul _ (sub_nonneg.mpr t.2.2), realLatticeRadius_smul _ t.2.1]
      _ ≤ (1 - (t : ℝ)) * j + (t : ℝ) * j :=
        add_le_add (mul_le_mul_of_nonneg_left p.property (sub_nonneg.mpr t.2.2))
          (mul_le_mul_of_nonneg_left q.property t.2.1)
      _ = j := by ring⟩
  continuous_toFun := by apply Continuous.subtype_mk; fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp

@[simp] theorem filledSegment_val {j : ℕ} (p q : FilledDisc j) (t : unitInterval) :
    (filledSegment p q t).val = (1 - (t : ℝ)) • p.val + (t : ℝ) • q.val := rfl

theorem latticeHat_vertex (u v : LatticeVertex) :
    latticeHat (realVertex u) v = if v = u then 1 else 0 := by
  classical
  by_cases h : v = u
  · subst v
    simp [latticeHat, realVertex, hatKernel, realLatticeRadius]
  · rw [ite_eq_right h]
    apply le_antisymm _ (latticeHat_nonneg _ _)
    by_contra hn
    have hp := (latticeHat_pos_iff (realVertex u) v).mp (lt_of_not_ge hn)
    dsimp only [realVertex] at hp
    have hx : |u.1 - v.1| < 1 := by exact_mod_cast hp.1
    have hy : |u.2 - v.2| < 1 := by exact_mod_cast hp.2.1
    rw [abs_lt] at hx hy
    apply h
    exact (Prod.ext (by omega) (by omega) : u = v).symm

@[simp] theorem filledToRips_vertex {j : ℕ} (v : Disc j) :
    filledToRipsPoint j (filledVertex v) = vertex v (by norm_num) := by
  classical
  apply Point.ext
  apply Finsupp.ext
  intro w
  change latticeHat (realVertex v.val) w.val = (Finsupp.single v (1 : ℝ)) w
  rw [latticeHat_vertex]
  by_cases h : w = v
  · subst w
    simp
  · have hv : v ≠ w := Ne.symm h
    have hc : w.val ≠ v.val := fun hc => h (Subtype.ext hc)
    simp [hv, hc]

theorem realLatticeRadius_adj_difference {j : ℕ} {u v : Disc j}
    (h : (discGraph j).Adj u v) : realLatticeRadius (realVertex v.val - realVertex u.val) = 1 := by
  have hx := h.1
  have hy := h.2.1
  have hn := h.2.2.2
  have hsum := h.2.2.1
  have hr : latticeRadius (v.val - u.val) = 1 := by
    change max (max |v.val.1 - u.val.1| |v.val.2 - u.val.2|)
      |(v.val.1 - u.val.1) + (v.val.2 - u.val.2)| = 1
    rw [abs_sub_comm] at hx hy hsum
    have hz : v.val.1 - u.val.1 + (v.val.2 - u.val.2) =
        (v.val.1 + v.val.2) - (u.val.1 + u.val.2) := by ring
    rw [hz]
    have hne : u.val.1 ≠ v.val.1 ∨ u.val.2 ≠ v.val.2 := by
      by_contra! hneg
      exact hn (Prod.ext hneg.1 hneg.2)
    apply le_antisymm (max_le (max_le hx hy) hsum)
    rcases hne with hx' | hy'
    · have hpos : 0 < |v.val.1 - u.val.1| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx'))
      exact (show 1 ≤ |v.val.1 - u.val.1| by omega).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · have hpos : 0 < |v.val.2 - u.val.2| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hy'))
      exact (show 1 ≤ |v.val.2 - u.val.2| by omega).trans
        ((le_max_right _ _).trans (le_max_left _ _))
  have he : realVertex v.val - realVertex u.val = realVertex (v.val - u.val) := by
    ext <;> simp [realVertex]
  rw [he, realLatticeRadius_vertex, hr]
  norm_num

theorem latticeHat_eq_radius (p : ℝ × ℝ) (v : LatticeVertex) :
    latticeHat p v = max 0 (1 - realLatticeRadius (p - realVertex v)) := rfl

theorem filledSegment_hat_left {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    latticeHat (filledSegment (filledVertex u) (filledVertex v) t).val u.val = 1 - (t : ℝ) := by
  rw [latticeHat_eq_radius]
  have he : (filledSegment (filledVertex u) (filledVertex v) t).val - realVertex u.val =
      (t : ℝ) • (realVertex v.val - realVertex u.val) := by
    rw [filledSegment_val]
    ext <;> simp [filledVertex] <;> ring
  rw [he, realLatticeRadius_smul _ t.2.1, realLatticeRadius_adj_difference h, mul_one,
    max_eq_right (sub_nonneg.mpr t.2.2)]

theorem filledSegment_hat_right {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    latticeHat (filledSegment (filledVertex u) (filledVertex v) t).val v.val = (t : ℝ) := by
  rw [latticeHat_eq_radius]
  have he : (filledSegment (filledVertex u) (filledVertex v) t).val - realVertex v.val =
      (1 - (t : ℝ)) • (realVertex u.val - realVertex v.val) := by
    rw [filledSegment_val]
    ext <;> simp [filledVertex] <;> ring
  rw [he, realLatticeRadius_smul _ (sub_nonneg.mpr t.2.2),
    realLatticeRadius_adj_difference h.symm, mul_one,
    max_eq_right (by linarith [t.2.1] : 0 ≤ 1 - (1 - (t : ℝ)))]
  ring

theorem Rips.Point.weight_zero_of_two {X : Type*} [PseudoMetricSpace X] [Fintype X]
    {r : ℝ} (p : Point X r) {x y z : X} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hs : p.weight x + p.weight y = 1) : p.weight z = 0 := by
  classical
  have hle : (∑ w ∈ ({x, y, z} : Finset X), p.weight w) ≤ ∑ w : X, p.weight w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun w _ _ => p.nonneg w)
  have hxz : x ≠ z := Ne.symm hzx
  have hyz : y ≠ z := Ne.symm hzy
  simp only [Finset.sum_insert (by simp [hxy, hxz] : x ∉ ({y, z} : Finset X)),
    Finset.sum_insert (by simp [hyz] : y ∉ ({z} : Finset X)), Finset.sum_singleton,
    p.sum_weight] at hle
  exact le_antisymm (by linarith) (p.nonneg z)

/-- The actual hat-function filling agrees exactly with the Rips edge. -/
theorem filledToRips_edge {j : ℕ} {u v : Disc j} (h : (discGraph j).Adj u v)
    (t : unitInterval) :
    filledToRipsPoint j (filledSegment (filledVertex u) (filledVertex v) t) =
      edgePath (show dist u v ≤ (1 : ℝ) by
        rw [discGraphMetric_eq]
        change ((discGraph j).dist u v : ℝ) ≤ 1
        exact_mod_cast (show (discGraph j).dist u v ≤ 1 by
          simpa using (discGraph j).dist_le h.toWalk)) t := by
  classical
  let p := filledToRipsPoint j (filledSegment (filledVertex u) (filledVertex v) t)
  have hleft : p.weight u = 1 - (t : ℝ) := filledSegment_hat_left h t
  have hright : p.weight v = (t : ℝ) := filledSegment_hat_right h t
  have huv : u ≠ v := fun he => h.2.2.2 (congrArg Subtype.val he)
  apply Point.ext
  apply Finsupp.ext
  intro w
  change p.weight w = (1 - (t : ℝ)) * (Finsupp.single u (1 : ℝ) w) +
    (t : ℝ) * (Finsupp.single v (1 : ℝ) w)
  by_cases hwu : w = u
  · subst w
    simpa [Ne.symm huv] using hleft
  by_cases hwv : w = v
  · subst w
    simpa [huv] using hright
  · rw [p.weight_zero_of_two huv hwu hwv (by rw [hleft, hright]; ring)]
    simp [Ne.symm hwu, Ne.symm hwv]

end CoarseAssembly

end

end OAI
