import OAI.Topology.CoarseAssembly.Lattice
import Mathlib.Tactic.NormNum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace OAI

/-! # Connectivity of the triangular lattice discs

Moving a nonzero coordinate one step toward zero stays in the hexagonal
disc and decreases the sum of absolute coordinates. This gives paths to
the origin within each finite base disc.
-/

namespace CoarseAssembly

def discOrigin (j : ℕ) : Disc j := ⟨(0, 0), by simp [latticeRadius]⟩

def discRank {j : ℕ} (u : Disc j) : ℕ := u.val.1.natAbs + u.val.2.natAbs

private theorem disc_lower_neighbor {j : ℕ} (u : Disc j) (hu : u ≠ discOrigin j) :
    ∃ v : Disc j, (discGraph j).Adj u v ∧ discRank v < discRank u := by
  rcases u with ⟨⟨a, b⟩, huj⟩
  have hh := huj
  simp only [latticeRadius, max_le_iff, abs_le] at hh
  have hstep (c d : ℤ) (hc : |c| ≤ (j : ℤ)) (hd : |d| ≤ (j : ℤ))
      (hcd : |c + d| ≤ (j : ℤ)) (ha : |a - c| ≤ 1) (hb : |b - d| ≤ 1)
      (hs : |(a + b) - (c + d)| ≤ 1) (hne : (a, b) ≠ (c, d))
      (hr : c.natAbs + d.natAbs < a.natAbs + b.natAbs) :
      ∃ v : Disc j, (discGraph j).Adj ⟨(a, b), huj⟩ v ∧
        discRank v < discRank ⟨(a, b), huj⟩ := by
    exact ⟨⟨(c, d), by simp only [latticeRadius, max_le_iff]; exact ⟨⟨hc, hd⟩, hcd⟩⟩,
      ⟨ha, hb, hs, hne⟩, hr⟩
  by_cases ha : 0 < a
  · apply hstep (a - 1) b
    · rw [abs_le]; omega
    · rw [abs_le]; omega
    · rw [abs_le]; omega
    · norm_num
    · simp
    · norm_num
    · intro he; have := congrArg Prod.fst he; omega
    · have h1 : (a.natAbs : ℤ) = a := by omega
      have h2 : ((a - 1).natAbs : ℤ) = a - 1 := by omega
      omega
  · by_cases ha' : a < 0
    · apply hstep (a + 1) b
      · rw [abs_le]; omega
      · rw [abs_le]; omega
      · rw [abs_le]; omega
      · norm_num
      · simp
      · norm_num
      · intro he; have := congrArg Prod.fst he; omega
      · have h1 : (a.natAbs : ℤ) = -a := by omega
        have h2 : ((a + 1).natAbs : ℤ) = -(a + 1) := by omega
        omega
    · have ha0 : a = 0 := by omega
      subst a
      have hb0 : b ≠ 0 := by
        intro hb
        apply hu
        subst b
        rfl
      by_cases hb : 0 < b
      · apply hstep 0 (b - 1)
        · simp
        · rw [abs_le]; omega
        · rw [abs_le]; omega
        · simp
        · norm_num
        · norm_num
        · intro he; have := congrArg Prod.snd he; omega
        · have h1 : (b.natAbs : ℤ) = b := by omega
          have h2 : ((b - 1).natAbs : ℤ) = b - 1 := by omega
          omega
      · have hb' : b < 0 := by omega
        apply hstep 0 (b + 1)
        · simp
        · rw [abs_le]; omega
        · rw [abs_le]; omega
        · simp
        · norm_num
        · norm_num
        · intro he; have := congrArg Prod.snd he; omega
        · have h1 : (b.natAbs : ℤ) = -b := by omega
          have h2 : ((b + 1).natAbs : ℤ) = -(b + 1) := by omega
          omega

theorem disc_reachable_origin {j : ℕ} (u : Disc j) :
    (discGraph j).Reachable u (discOrigin j) := by
  induction hn : discRank u using Nat.strong_induction_on generalizing u with
  | h n ih =>
    by_cases hu : u = discOrigin j
    · subst u; exact SimpleGraph.Reachable.refl _
    · obtain ⟨v, huv, hv⟩ := disc_lower_neighbor u hu
      have hvo := ih (discRank v) (by omega) v rfl
      exact huv.reachable.trans hvo

theorem discGraph_connected (j : ℕ) : (discGraph j).Connected where
  preconnected u v := (disc_reachable_origin u).trans (disc_reachable_origin v).symm
  nonempty := ⟨discOrigin j⟩

end CoarseAssembly

end OAI
