import OAI.Topology.CoarseAssembly.FiberedGraph
import OAI.Topology.CoarseAssembly.CongruenceFibers
import OAI.Topology.CoarseAssembly.BoundedGeometry

namespace OAI

/-! # A uniform degree bound for the finite fibered graphs

A neighbor is encoded by its base vertex, one integral left move, and nine
binary digits. The digits distinguish children in a successive congruence
fiber; at equal or smaller depth the reduced equation already determines
the target. The resulting bound is independent of the disc radius.
-/

noncomputable section

namespace CoarseAssembly

open Congruence

abbrev FiberBits := Fin 3 → Fin 3 → Fin 2

def fiberBits : (k : ℕ) → Quotient k → FiberBits
  | 0, _ => fun _ _ => 0
  | k + 1, q => matrixTopBits k q

def baseNeighbors {j : ℕ} (u : Disc j) : Finset (Disc j) := by
  classical
  exact Finset.univ.filter (fun v => v = u ∨ (discGraph j).Adj u v)

@[simp] theorem mem_baseNeighbors {j : ℕ} (u v : Disc j) :
    v ∈ baseNeighbors u ↔ v = u ∨ (discGraph j).Adj u v := by
  classical
  simp [baseNeighbors]

theorem card_baseNeighbors_le {j : ℕ} (u : Disc j) : (baseNeighbors u).card ≤ 7 := by
  classical
  have himage : (baseNeighbors u).image Subtype.val ⊆ insert u.val (latticeNeighbors u.val) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    rcases (mem_baseNeighbors u w).mp hw with hw | hw
    · subst w; exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_latticeNeighbors_iff _ _).mpr hw)
  calc
    (baseNeighbors u).card = ((baseNeighbors u).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ (insert u.val (latticeNeighbors u.val)).card := Finset.card_le_card himage
    _ ≤ (latticeNeighbors u.val).card + 1 := Finset.card_insert_le _ _
    _ ≤ 7 := by have := card_latticeNeighbors_le u.val; omega

private theorem fiberBits_injective {k l : ℕ} (h : l = k + 1)
    (q r : Quotient l) (he : quotientMap (by omega : k ≤ l) q =
      quotientMap (by omega : k ≤ l) r) (hb : fiberBits l q = fiberBits l r) : q = r := by
  subst l
  exact quotient_fiber_code_injective k he hb

private theorem target_eq_of_same_code {t : ℤ_[2]ˣ}
    {j : ℕ} (x : FiberVertex j) (v : Disc j) (q r : Quotient (discDepth j v))
    (s : ArithmeticGroup)
    (hp : x.1 = v ∨ (discGraph j).Adj x.1 v ∧ s = 1)
    (hq : ∀ m (hx : m ≤ discDepth j x.1) (hv : m ≤ discDepth j v),
      quotientMap hv q = reduce m s * quotientMap hx x.2 *
        holonomy t m ^ latticeCharge x.1.val v.val)
    (hr : ∀ m (hx : m ≤ discDepth j x.1) (hv : m ≤ discDepth j v),
      quotientMap hv r = reduce m s * quotientMap hx x.2 *
        holonomy t m ^ latticeCharge x.1.val v.val)
    (hbits : fiberBits (discDepth j v) q = fiberBits (discDepth j v) r) : q = r := by
  by_cases hvx : discDepth j v ≤ discDepth j x.1
  · have he := (hq _ hvx le_rfl).trans (hr _ hvx le_rfl).symm
    simpa only [quotientMap_self] using he
  · have hdepth : discDepth j v = discDepth j x.1 + 1 := by
      rcases hp with hp | ⟨hp, hs⟩
      · subst v; omega
      · have := discDepth_adj hp
        rw [abs_le] at this
        omega
    have he := (hq _ le_rfl (by omega)).trans (hr _ le_rfl (by omega)).symm
    exact fiberBits_injective hdepth q r he hbits

private def neighborMove {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) (y : {y // (fiberedGraph S t j).Adj x y}) : ArithmeticGroup :=
  y.property.2.choose

private theorem neighborMove_spec {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) (y : {y // (fiberedGraph S t j).Adj x y}) :
    neighborMove x y ∈ symmetricMoves S ∧
    (x.1 = y.val.1 ∨ (discGraph j).Adj x.1 y.val.1 ∧ neighborMove x y = 1) ∧
    ∀ l (hx : l ≤ discDepth j x.1) (hy : l ≤ discDepth j y.val.1),
      fiberCoordinate y.val hy = reduce l (neighborMove x y) * fiberCoordinate x hx *
        holonomy t l ^ fiberCharge x y.val := y.property.2.choose_spec

private def neighborCode {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) (y : {y // (fiberedGraph S t j).Adj x y}) :
    {v // v ∈ baseNeighbors x.1} × {s // s ∈ symmetricMoves S} × FiberBits := by
  refine ⟨⟨y.val.1, ?_⟩, ⟨neighborMove x y, (neighborMove_spec x y).1⟩,
    fiberBits _ y.val.2⟩
  apply (mem_baseNeighbors _ _).mpr
  exact ((neighborMove_spec x y).2.1).elim (fun h => Or.inl h.symm) (fun h => Or.inr h.1)

private theorem neighborCode_injective {S : Finset ArithmeticGroup} {t : ℤ_[2]ˣ} {j : ℕ}
    (x : FiberVertex j) : Function.Injective (neighborCode (S := S) (t := t) x) := by
  intro y z he
  have hb : y.val.1 = z.val.1 := congrArg (fun c => c.1.val) he
  have hs : neighborMove x y = neighborMove x z := congrArg (fun c => c.2.1.val) he
  have hc : fiberBits _ y.val.2 = fiberBits _ z.val.2 := congrArg (fun c => c.2.2) he
  apply Subtype.ext
  rcases y with ⟨⟨v, q⟩, hy⟩
  rcases z with ⟨⟨w, r⟩, hz⟩
  dsimp only at hb
  subst w
  apply congrArg (Sigma.mk v)
  apply target_eq_of_same_code x v q r (neighborMove x ⟨⟨v, q⟩, hy⟩)
    (neighborMove_spec x ⟨⟨v, q⟩, hy⟩).2.1
  · exact (neighborMove_spec x ⟨⟨v, q⟩, hy⟩).2.2
  · simpa only [hs, fiberCoordinate, fiberCharge] using (neighborMove_spec x ⟨⟨v, r⟩, hz⟩).2.2
  · exact hc

/-- A bound uniform in the component and in the chosen vertex. -/
theorem card_fibered_neighbors_le (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    Nat.card {y // (fiberedGraph S t j).Adj x y} ≤
      7 * (symmetricMoves S).card * 2 ^ 9 := by
  classical
  rw [Nat.card_eq_fintype_card]
  have h := Fintype.card_le_of_injective _ (neighborCode_injective (S := S) (t := t) x)
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun,
    Fintype.card_fin, FiberBits] at h
  calc
    _ ≤ (baseNeighbors x.1).card * ((symmetricMoves S).card * (2 ^ 3) ^ 3) := h
    _ ≤ 7 * ((symmetricMoves S).card * (2 ^ 3) ^ 3) :=
      Nat.mul_le_mul_right _ (card_baseNeighbors_le x.1)
    _ = _ := by ring

def fiberedNeighbors (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ) {j : ℕ}
    (x : FiberVertex j) : Finset (FiberVertex j) := by
  classical
  exact Finset.univ.filter (fun y => (fiberedGraph S t j).Adj x y)

@[simp] theorem mem_fiberedNeighbors (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x y : FiberVertex j) :
    y ∈ fiberedNeighbors S t x ↔ (fiberedGraph S t j).Adj x y := by
  classical
  simp [fiberedNeighbors]

theorem card_fiberedNeighbors_le (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) :
    (fiberedNeighbors S t x).card ≤ 7 * (symmetricMoves S).card * 2 ^ 9 := by
  classical
  have h := card_fibered_neighbors_le S t x
  simpa only [Nat.card_eq_fintype_card, Fintype.card_subtype,
    fiberedNeighbors] using h

/-- Uniform bounded geometry in the intrinsic graph distance. -/
theorem fiberedGraph_ball_bound (S : Finset ArithmeticGroup) (t : ℤ_[2]ˣ)
    {j : ℕ} (x : FiberVertex j) (r : ℕ) :
    Set.ncard {y | (fiberedGraph S t j).edist x y ≤ (r : ℕ∞)} ≤
      (7 * (symmetricMoves S).card * 2 ^ 9 + 1) ^ r := by
  classical
  exact ncard_edist_ball_le (fiberedNeighbors S t) _
    (fun x y h => (mem_fiberedNeighbors S t x y).mpr h)
    (card_fiberedNeighbors_le S t) x r

end CoarseAssembly

end

end OAI
