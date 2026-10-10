import OAI.RingTheory.BassTrace.SupportGeometry

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

/-! Canonical affine polyhedral cutting and coning in a real vector space, without
manifold or cross-simplex metric compatibility assumptions. -/

/-! Local finiteness passes to a simplexwise finite subdivision. -/

/-! Geometric subcomplexes used by the compatible-cut lemma. A marked subset
is a union of closed simplices, not necessarily the full complex induced by
its old vertices. Keeping this distinction is essential for unions of levels. -/

namespace BassTrace.Sparse.Cuts

open Set Finset

open scoped Classical

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable {K : Geometry.SimplicialComplex ℝ V} {n : ℕ}

namespace PointFiltration

variable (Q : PointFiltration K n)

lemma face_in_zero_carrier (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i ≤ n) {z : V} (hz : z ∈ Q.Z 0) :
    ∃ S ∈ (Q.T i).faces, S.card = i+1 ∧ ∀ F ∈ (Q.T 0).faces,
      F.card = i+1 → convexHull ℝ (F : Set V) ⊆ Q.Z i → z ∈ F →
      convexHull ℝ (F : Set V) ⊆ convexHull ℝ (S : Set V) := by
  obtain ⟨S,hS,_,_,hc,_,huniq⟩ := Q.zero_carrier hK hi hz
  refine ⟨S,hS,hc,?_⟩
  intro F hF hFc hFZ hzF
  obtain ⟨D,hD⟩ := Q.refines (Nat.zero_le i) hi
  obtain ⟨U,hU,hUZ,hFU⟩ := D.carrier_marked (Q.marked i hi) (hD.symm ▸ hF) hFZ
  have hu := Q.dimension_bound hK hi hU hUZ
  have hlu := (Q.T 0).indep hF |>.card_le_card_of_subset_affineSpan
    ((subset_convexHull ℝ _).trans (hFU.trans (convexHull_subset_affineSpan _)))
  have hcU : U.card = i+1 := by omega
  have he : U = S := huniq U hU (hFU (subset_convexHull ℝ _ hzF)) hcU
  exact he ▸ hFU

lemma flagged_cofaces_card_le_two (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    {i : ℕ} (hi : i < n) {z : V} (hz : z ∈ Q.Z 0) {F : Finset V}
    (hFc : F.card = i+1) (hzF : z ∈ F) (B : Finset (Finset V))
    (hB : ∀ E ∈ B, E ∈ (Q.T 0).faces ∧ E.card = i+2 ∧
      convexHull ℝ (E : Set V) ⊆ Q.Z (i+1) ∧ F ⊆ E) : B.card ≤ 2 := by
  obtain ⟨S,_,hSc,hS⟩ := Q.face_in_zero_carrier hK (show i+1 ≤ n by omega) hz
  apply BassTrace.Sparse.facet_coface_card_le_two (Q.T 0) (S := S) ⟨z,hzF⟩
  · omega
  · exact fun E hE => (hB E hE).1
  · intro E hE
    obtain ⟨_,hc,_,hFE⟩ := hB E hE
    exact ⟨hFE,by omega⟩
  · intro E hE
    obtain ⟨hE,hc,hEZ,hFE⟩ := hB E hE
    exact (subset_convexHull ℝ _).trans (hS E hE (by omega) hEZ (hFE hzF))

def pointedFlags (Q : PointFiltration K n) (Ω : Finset (Finset V)) (z : V) : ℕ → Finset (List (Finset V))
  | 0 => if {z} ∈ Ω ∧ ({z} : Finset V) ∈ (Q.T 0).faces ∧ z ∈ Q.Z 0
      then { [{z}] } else ∅
  | k+1 => (pointedFlags Q Ω z k).biUnion fun L =>
      (Ω.filter fun E => E ∈ (Q.T 0).faces ∧ E.card = k+2 ∧
        convexHull ℝ (E : Set V) ⊆ Q.Z (k+1) ∧ L.headD ∅ ⊆ E).image
        (fun E => E :: L)

lemma pointedFlags_head {Ω : Finset (Finset V)} {z : V} {k : ℕ}
    {L : List (Finset V)} (hL : L ∈ Q.pointedFlags Ω z k) :
    (L.headD ∅).card = k+1 ∧ z ∈ L.headD ∅ := by
  induction k generalizing L with
  | zero =>
    simp only [pointedFlags] at hL
    split_ifs at hL with h
    · simp only [Finset.mem_singleton] at hL
      subst L
      simp
    · simp at hL
  | succ k ih =>
    rw [pointedFlags] at hL
    obtain ⟨M,hM,hL⟩ := Finset.mem_biUnion.mp hL
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hL
    obtain ⟨_,_,hc,_,hME⟩ := Finset.mem_filter.mp hE
    exact ⟨hc,hME (ih hM).2⟩

lemma pointedFlags_card (hK : ∀ F ∈ K.faces, F.card ≤ n+1)
    (Ω : Finset (Finset V)) {z : V} (hz : z ∈ Q.Z 0) {k : ℕ} (hk : k ≤ n) :
    (Q.pointedFlags Ω z k).card ≤ 2^k := by
  induction k with
  | zero =>
    simp only [pointedFlags]
    split_ifs <;> simp
  | succ k ih =>
    rw [pointedFlags]
    apply Finset.card_biUnion_le.trans
    calc
      _ ≤ ∑ _L ∈ Q.pointedFlags Ω z k, 2 := by
        apply Finset.sum_le_sum
        intro L hL
        apply Finset.card_image_le.trans
        apply Q.flagged_cofaces_card_le_two hK (by omega) hz
          (Q.pointedFlags_head hL).1 (Q.pointedFlags_head hL).2
        intro E hE
        exact (Finset.mem_filter.mp hE).2
      _ = (Q.pointedFlags Ω z k).card * 2 := by simp [Nat.mul_comm]
      _ ≤ 2^k * 2 := Nat.mul_le_mul_right 2 (ih (by omega))
      _ = 2^(k+1) := (pow_succ 2 k).symm

end PointFiltration

end

end BassTrace.Sparse.Cuts

end OAI
