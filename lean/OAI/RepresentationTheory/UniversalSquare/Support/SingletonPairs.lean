import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.GeneralDetection
import OAI.RepresentationTheory.UniversalSquare.Specht.WeightedRestriction
import OAI.RepresentationTheory.UniversalSquare.Specht.AlternateColumns

namespace OAI

/-! Singleton Pairs. -/

section

noncomputable section
namespace Saxl

def symmetricPartialPairs {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (i : Fin b ↪ Fin a) (v : Fin d → ℂ) : WordSpace n d := fun w =>
  if leftWord e w ∘ i = rightWord e w then
    ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (leftWord e w k) else 0

lemma wordMap_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (L : Fin d → Fin D → ℂ) (x : WordSpace a d) (y : WordSpace b d) :
    wordMap L (positionProduct e x y) =
      positionProduct e (wordMap L x) (wordMap L y) := by
  classical
  funext w
  change (∑ c, (x (leftWord e c) * y (rightWord e c)) * ∏ i, L (c i) (w i)) = _
  calc
    _ = ∑ p : (Fin a → Fin d) × (Fin b → Fin d),
        (x p.1 * ∏ i, L (p.1 i) (leftWord e w i)) *
          (y p.2 * ∏ i, L (p.2 i) (rightWord e w i)) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro c
      have he : (∏ i, L (c i) (w i)) =
          (∏ i, L (leftWord e c i) (leftWord e w i)) *
            ∏ i, L (rightWord e c i) (rightWord e w i) := by
        calc
          _ = ∏ z : Fin a ⊕ Fin b, L (c (e.symm z)) (w (e.symm z)) :=
            (Equiv.prod_comp e.symm (fun i => L (c i) (w i))).symm
          _ = _ := by rw [Fintype.prod_sum_type]; rfl
      rw [he]
      change _ = (x (leftWord e c) * _) * (y (rightWord e c) * _)
      dsimp [positionWordsEquiv]
      ring
    _ = _ := by
      change _ = (∑ c, x c * ∏ i, L (c i) (leftWord e w i)) *
        (∑ c, y c * ∏ i, L (c i) (rightWord e w i))
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      simp only [Finset.mul_sum]

lemma letterLift_positionProduct {n a b d D : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (φ : Fin d → Fin D) (x : WordSpace a d) (y : WordSpace b d) :
    letterLift φ (positionProduct e x y) =
      positionProduct e (letterLift φ x) (letterLift φ y) :=
  wordMap_positionProduct e _ x y

lemma letterLift_comp {n a b c : ℕ} (φ : Fin a → Fin b) (ψ : Fin b → Fin c)
    (x : WordSpace n a) : letterLift ψ (letterLift φ x) = letterLift (ψ ∘ φ) x := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  rw [hx, map_sum, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, map_smul, map_smul, letterLift_single,
    letterLift_single, letterLift_single]
  rfl

lemma symmetricPartialPairs_lift_pair {n a b d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b ↪ Fin a)
    (φ : Fin d → Fin D) (hφ : Function.Injective φ)
    (v : Fin D → ℂ) (x : WordSpace n d) :
    dotProduct (letterLift φ x) (symmetricPartialPairs e i v) =
      dotProduct x (symmetricPartialPairs e i (v ∘ φ)) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) ∘ i = rightWord e (φ ∘ w) ↔
      leftWord e w ∘ i = rightWord e w := by
    constructor
    · intro h
      funext k
      exact hφ (congrFun h k)
    · intro h
      funext k
      exact congrArg φ (congrFun h k)
  simp only [symmetricPartialPairs, hh]
  rfl

lemma symmetricPartialPairs_contraction {n a b d D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i : Fin b ↪ Fin a)
    (j : Fin d ↪ Fin D) (v : Fin D → ℂ)
    (x : WordSpace a D) (y : WordSpace b d) :
    dotProduct (positionProduct e x (letterLift j y)) (symmetricPartialPairs e i v) =
      dotProduct (weightedRestrict i j v x) y := by
  classical
  calc
    _ = ∑ p : (Fin a → Fin D) × (Fin b → Fin D),
        x p.1 * letterLift j y p.2 *
          (if p.1 ∘ i = p.2 then
            ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (p.1 k) else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = dotProduct (letterLift j y) (fun r => ∑ l : Fin a → Fin D,
        if l ∘ i = r then x l *
          ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (l k) else 0) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      unfold dotProduct
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      split_ifs <;> ring
    _ = _ := by
      rw [letterLift_pair, dotProduct_comm]
      rfl

lemma alternateTableau_partialPair {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ))
    (hs : HorizontalStrip (halfRows μ) (ceilRows μ)) (v : Fin (μ.colLen 0) → ℂ) :
    dotProduct (polytabloid (alternateTableau μ e s t))
      (symmetricPartialPairs e (tableauInclusion t s hs.1) v) =
      (Nat.card (columnGroup t) : ℂ) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion t s hs.1)),
          v (Fin.cast (ceilRows_height μ) (rowWord s k)) := by
  rw [alternateTableau_factor, ← letterLift_comp, ← letterLift_positionProduct,
    symmetricPartialPairs_lift_pair _ _ _ (Fin.cast_injective _),
    symmetricPartialPairs_contraction, weighted_strip_pair t s hs]
  rfl

lemma tableauInclusion_range {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin n) :
    k ∈ Set.range (tableauInclusion s t h) ↔ (t k).val ∈ ν := by
  constructor
  · rintro ⟨l,rfl⟩
    rw [tableauInclusion_cell]
    exact (s l).property
  · intro hk
    refine ⟨s.symm ⟨(t k).val,hk⟩, ?_⟩
    apply t.injective
    apply Subtype.ext
    rw [tableauInclusion_cell]
    simp

lemma alternateRows_card (μ : YoungDiagram) (k : ℕ)
    (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i)) :
    (ceilRows μ).card = (halfRows μ).card + 1 := by
  have hs : (halfRows μ).cells ⊆ (ceilRows μ).cells := halfRows_le_ceilRows μ
  have hd : (ceilRows μ).cells \ (halfRows μ).cells = {(k, μ.rowLen k / 2)} := by
    ext c
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    exact alternateRows_difference μ k hk he c
  have hh := Finset.card_sdiff_add_card_eq_card hs
  rw [hd, Finset.card_singleton] at hh
  change 1 + (halfRows μ).card = (ceilRows μ).card at hh
  omega

lemma odd_row_lt_height {μ : YoungDiagram} {k : ℕ} (hk : Odd (μ.rowLen k)) :
    k < μ.colLen 0 := by
  apply YoungDiagram.mem_iff_lt_colLen.mp
  apply YoungDiagram.mem_iff_lt_rowLen.mpr
  obtain ⟨q,hq⟩ := hk
  omega

lemma alternateTableau_partialPair_ne_zero {n a b : ℕ} (μ : YoungDiagram)
    (e : Fin n ≃ Fin a ⊕ Fin b) (s : Tableau a (ceilRows μ)) (t : Tableau b (halfRows μ))
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ i, i ≠ k → Even (μ.rowLen i))
    (v : Fin (μ.colLen 0) → ℂ) (hv : v ⟨k, odd_row_lt_height hk⟩ ≠ 0) :
    dotProduct (polytabloid (alternateTableau μ e s t))
      (symmetricPartialPairs e (tableauInclusion t s (halfRows_le_ceilRows μ)) v) ≠ 0 := by
  rw [alternateTableau_partialPair μ e s t (alternateRows_strip μ k hk he)]
  apply mul_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply Finset.prod_ne_zero_iff.mpr
  intro l hl
  have hln : (s l).val ∉ halfRows μ :=
    mt (tableauInclusion_range t s (halfRows_le_ceilRows μ) l).mpr (Finset.mem_filter.mp hl).2
  have hcell := (alternateRows_difference μ k hk he (s l).val).mp ⟨(s l).property,hln⟩
  have hh : Fin.cast (ceilRows_height μ) (rowWord s l) = ⟨k, odd_row_lt_height hk⟩ :=
    Fin.ext (congrArg Prod.fst hcell)
  rwa [hh]

lemma symmetricPartialPairs_action {n a b d : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (i j : Fin b ↪ Fin a)
    (q : Equiv.Perm (Fin a)) (hq : ∀ k, q (i k) = j k) (v : Fin d → ℂ) :
    wordRep n d (sumPerm e q 1) (symmetricPartialPairs e i v) =
      symmetricPartialPairs e j v := by
  classical
  have hrange (k : Fin a) : q k ∈ Set.range j ↔ k ∈ Set.range i := by
    constructor
    · rintro ⟨l,hl⟩
      exact ⟨l, q.injective ((hq l).trans hl)⟩
    · rintro ⟨l,rfl⟩
      exact ⟨l,(hq l).symm⟩
  funext w
  have hl : leftWord e (w ∘ sumPerm e q 1) = leftWord e w ∘ q := by
    funext k
    simp [leftWord]
  have hr : rightWord e (w ∘ sumPerm e q 1) = rightWord e w := by
    funext k
    simp [rightWord]
  have hi : (leftWord e w ∘ q) ∘ i = leftWord e w ∘ j := by
    funext k
    simp only [Function.comp_apply, hq]
  change (if leftWord e (w ∘ sumPerm e q 1) ∘ i = rightWord e (w ∘ sumPerm e q 1)
    then _ else 0) = _
  simp only [hl,hr,hi,symmetricPartialPairs]
  congr 1
  simp only [Finset.prod_filter]
  apply Fintype.prod_equiv q
  intro k
  simp only [hrange, Function.comp_apply]

theorem one_odd_row_symmetricPartialPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin (m+1) ⊕ Fin m) (i : Fin m ↪ Fin (m+1))
    (v : Fin d → ℂ) (hv : v ≠ 0)
    (μ : YoungDiagram) (t : Tableau n μ)
    (k : ℕ) (hk : Odd (μ.rowLen k)) (he : ∀ l, l ≠ k → Even (μ.rowLen l))
    (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPartialPairs e i v)).toRepresentation, F ≠ 0 := by
  classical
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = (m+1)+m := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr e
  have hc := alternateCells_card μ
  have hdif := alternateRows_card μ k hk he
  have hm : (halfRows μ).card = m := by omega
  have hM : (ceilRows μ).card = m+1 := by omega
  let s := canonicalTableau (ceilRows μ) hM
  let r := canonicalTableau (halfRows μ) hm
  let j := tableauInclusion r s (halfRows_le_ceilRows μ)
  let tt := alternateTableau μ e s r
  obtain ⟨a,ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra! hh
    exact hv (funext hh)
  let kk : Fin (μ.colLen 0) := ⟨k, odd_row_lt_height hk⟩
  let φ : Fin (μ.colLen 0) → Fin d :=
    (Equiv.swap (Fin.castLE hd kk) a) ∘ Fin.castLE hd
  have hφ : Function.Injective φ :=
    (Equiv.swap _ _).injective.comp (Fin.castLE_injective hd)
  have hφk : (v ∘ φ) kk ≠ 0 := by simpa [φ] using ha
  have hh : dotProduct (letterLift φ (polytabloid tt))
      (symmetricPartialPairs e j v) ≠ 0 := by
    rw [symmetricPartialPairs_lift_pair _ _ _ hφ]
    exact alternateTableau_partialPair_ne_zero μ e s r k hk he (v ∘ φ) hφk
  have hs := specht_to_cyclic_of_pair tt
    (fun a b => if φ a = b then 1 else 0) (symmetricPartialPairs e j v) hh
  obtain ⟨q,hq⟩ := Equiv.Perm.exists_extending_pair i j i.injective j.injective
  have hcyc : cyclic (wordRep n d) (symmetricPartialPairs e j v) =
      cyclic (wordRep n d) (symmetricPartialPairs e i v) := by
    rw [← symmetricPartialPairs_action e i j q hq v, cyclic_action_eq]
  change ∃ F : Representation.IntertwiningMap (spechtSub tt).toRepresentation
    (cyclic (wordRep n d) (symmetricPartialPairs e j v)).toRepresentation, F ≠ 0 at hs
  rw [spechtSub_tableau_independent tt t, hcyc] at hs
  exact hs

end Saxl
end
end

end OAI
