import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Symmetric Pairs. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def symmetricPairs {n m : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) (d : ℕ) : WordSpace n d :=
  fun w => if leftWord e w = rightWord e w then 1 else 0

lemma symmetricPairs_real {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m) :
    star (symmetricPairs e d) = symmetricPairs e d := by
  ext w
  simp only [Pi.star_apply, symmetricPairs]
  split_ifs <;> simp

def positionWordsEquiv {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    (Fin n → Fin d) ≃ (Fin a → Fin d) × (Fin b → Fin d) where
  toFun w := (leftWord e w, rightWord e w)
  invFun p := joinPositions e p.1 p.2
  left_inv := joinPositions_parts e
  right_inv p := by simp

lemma symmetricPairs_contraction {n m d : ℕ} (e : Fin n ≃ Fin m ⊕ Fin m)
    (x y : WordSpace m d) :
    dotProduct (positionProduct e x y) (symmetricPairs e d) = dotProduct x y := by
  classical
  unfold dotProduct
  calc
    _ = ∑ p : (Fin m → Fin d) × (Fin m → Fin d),
        x p.1 * y p.2 * (if p.1 = p.2 then 1 else 0) := by
      apply Fintype.sum_equiv (positionWordsEquiv e)
      intro w
      rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp

lemma real_self_pair_ne_zero {n d : ℕ} (x : WordSpace n d)
    (hr : star x = x) (hx : x ≠ 0) : dotProduct x x ≠ 0 := by
  let : PartialOrder ℂ := RCLike.toPartialOrder
  let : StarOrderedRing ℂ := RCLike.toStarOrderedRing
  intro he
  apply hx
  exact dotProduct_self_star_eq_zero.mp (by simpa only [hr] using he)

def halfRows (μ : YoungDiagram) : YoungDiagram where
  cells := μ.cells.filter (fun c => 2*c.2+1 < μ.rowLen c.1)
  isLowerSet := by
    intro x y hxy hy
    obtain ⟨hym,hy⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_filter.mpr ⟨μ.up_left_mem hxy.1 hxy.2 hym, ?_⟩
    have hm := μ.rowLen_anti _ _ hxy.1
    have hj := hxy.2
    omega

lemma mem_halfRows (μ : YoungDiagram) (i j : ℕ) :
    (i,j) ∈ halfRows μ ↔ 2*j+1 < μ.rowLen i := by
  change (i,j) ∈ μ.cells.filter _ ↔ _
  rw [Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨YoungDiagram.mem_iff_lt_rowLen.mpr (by omega),h⟩⟩

lemma halfRows_rowLen (μ : YoungDiagram) (i : ℕ) :
    (halfRows μ).rowLen i = μ.rowLen i / 2 := by
  have hh : ∀ j, j < (halfRows μ).rowLen i ↔ j < μ.rowLen i / 2 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen, mem_halfRows]
    omega
  have h₁ := hh ((halfRows μ).rowLen i)
  have h₂ := hh (μ.rowLen i / 2)
  omega

lemma halfRows_height (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    (halfRows μ).colLen 0 = μ.colLen 0 := by
  have hh : ∀ i, i < (halfRows μ).colLen 0 ↔ i < μ.colLen 0 := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, ← YoungDiagram.mem_iff_lt_colLen,
      mem_halfRows, YoungDiagram.mem_iff_lt_rowLen]
    obtain ⟨k,hk⟩ := he i
    omega
  have h₁ := hh ((halfRows μ).colLen 0)
  have h₂ := hh (μ.colLen 0)
  omega

def pairedCells (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    (halfRows μ).cells ⊕ (halfRows μ).cells ≃ μ.cells where
  toFun := Sum.elim
    (fun c => ⟨(c.val.1,2*c.val.2), YoungDiagram.mem_iff_lt_rowLen.mpr (by
      have h : 2*c.val.2+1 < μ.rowLen c.val.1 := (mem_halfRows μ _ _).mp c.property
      change 2*c.val.2 < μ.rowLen c.val.1
      omega)⟩)
    (fun c => ⟨(c.val.1,2*c.val.2+1), YoungDiagram.mem_iff_lt_rowLen.mpr
      ((mem_halfRows μ _ _).mp c.property)⟩)
  invFun c :=
    if h : c.val.2 % 2 = 0 then Sum.inl ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      obtain ⟨k,hk⟩ := he c.val.1
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
    else Sum.inr ⟨(c.val.1,c.val.2/2), (mem_halfRows μ _ _).mpr (by
      have hc : c.val.2 < μ.rowLen c.val.1 := YoungDiagram.mem_iff_lt_rowLen.mp c.property
      change 2*(c.val.2/2)+1 < μ.rowLen c.val.1
      omega)⟩
  left_inv c := by
    cases c with
    | inl c => simp
    | inr c =>
      simp
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (2*c.val.2+1)/2 = c.val.2
        omega
  right_inv c := by
    dsimp only
    split_ifs with h
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2) = c.val.2
        change c.val.2 % 2 = 0 at h
        omega
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change 2*(c.val.2/2)+1 = c.val.2
        change c.val.2 % 2 ≠ 0 at h
        omega

def pairedTableau {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) : Tableau n μ :=
  e.trans ((Equiv.sumCongr s s).trans (pairedCells μ he))

lemma pairedTableau_left {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inl i))).val =
      ((s i).val.1, 2*(s i).val.2) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_right {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) (i : Fin m) :
    (pairedTableau μ he e s (e.symm (Sum.inr i))).val =
      ((s i).val.1, 2*(s i).val.2+1) := by
  simp [pairedTableau, pairedCells]

lemma pairedTableau_group_sector {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    columnGroup (pairedTableau μ he e s) ≤ sectorGroup (fun i => (e i).isLeft = true) := by
  intro g hg i
  have hc := hg i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  obtain ⟨k,hk⟩ := e.symm.surjective (g (e.symm j))
  rw [← hk] at hc ⊢
  cases j <;> cases k <;>
    simp only [Equiv.apply_symm_apply, Sum.isLeft_inl, Sum.isLeft_inr] at *
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega
  · rw [pairedTableau_left, pairedTableau_right] at hc
    dsimp only at hc
    omega

lemma pairedTableau_factor {n m : ℕ} (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i))
    (e : Fin n ≃ Fin m ⊕ Fin m) (s : Tableau m (halfRows μ)) :
    polytabloid (pairedTableau μ he e s) = positionProduct e
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s))
      (letterLift (Fin.cast (halfRows_height μ he)) (polytabloid s)) := by
  let t := pairedTableau μ he e s
  let f : Fin n → ℕ := fun i => (t i).val.2
  have hn : columnGroup t = fiberGroup f := rfl
  have hg : columnGroup t = fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true) := by
    rw [← hn]
    exact (inf_eq_left.mpr (pairedTableau_group_sector μ he e s)).symm
  have hl : fiberGroup (fun i => f (e.symm (Sum.inl i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inl (g i)))).val.2 =
      (t (e.symm (Sum.inl i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_left, Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hr : fiberGroup (fun i => f (e.symm (Sum.inr i))) = columnGroup s := by
    apply Subgroup.ext
    intro g
    change (∀ i, (t (e.symm (Sum.inr (g i)))).val.2 =
      (t (e.symm (Sum.inr i))).val.2) ↔ ∀ i, (s (g i)).val.2 = (s i).val.2
    simp only [t, pairedTableau_right, Nat.add_right_cancel_iff,
      Nat.mul_right_inj (by decide : 2 ≠ 0)]
  have hw₁ : leftWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inl i))).val.1 = (s i).val.1
    rw [pairedTableau_left]
  have hw₂ : rightWord e (rowWord t) = Fin.cast (halfRows_height μ he) ∘ rowWord s := by
    funext i
    apply Fin.ext
    change (t (e.symm (Sum.inr i))).val.1 = (s i).val.1
    rw [pairedTableau_right]
  change polytabloid t = _
  rw [polytabloid_eq_altWord, hg, altWord_fiber_split, hl, hr, hw₁, hw₂,
    ← letterLift_altWord, ← polytabloid_eq_altWord]

lemma letterLift_real {n a b : ℕ} (φ : Fin a → Fin b) (x : WordSpace n a)
    (hr : star x = x) : star (letterLift φ x) = letterLift φ x := by
  classical
  funext w
  change star (∑ c, x c * ∏ i, if φ (c i) = w i then (1 : ℂ) else 0) = _
  simp only [star_sum, star_mul, star_prod, apply_ite, star_one, star_zero]
  have hx (c) : star (x c) = x c := congrFun hr c
  simp_rw [hx]
  simp only [letterLift, wordMap, mul_comm]
  rfl

lemma letterLift_pair {n a b : ℕ} (φ : Fin a → Fin b)
    (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (letterLift φ x) y = dotProduct x (fun w => y (φ ∘ w)) := by
  classical
  have hx : x = ∑ w, x w • Pi.single w (1 : ℂ) := by
    funext w
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    map_smul, letterLift_single]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext w
  simp [Pi.single_apply]

lemma letterLift_symmetricPairs_pair {n m a b : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (φ : Fin a → Fin b)
    (hφ : Function.Injective φ) (x : WordSpace n a) :
    dotProduct (letterLift φ x) (symmetricPairs e b) =
      dotProduct x (symmetricPairs e a) := by
  rw [letterLift_pair]
  congr 1
  funext w
  have hh : leftWord e (φ ∘ w) = rightWord e (φ ∘ w) ↔
      leftWord e w = rightWord e w := by
    constructor
    · intro h
      funext i
      exact hφ (congrFun h i)
    · intro h
      funext i
      exact congrArg φ (congrFun h i)
  simp only [symmetricPairs, hh]

lemma pairedTableau_contraction {n m : ℕ} (μ : YoungDiagram)
    (he : ∀ i, Even (μ.rowLen i)) (e : Fin n ≃ Fin m ⊕ Fin m)
    (s : Tableau m (halfRows μ)) :
    dotProduct (polytabloid (pairedTableau μ he e s))
      (symmetricPairs e (μ.colLen 0)) ≠ 0 := by
  rw [pairedTableau_factor, symmetricPairs_contraction]
  apply real_self_pair_ne_zero
  · exact letterLift_real _ _ (polytabloid_real s)
  · intro hz
    apply polytabloid_ne_zero s
    exact letterLift_injective _ (Fin.cast_injective _) (hz.trans (map_zero _).symm)

lemma halfRows_card (μ : YoungDiagram) (he : ∀ i, Even (μ.rowLen i)) :
    2 * (halfRows μ).card = μ.card := by
  have hc := Fintype.card_congr (pairedCells μ he)
  simpa only [Fintype.card_sum, Fintype.card_coe, ← two_mul] using hc

theorem even_rows_symmetricPairs_support {n m d : ℕ}
    (e : Fin n ≃ Fin m ⊕ Fin m) (μ : YoungDiagram) (t : Tableau n μ)
    (he : ∀ i, Even (μ.rowLen i)) (hd : μ.colLen 0 ≤ d) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) (symmetricPairs e d)).toRepresentation, F ≠ 0 := by
  have hn : μ.card = n := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have hnm : n = 2*m := by
    simpa only [Fintype.card_fin, Fintype.card_sum, ← two_mul] using Fintype.card_congr e
  have hm : (halfRows μ).card = m := by
    have hc := halfRows_card μ he
    omega
  let s := canonicalTableau (halfRows μ) hm
  let es : Fin n ≃ Fin m ⊕ Fin m := t.trans ((pairedCells μ he).symm.trans
    (Equiv.sumCongr s.symm s.symm))
  have ht : pairedTableau μ he es s = t := by
    apply Equiv.ext
    intro i
    change pairedCells μ he ((Equiv.sumCongr s s)
      ((Equiv.sumCongr s s).symm ((pairedCells μ he).symm (t i)))) = t i
    simp only [Equiv.apply_symm_apply]
  let φ : Fin (μ.colLen 0) → Fin d := Fin.castLE hd
  have hh : dotProduct (letterLift φ (polytabloid t)) (symmetricPairs es d) ≠ 0 := by
    rw [letterLift_symmetricPairs_pair _ φ (Fin.castLE_injective hd), ← ht]
    exact pairedTableau_contraction μ he es s
  have hsupp := hom_to_cyclic_of_pair
    (fun a b => if φ a = b then 1 else 0) (spechtSub t)
    ⟨polytabloid t, mem_cyclic _ _⟩ (symmetricPairs es d) (symmetricPairs_real es) hh
  let g : Equiv.Perm (Fin n) := e.trans es.symm
  have hg : wordRep n d g (symmetricPairs e d) = symmetricPairs es d := by
    funext w
    have hl : leftWord e (w ∘ g) = leftWord es w := by
      funext i
      simp [leftWord, g]
    have hr : rightWord e (w ∘ g) = rightWord es w := by
      funext i
      simp [rightWord, g]
    change (if leftWord e (w ∘ g) = rightWord e (w ∘ g) then 1 else 0) = _
    simp only [hl, hr, symmetricPairs]
  have hc : cyclic (wordRep n d) (symmetricPairs es d) =
      cyclic (wordRep n d) (symmetricPairs e d) := by
    rw [← hg, cyclic_action_eq]
  change ∃ f : Representation.IntertwiningMap (spechtRep t)
    (cyclic (wordRep n d) (symmetricPairs es d)).toRepresentation, f ≠ 0 at hsupp
  rw [hc] at hsupp
  exact hsupp

end Saxl
end
end

end OAI
