import OAI.RepresentationTheory.Saxl.DominatedQuotient

namespace OAI

noncomputable section

open scoped TensorProduct

universe uX uY

namespace Saxl

lemma transpose_card (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  change ((Equiv.prodComm ℕ ℕ).finsetCongr μ.cells).card = μ.cells.card
  simp only [Equiv.finsetCongr_apply, Finset.card_map]

def colTruncate (μ : YoungDiagram) (k : ℕ) := (rowTruncate μ.transpose k).transpose

lemma colTruncate_rowLen (μ : YoungDiagram) (k i : ℕ) :
    (colTruncate μ k).rowLen i = min k (μ.rowLen i) := by
  have hh : ∀ j, j < (colTruncate μ k).rowLen i ↔ j < min k (μ.rowLen i) := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    change (i,j) ∈ (rowTruncate μ.transpose k).transpose ↔ _
    rw [YoungDiagram.mem_transpose]
    change (j,i) ∈ rowTruncate μ.transpose k ↔ _
    rw [mem_rowTruncate, YoungDiagram.mem_transpose]
    simp only [Prod.swap_prod_mk, YoungDiagram.mem_iff_lt_rowLen, lt_min_iff]
    omega
  have h₁ := hh ((colTruncate μ k).rowLen i)
  have h₂ := hh (min k (μ.rowLen i))
  omega

lemma colTruncate_height (μ : YoungDiagram) (k : ℕ) :
    (colTruncate μ k).colLen 0 ≤ μ.colLen 0 := by
  by_contra h
  have hm : (μ.colLen 0,0) ∈ colTruncate μ k := YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hm
  rw [colTruncate_rowLen, rowLen_zero_of_height_le μ le_rfl] at hr
  simp at hr

lemma sum_range_if_lt (f : ℕ → ℕ) {r H : ℕ} (hr : r ≤ H) :
    (∑ i ∈ Finset.range H, if i < r then f i else 0) = ∑ i ∈ Finset.range r, f i := by
  classical
  rw [← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

lemma corner_inequality (μ : YoungDiagram) (k r : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ r ≤ μ.card + r*k := by
  let H := max (μ.colLen 0) r
  have hh : μ.colLen 0 ≤ H := Nat.le_max_left _ _
  have hr : r ≤ H := Nat.le_max_right _ _
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ ((colTruncate_height μ k).trans hh)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  rw [hm, ← rowPrefix_eq_card μ hh]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) ≤ (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  split_ifs <;> omega

lemma corner_equality (μ : YoungDiagram) (k : ℕ) :
    rowPrefix μ.transpose k + rowPrefix μ (μ.colLen k) = μ.card + μ.colLen k*k := by
  let r := μ.colLen k
  let H := μ.colLen 0
  have hr : r ≤ H := μ.colLen_anti 0 k (Nat.zero_le _)
  have hm : rowPrefix μ.transpose k = ∑ i ∈ Finset.range H, min k (μ.rowLen i) := by
    rw [← rowTruncate_card, ← transpose_card (rowTruncate μ.transpose k)]
    change (colTruncate μ k).card = _
    rw [← rowPrefix_eq_card _ (colTruncate_height μ k)]
    exact Finset.sum_congr rfl (fun i _ => colTruncate_rowLen μ k i)
  change rowPrefix μ.transpose k + rowPrefix μ r = μ.card + r*k
  rw [hm, ← rowPrefix_eq_card μ (le_refl H)]
  change _ + (∑ i ∈ Finset.range r, μ.rowLen i) = (∑ i ∈ Finset.range H, μ.rowLen i) + r*k
  have hconst : (∑ i ∈ Finset.range r, k) = r*k := by simp
  rw [← hconst, ← sum_range_if_lt μ.rowLen hr, ← sum_range_if_lt (fun _ => k) hr,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have he : i < r ↔ k < μ.rowLen i := by
    exact YoungDiagram.mem_iff_lt_colLen.symm.trans YoungDiagram.mem_iff_lt_rowLen
  split_ifs with h
  · have hh := he.mp h
    omega
  · have hh := not_congr he |>.mp h
    omega

/- Ordinary conjugation reverses dominance, including empty diagrams. -/
theorem dominates_transpose {μ ν : YoungDiagram} (hc : μ.card = ν.card)
    (h : Dominates μ ν) : Dominates ν.transpose μ.transpose := by
  intro k
  have h₁ := corner_inequality μ k (ν.colLen k)
  have h₂ := corner_equality ν k
  have h₃ := h (ν.colLen k)
  omega

open scoped MonoidAlgebra

end Saxl

namespace Saxl

lemma rowWord_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (j : Fin (μ.colLen 0)) :
    (Finset.univ.filter (fun i => rowWord t i = j)).card = μ.rowLen j := by
  classical
  let e : {i // rowWord t i = j} ≃ Fin (μ.rowLen j) :=
    { toFun := fun i => ⟨(t i.val).val.2, by
        have hh := YoungDiagram.mem_iff_lt_rowLen.mp (t i.val).property
        have hj := congrArg Fin.val i.property
        change (t i.val).val.1 = j.val at hj
        simpa only [hj] using hh⟩
      invFun := fun k => ⟨t.symm ⟨(j.val,k.val), YoungDiagram.mem_iff_lt_rowLen.mpr k.isLt⟩,
        by apply Fin.ext; change (t (t.symm _)).val.1 = _; simp only [Equiv.apply_symm_apply]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply t.injective
        simp only [Equiv.apply_symm_apply]
        apply Subtype.ext
        apply Prod.ext
        · exact (congrArg Fin.val i.property).symm
        · rfl
      right_inv := by intro k; apply Fin.ext; simp only [Equiv.apply_symm_apply] }
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_congr e

@[simp] lemma staircase_transpose (m : ℕ) : (staircase m).transpose = staircase m := by
  apply YoungDiagram.ext
  apply Finset.ext
  intro x
  rcases x with ⟨i,j⟩
  simp only [YoungDiagram.mem_cells, YoungDiagram.mem_transpose, Prod.swap_prod_mk, mem_staircase]
  omega

def signCancelMap {n : ℕ} {X : Type uX} {Y : Type uY} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Equiv.Perm (Fin n)) X} {σ : Representation ℂ (Equiv.Perm (Fin n)) Y}
    (f : Representation.IntertwiningMap (signTwist ρ) σ) :
    Representation.IntertwiningMap ρ (signTwist σ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext x
    change f (ρ g x) = signC g • σ g (f x)
    have hh := LinearMap.congr_fun (f.isIntertwining' g) x
    change f (signC g • ρ g x) = σ g (f x) at hh
    have he := congrArg (fun y => signC g • y) hh
    rw [map_smul, smul_smul, signC_mul_self, one_smul] at he
    exact he

theorem dominated_support (m : ℕ) (_hm : 1 ≤ m) (μ : YoungDiagram)
    (t : Tableau (staircase m).card μ) (hμ : Dominates (staircase m) μ) :
    ∃ f : Representation.IntertwiningMap (spechtRep t)
      (staircaseCyclic m).toRepresentation, f ≠ 0 := by
  classical
  have hc : μ.card = (staircase m).card := by
    simpa only [Fintype.card_fin, Fintype.card_coe] using (Fintype.card_congr t).symm
  have ht : μ.transpose.card = (staircase m).card := by rw [transpose_card, hc]
  have hd : Dominates μ.transpose (staircase m) := by
    simpa only [staircase_transpose] using dominates_transpose hc.symm hμ
  have hw (j : Fin ((staircase m).colLen 0)) :
      (Finset.univ.filter (fun i => repeatedTarget m i = Fin.rev j)).card = (staircase m).rowLen j := by
    simpa only [repeatedTarget, Fin.rev_inj] using rowWord_content (stairTableau m) j
  obtain ⟨F,hF⟩ := young_orbit_map (staircase m) μ.transpose (transposeTableau t)
    ht hd (repeatedTarget m) Fin.revPerm hw
  obtain ⟨φ⟩ := staircase_sign_equiv m
  let Q := F.comp (dominatedQuotient m φ)
  have hQ : Q ≠ 0 := by
    obtain ⟨x,hx⟩ := repeatedTarget_in_quotient m φ
    intro hz
    apply hF
    have hh := congrArg (fun l => l x) hz
    change F (dominatedQuotient m φ x) = 0 at hh
    change dominatedQuotient m φ x = Pi.single (repeatedTarget m) 1 at hx
    rwa [hx] at hh
  obtain ⟨E⟩ := specht_sign_transpose t
  let R := E.symm.toIntertwiningMap.comp (signCancelMap Q)
  have hR : R ≠ 0 := by
    intro hz
    apply hQ
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    have hh := congrArg (fun l => l x) hz
    change E.symm (Q x) = 0 at hh
    exact E.symm.injective (hh.trans (map_zero _).symm)
  let := specht_irreducible t
  have hRs : Function.Surjective R :=
    (Representation.IsIrreducible.surjective_or_eq_zero R).resolve_right hR
  obtain ⟨f,hf⟩ := intertwining_lift_surjective R hRs (Representation.IntertwiningMap.id (spechtRep t))
  refine ⟨f, ?_⟩
  intro hz
  have hzero : (Representation.IntertwiningMap.id (spechtRep t)) = 0 := by
    rw [← hf, hz]
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact map_zero R
  have he := congrArg (fun l : Representation.IntertwiningMap (spechtRep t) (spechtRep t) =>
    l ⟨polytabloid t, mem_cyclic _ _⟩) hzero
  exact polytabloid_ne_zero t (congrArg Subtype.val he)

end Saxl

end

end OAI
