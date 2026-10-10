import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Weighted Restriction. -/

section

noncomputable section
namespace Saxl

def weightedRestrict {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (v : Fin e → ℂ) : WordSpace n e →ₗ[ℂ] WordSpace a d := by
  classical
  exact {
    toFun := fun x b => ∑ c : Fin n → Fin e,
      if c ∘ i = j ∘ b then x c * ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k)
      else 0
    map_add' := by
      intro x y
      funext b
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> ring
    map_smul' := by
      intro z x
      funext b
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      split_ifs <;> ring }

lemma weightedRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (v : Fin e → ℂ) (c : Fin n → Fin e) (b : Fin a → Fin d) :
    weightedRestrict i j v (Pi.single c 1) b =
      if c ∘ i = j ∘ b then ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k)
      else 0 := by
  classical
  simp only [weightedRestrict, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_eq_single c]
  · simp
  · intro c' hc' hne
    rw [Pi.single_eq_of_ne hne]
    split_ifs <;> simp
  · simp

lemma weightedRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n)
    (j : Fin d ↪ Fin e) (v : Fin e → ℂ) (h : Equiv.Perm (Fin a)) (x : WordSpace n e) :
    weightedRestrict i j v (wordRep n e (h.viaEmbedding i) x) =
      wordRep a d h (weightedRestrict i j v x) := by
  classical
  let g := h.viaEmbedding i
  funext b
  change (∑ c : Fin n → Fin e,
    if c ∘ i = j ∘ b then x (c ∘ g) *
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0) =
    ∑ c : Fin n → Fin e,
      if c ∘ i = j ∘ (b ∘ h) then x c *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c *
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0))
  apply Finset.sum_congr rfl
  intro c hc
  have he : c ∘ i = j ∘ b ↔ (c ∘ g) ∘ i = j ∘ (b ∘ h) := by
    constructor
    · intro hh
      funext k
      simpa only [Function.comp_apply, g, Equiv.Perm.viaEmbedding_apply] using congrFun hh (h k)
    · intro hh
      funext k
      have hh' := congrFun hh (h⁻¹ k)
      simpa [Function.comp_apply, g, Equiv.Perm.viaEmbedding_apply] using hh'
  change (if c ∘ i = j ∘ b then x (c ∘ g) *
    ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c k) else 0) =
      if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range i), v (c (g k)) else 0
  by_cases hh : c ∘ i = j ∘ b
  · simp only [ite_eq_left hh, ite_eq_left (he.mp hh)]
    congr 1
    apply Finset.prod_congr rfl
    intro k hk
    rw [Equiv.Perm.viaEmbedding_apply_of_notMem h i k (Finset.mem_filter.mp hk).2]
  · simp only [ite_eq_right hh, ite_eq_right (mt he.mpr hh)]

lemma weighted_strip_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (v : Fin (μ.colLen 0) → ℂ) :
    weightedRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) v
      (polytabloid t) (rowWord s) =
      ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion s t hs.1)),
        v (rowWord t k) := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  have he (g : columnGroup t) :
      (rowWord t ∘ ((g : Equiv.Perm (Fin n))⁻¹ : Equiv.Perm (Fin n))) ∘ i = j ∘ rowWord s ↔ g = 1 := by
    constructor
    · intro hh
      have hf : ∀ k, ((g : Equiv.Perm (Fin n))⁻¹) (i k) = i k := by
        intro k
        apply t.injective
        apply Subtype.ext
        apply Prod.ext
        · have hh' := congrArg Fin.val (congrFun hh k)
          simpa [rowWord, j, rowLetterInclusion, i] using hh'
        · exact (g⁻¹).property (i k)
      have hh' : (g⁻¹ : columnGroup t) = 1 := column_fixed_of_strip s t hs (g⁻¹) hf
      simpa using congrArg Inv.inv hh'
    · rintro rfl
      funext k
      apply Fin.ext
      exact congrArg Prod.fst (tableauInclusion_cell s t hs.1 k)
  let := Fintype.ofFinite (columnGroup t)
  change weightedRestrict i j v (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, weightedRestrict_single, he]
  simp [i]
  rfl

lemma weighted_strip_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (v : Fin (μ.colLen 0) → ℂ) :
    dotProduct (weightedRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) v
      (polytabloid t)) (polytabloid s) =
      (Nat.card (columnGroup s) : ℂ) *
        ∏ k ∈ Finset.univ.filter (fun k => k ∉ Set.range (tableauInclusion s t hs.1)),
          v (rowWord t k) := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := weightedRestrict i j v (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← weightedRestrict_equivariant i j v (g : Equiv.Perm (Fin a)) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) = _
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    weightedRestrict i j v (polytabloid t) (rowWord s) = _
  rw [weighted_strip_coefficient s t hs v, Fintype.card_eq_nat_card]

end Saxl
end
end

end OAI
