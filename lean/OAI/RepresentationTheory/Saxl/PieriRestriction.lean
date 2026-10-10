import OAI.RepresentationTheory.Saxl.SignEquivalence

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A horizontal strip removes at most one cell in each column. -/
def HorizontalStrip (ν μ : YoungDiagram) : Prop :=
  ν ≤ μ ∧ ∀ x ∈ μ, x ∉ ν → ∀ y ∈ μ, y ∉ ν → x.2 = y.2 → x = y

/- Position embedding induced by inclusion of the actual Young diagrams. -/
def tableauInclusion {a n : ℕ} {ν μ : YoungDiagram} (s : Tableau a ν) (t : Tableau n μ)
    (h : ν ≤ μ) : Fin a ↪ Fin n where
  toFun i := t.symm ⟨(s i).val, h (s i).property⟩
  inj' := by
    intro i j hij
    apply s.injective
    apply Subtype.ext
    simpa using congrArg (fun k => (t k).val) hij

lemma colLen_mono {ν μ : YoungDiagram} (h : ν ≤ μ) (j : ℕ) :
    ν.colLen j ≤ μ.colLen j := by
  by_contra hn
  have hm : (μ.colLen j, j) ∈ ν := YoungDiagram.mem_iff_lt_colLen.mpr (lt_of_not_ge hn)
  exact (lt_irrefl _) (YoungDiagram.mem_iff_lt_colLen.mp (h hm))

def rowLetterInclusion {ν μ : YoungDiagram} (h : ν ≤ μ) : Fin (ν.colLen 0) ↪ Fin (μ.colLen 0) :=
  Fin.castLEEmb (colLen_mono h 0)

/- Restrict letters on a specified position set, and sum over all other letters.
This is precisely contraction with the all-ones functional at deleted positions. -/
def wordRestrict {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e) :
    WordSpace n e →ₗ[ℂ] WordSpace a d where
  toFun x b := ∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x c else 0
  map_add' x y := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then x c + y c else 0) =
      (∑ c, if c ∘ i = j ∘ b then x c else 0) + (∑ c, if c ∘ i = j ∘ b then y c else 0)
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all
  map_smul' r x := by
    ext b
    change (∑ c, if c ∘ i = j ∘ b then r * x c else 0) =
      r * ∑ c, if c ∘ i = j ∘ b then x c else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c hc
    split <;> simp_all

lemma wordRestrict_single {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (c : Fin n → Fin e) (b : Fin a → Fin d) :
    wordRestrict i j (Pi.single c 1) b = if c ∘ i = j ∘ b then 1 else 0 := by
  classical
  change (∑ z : Fin n → Fin e, if z ∘ i = j ∘ b then (Pi.single c (1 : ℂ) : WordSpace n e) z else 0) = _
  rw [Finset.sum_eq_single c]
  · simp
  · intro z hz hzc
    simp [hzc]
  · simp

lemma wordRestrict_equivariant {a n d e : ℕ} (i : Fin a ↪ Fin n) (j : Fin d ↪ Fin e)
    (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)) (hi : ∀ k, g (i k) = i (h k))
    (x : WordSpace n e) :
    wordRestrict i j (wordRep n e g x) = wordRep a d h (wordRestrict i j x) := by
  classical
  ext b
  change (∑ c : Fin n → Fin e, if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    ∑ c : Fin n → Fin e, if c ∘ i = j ∘ (b ∘ h) then x c else 0
  apply Eq.trans ?_ (Equiv.sum_comp (wordPerm n e g)
    (fun c => if c ∘ i = j ∘ (b ∘ h) then x c else 0))
  apply Finset.sum_congr rfl
  intro c hc
  change (if c ∘ i = j ∘ b then x (c ∘ g) else 0) =
    if (c ∘ g) ∘ i = j ∘ (b ∘ h) then x (c ∘ g) else 0
  congr 1
  apply propext
  constructor
  · intro hh
    funext k
    simpa only [Function.comp_apply, hi] using congrFun hh (h k)
  · intro hh
    funext k
    have he := congrFun hh (h⁻¹ k)
    simpa [Function.comp_apply, hi] using he


@[simp] lemma tableauInclusion_cell {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (k : Fin a) :
    (t (tableauInclusion s t h k)).val = (s k).val := by
  change (t (t.symm ⟨(s k).val, h (s k).property⟩)).val = _
  simp

lemma column_fixed_of_strip {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ)
    (g : columnGroup t) (hg : ∀ i, (g : Equiv.Perm (Fin n)) (tableauInclusion s t hs.1 i) =
      tableauInclusion s t hs.1 i) : g = 1 := by
  have hin (k : Fin n) (hk : (t k).val ∈ ν) : (g : Equiv.Perm (Fin n)) k = k := by
    let i := s.symm ⟨(t k).val, hk⟩
    have he : tableauInclusion s t hs.1 i = k := by
      apply t.injective
      apply Subtype.ext
      rw [tableauInclusion_cell]
      simp [i]
    simpa only [he] using hg i
  apply Subtype.ext
  apply Equiv.ext
  intro k
  by_cases hk : (t k).val ∈ ν
  · exact hin k hk
  · have ho : (t ((g : Equiv.Perm (Fin n)) k)).val ∉ ν := by
      intro hh
      have he := hin ((g : Equiv.Perm (Fin n)) k) hh
      have he' := (g : Equiv.Perm (Fin n)).injective he
      exact hk (he' ▸ hh)
    apply t.injective
    apply Subtype.ext
    exact hs.2 _ (t _).property ho _ (t _).property hk (g.property k)

lemma strip_contraction_coefficient {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t) (rowWord s) = 1 := by
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
  change wordRestrict i j (∑ g : columnGroup t,
    signC (g : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0)
      (g : Equiv.Perm (Fin n)) (Pi.single (rowWord t) 1)) (rowWord s) = _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    wordRep_single, wordRestrict_single, he]
  simp

lemma column_viaEmbedding {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (h : ν ≤ μ) (g : columnGroup s) :
    (g : Equiv.Perm (Fin a)).viaEmbedding (tableauInclusion s t h) ∈ columnGroup t := by
  intro k
  by_cases hk : k ∈ Set.range (tableauInclusion s t h)
  · obtain ⟨l, rfl⟩ := hk
    rw [Equiv.Perm.viaEmbedding_apply]
    simpa only [tableauInclusion_cell] using g.property l
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hk]

lemma signC_viaEmbedding {a n : ℕ} (i : Fin a ↪ Fin n) (g : Equiv.Perm (Fin a)) :
    signC (g.viaEmbedding i) = signC g := by
  classical
  simp [signC_def, Equiv.Perm.viaEmbedding, Equiv.Perm.sign_extendDomain]

lemma strip_contraction_pair {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    dotProduct (wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
      (polytabloid t)) (polytabloid s) ≠ 0 := by
  classical
  let i := tableauInclusion s t hs.1
  let j := rowLetterInclusion hs.1
  let x := wordRestrict i j (polytabloid t)
  have hx (g : columnGroup s) : wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a)) x =
      signC (g : Equiv.Perm (Fin a)) • x := by
    rw [← wordRestrict_equivariant i j ((g : Equiv.Perm (Fin a)).viaEmbedding i)
      (g : Equiv.Perm (Fin a)) (Equiv.Perm.viaEmbedding_apply _ _) (polytabloid t)]
    rw [polytabloid_alternating t ⟨_, column_viaEmbedding s t hs.1 g⟩]
    rw [map_smul, signC_viaEmbedding]
  rw [← columnAlt_coefficient]
  let := Fintype.ofFinite (columnGroup s)
  have he : columnAlt s x = (Fintype.card (columnGroup s) : ℂ) • x := by
    change (∑ g : columnGroup s, signC (g : Equiv.Perm (Fin a)) •
      wordRep a (ν.colLen 0) (g : Equiv.Perm (Fin a))) x = _
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, hx, smul_smul,
      signC_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  change columnAlt s x (rowWord s) ≠ 0
  rw [he]
  change (Fintype.card (columnGroup s) : ℂ) *
    wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1) (polytabloid t) (rowWord s) ≠ 0
  rw [strip_contraction_coefficient s t hs, mul_one]
  exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero

/- Positive horizontal-strip Pieri map, equivariant for the full Young subgroup. -/
theorem pieri_strip_restriction {a n : ℕ} {ν μ : YoungDiagram}
    (s : Tableau a ν) (t : Tableau n μ) (hs : HorizontalStrip ν μ) :
    ∃ F : Specht t →ₗ[ℂ] Specht s, F ≠ 0 ∧
      ∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ k, g (tableauInclusion s t hs.1 k) = tableauInclusion s t hs.1 (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x) := by
  let pr := subrepProject (spechtSub s) (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
  let T := wordRestrict (tableauInclusion s t hs.1) (rowLetterInclusion hs.1)
  let F := pr.toLinearMap.comp (T.comp (spechtSub t).toSubmodule.subtype)
  refine ⟨F, ?_, ?_⟩
  · intro hF
    have hp := subrepProject_pair (spechtSub s)
      (fun _ hx => cyclic_star _ (polytabloid_real s) hx)
      (T (polytabloid t)) ⟨polytabloid s, mem_cyclic _ _⟩
    have he : pr (T (polytabloid t)) = 0 := by
      exact congrArg (fun L : Specht t →ₗ[ℂ] Specht s => L ⟨polytabloid t, mem_cyclic _ _⟩) hF
    rw [he] at hp
    exact strip_contraction_pair s t hs (hp.symm.trans (zero_dotProduct _))
  · intro g h hh x
    change pr (T (wordRep n (μ.colLen 0) g x.val)) = spechtRep s h (pr (T x.val))
    rw [wordRestrict_equivariant _ _ g h hh x.val]
    exact LinearMap.congr_fun (pr.isIntertwining' h) (T x.val)

end Saxl

end

end OAI
