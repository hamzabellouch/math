import OAI.RepresentationTheory.Saxl.HorizontalRemoval

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

/- Horizontal-strip chains recording the exact ordered strip sizes. -/
def rowWeights (θ : YoungDiagram) : ℕ → List ℕ
  | 0 => []
  | k+1 => rowWeights θ k ++ [θ.rowLen k]

lemma rowWeights_congr (θ τ : YoungDiagram) (k : ℕ)
    (he : ∀ i < k, θ.rowLen i = τ.rowLen i) : rowWeights θ k = rowWeights τ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rowWeights, rowWeights, ih (fun i hi => he i (by omega)), he k (by omega)]

lemma card_zero_iff_bot (μ : YoungDiagram) : μ.card = 0 ↔ μ = ⊥ := by
  change μ.cells.card = 0 ↔ _
  rw [Finset.card_eq_zero]
  constructor
  · intro h; exact YoungDiagram.ext h
  · intro h; subst μ; rfl

/- The actual constructive sufficiency step in Young's rule. No tableau,
Pieri, or representation hypothesis is assumed by this combinatorial theorem. -/
theorem sizedStripChain_of_dominates (θ τ : YoungDiagram) (k : ℕ)
    (hh : θ.colLen 0 ≤ k) (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    SizedStripChain (rowWeights θ k) ⊥ τ := by
  induction k generalizing θ τ with
  | zero =>
    have hcθ : θ.card = 0 := by
      have he := rowPrefix_eq_card θ hh
      simpa [rowPrefix] using he.symm
    have ht : τ = ⊥ := (card_zero_iff_bot τ).mp (hc.trans hcθ)
    subst τ
    exact SizedStripChain.nil ⊥
  | succ k ih =>
    obtain ⟨hcν,hdν⟩ := dominates_stripRemove_last θ τ k hh hc hd
    have hs := ih (rowTruncate θ k) (stripRemove τ (θ.rowLen k))
      (rowTruncate_height θ k) hcν hdν
    have he : rowWeights (rowTruncate θ k) k = rowWeights θ k := by
      apply rowWeights_congr
      intro i hi
      rw [rowTruncate_rowLen, ite_eq_left hi]
    rw [he] at hs
    apply SizedStripChain.snoc hs (stripRemove_horizontal τ (θ.rowLen k))
    have hw : θ.rowLen k ≤ τ.rowLen 0 := by
      have hp := hd 1
      simp only [rowPrefix, Finset.sum_range_one] at hp
      exact (θ.rowLen_anti 0 k (Nat.zero_le _)).trans hp
    simpa only [min_eq_left hw] using stripRemove_card τ (θ.rowLen k)



lemma rowWeights_length (θ : YoungDiagram) (k : ℕ) : (rowWeights θ k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [rowWeights, List.length_append, List.length_singleton, ih]

lemma rowWeights_getElem (θ : YoungDiagram) (k j : ℕ) (hj : j < k) :
    (rowWeights θ k)[j]'(by rw [rowWeights_length]; exact hj) = θ.rowLen j := by
  induction k with
  | zero => omega
  | succ k ih =>
    change (rowWeights θ k ++ [θ.rowLen k])[j]'(by simpa only [List.length_append, List.length_singleton, rowWeights_length] using hj) = θ.rowLen j
    by_cases h : j < k
    · rw [List.getElem_append_left (by rwa [rowWeights_length]), ih h]
    · have he : j = k := by omega
      subst j
      rw [List.getElem_append_right (by rw [rowWeights_length])]
      simp only [rowWeights_length, Nat.sub_self, List.getElem_singleton]

lemma perm_of_equal_content {n d : ℕ} (a b : Fin n → Fin d)
    (h : ∀ j, (Finset.univ.filter (fun i => a i = j)).card =
      (Finset.univ.filter (fun i => b i = j)).card) :
    ∃ g : Equiv.Perm (Fin n), b ∘ g = a := by
  classical
  let e (j) : {i // a i = j} ≃ {i // b i = j} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_subtype] using h j)
  let g := (Equiv.sigmaFiberEquiv a).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv b))
  refine ⟨g, ?_⟩
  funext i
  exact (e (a i) ⟨i,rfl⟩).property

lemma vector_of_invariant_functional {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (l : Module.Dual ℂ (Specht t)) (hl : l ≠ 0)
    (he : ∀ g : Equiv.Perm (Fin n), a ∘ g = a → ∀ x, l (spechtRep t g x) = l x) :
    ∃ y : Specht t, y ≠ 0 ∧ ∀ g : Equiv.Perm (Fin n), a ∘ g = a → spechtRep t g y = y := by
  let e := spechtSelfDual t
  refine ⟨e.symm l, ?_, ?_⟩
  · intro hz
    exact hl (e.symm.injective (hz.trans (map_zero _).symm))
  · intro g hg
    have hi : a ∘ (g⁻¹ : Equiv.Perm (Fin n)) = a := by
      funext i
      have hh := congrFun hg (g⁻¹ i)
      simpa using hh.symm
    have hdual : (spechtRep t).dual g l = l := by
      apply LinearMap.ext
      intro x
      exact he g⁻¹ hi x
    have hh := LinearMap.congr_fun (e.symm.isIntertwining' g) l
    change e.symm ((spechtRep t).dual g l) = spechtRep t g (e.symm l) at hh
    rw [hdual] at hh
    exact hh.symm

/- Young's sufficiency in the exact form needed for the repeated-row quotient:
a dominant Specht has a nonzero invariant functional for a word of the
prescribed content. -/
theorem young_invariant_functional (θ τ : YoungDiagram)
    (hc : τ.card = θ.card) (hd : Dominates τ θ) :
    ∃ (a : Fin τ.card → Fin (θ.colLen 0)) (l : Module.Dual ℂ (Specht (shapeTableau τ))),
      l ≠ 0 ∧
      (∀ j, (Finset.univ.filter (fun i => a i = j)).card = θ.rowLen j) ∧
      (∀ g : Equiv.Perm (Fin τ.card), a ∘ g = a →
        ∀ x, l (spechtRep (shapeTableau τ) g x) = l x) := by
  classical
  let bs := rowWeights θ (θ.colLen 0)
  have hs := sizedStripChain_of_dominates θ τ (θ.colLen 0) le_rfl hc hd
  obtain ⟨c,F,hF,hcB,hzero,hcount,he⟩ := stripChain_restriction hs
  have hpos (i) : 0 < c i := by
    have hz := hzero i
    have hn : ¬ i ∈ Set.range (tableauInclusion (shapeTableau ⊥) (shapeTableau τ) hs.le) := by
      rintro ⟨j,hj⟩
      exact Fin.elim0 j
    have hc0 : c i ≠ 0 := fun h => hn (hz.mp h)
    omega
  have hbound (i) : c i ≤ θ.colLen 0 := by simpa only [rowWeights_length] using hcB i
  let a : Fin τ.card → Fin (θ.colLen 0) := fun i => ⟨c i-1, by have hh := hpos i; have ht := hbound i; omega⟩
  let v : Specht (shapeTableau ⊥) := ⟨polytabloid (shapeTableau ⊥), mem_cyclic _ _⟩
  let l₀ := spechtSelfDual (shapeTableau ⊥) v
  have hl₀ : l₀ ≠ 0 := by
    intro hz
    have hh := (spechtSelfDual (shapeTableau ⊥)).injective (hz.trans (map_zero _).symm)
    exact polytabloid_ne_zero _ (congrArg Subtype.val hh)
  let l := l₀.comp F
  have hl : l ≠ 0 := by
    intro hz
    apply hl₀
    apply LinearMap.ext
    intro y
    obtain ⟨x,rfl⟩ := hF y
    exact LinearMap.congr_fun hz x
  refine ⟨a,l,hl,?_,?_⟩
  · intro j
    have hj : j.val < (rowWeights θ (θ.colLen 0)).length := by rw [rowWeights_length]; exact j.isLt
    rw [← rowWeights_getElem θ (θ.colLen 0) j.val j.isLt, ← hcount j.val hj]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (⟨c i-1, _⟩ : Fin (θ.colLen 0)) = j ↔ c i = j.val+1
    rw [Fin.ext_iff]
    change c i-1 = j.val ↔ c i = j.val+1
    have hh := hpos i
    omega
  · intro g hg x
    have hcol (i) : c (g i) = c i := by
      have hh := congrArg Fin.val (congrFun hg i)
      change c (g i)-1 = c i-1 at hh
      have hp := hpos i
      have hpg := hpos (g i)
      omega
    have hh := he g 1 hcol (fun k => Fin.elim0 k) x
    change l₀ (F (spechtRep (shapeTableau τ) g x)) = l₀ (F x)
    rw [hh, map_one]
    rfl

end Saxl

end

end OAI
