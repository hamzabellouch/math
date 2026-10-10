import OAI.RepresentationTheory.Saxl.StripExtension

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl

inductive SizedStripChain : List ℕ → YoungDiagram → YoungDiagram → Prop
  | nil (μ) : SizedStripChain [] μ μ
  | snoc {bs ν η μ b} : SizedStripChain bs ν η → HorizontalStrip η μ →
      η.card + b = μ.card → SizedStripChain (bs ++ [b]) ν μ

lemma SizedStripChain.le {bs ν μ} (hs : SizedStripChain bs ν μ) : ν ≤ μ := by
  induction hs with
  | nil => exact le_rfl
  | snoc hs hh hc ih => exact ih.trans hh.1

abbrev shapeTableau (μ : YoungDiagram) : Tableau μ.card μ := canonicalTableau μ rfl

lemma tableauInclusion_self {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : Fin n) :
    tableauInclusion t t le_rfl k = k := by
  change t.symm (t k) = k
  exact t.symm_apply_apply k

/- Iterated positive Pieri, with an explicit coloring of the added strips.
The map is surjective and equivariant for all permutations preserving each
strip, not just for the smaller symmetric group. -/
theorem stripChain_restriction {bs ν μ} (hs : SizedStripChain bs ν μ) :
    ∃ (c : Fin μ.card → ℕ) (F : Specht (shapeTableau μ) →ₗ[ℂ] Specht (shapeTableau ν)),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin μ.card)) (h : Equiv.Perm (Fin ν.card)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le k) =
          tableauInclusion (shapeTableau ν) (shapeTableau μ) hs.le (h k)) →
        ∀ x, F (spechtRep (shapeTableau μ) g x) = spechtRep (shapeTableau ν) h (F x)) := by
  classical
  induction hs with
  | nil ν =>
    refine ⟨fun _ => 0, LinearMap.id, Function.surjective_id, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _; exact ⟨i,tableauInclusion_self _ i⟩
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      have hh : g = h := by
        apply Equiv.ext
        intro k
        simpa only [tableauInclusion_self] using he k
      subst h
      rfl
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) (shapeTableau μ) hh
    let i := tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans (shapeTableau ν) (shapeTableau η) (shapeTableau μ) hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le l) =
          tableauInclusion (shapeTableau ν) (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _) =
          tableauInclusion (shapeTableau η) (shapeTableau μ) hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep (shapeTableau μ) g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl



theorem stripChain_restriction_any {bs ν μ} (hs : SizedStripChain bs ν μ)
    {a n : ℕ} (s : Tableau a ν) (t : Tableau n μ) :
    ∃ (c : Fin n → ℕ) (F : Specht t →ₗ[ℂ] Specht s),
      Function.Surjective F ∧
      (∀ i, c i ≤ bs.length) ∧
      (∀ i, c i = 0 ↔ i ∈ Set.range (tableauInclusion s t hs.le)) ∧
      (∀ j (hj : j < bs.length), (Finset.univ.filter (fun i => c i = j+1)).card = bs[j]) ∧
      (∀ (g : Equiv.Perm (Fin n)) (h : Equiv.Perm (Fin a)),
        (∀ i, c (g i) = c i) →
        (∀ k, g (tableauInclusion s t hs.le k) =
          tableauInclusion s t hs.le (h k)) →
        ∀ x, F (spechtRep t g x) = spechtRep s h (F x)) := by
  classical
  induction hs generalizing a n with
  | nil ν =>
    obtain ⟨F,hF,hFe⟩ := pieri_strip_surjective s t
      (show HorizontalStrip ν ν from ⟨le_rfl, by intros x hx hn; exact False.elim (hn hx)⟩)
    refine ⟨fun _ => 0, F, hF, by simp, ?_, ?_, ?_⟩
    · intro i
      constructor
      · intro _
        refine ⟨s.symm (t i), ?_⟩
        change t.symm ⟨(s (s.symm (t i))).val, _⟩ = i
        simp only [Equiv.apply_symm_apply]
        exact t.symm_apply_apply i
      · intro _; rfl
    · intro j hj; simp at hj
    · intro g h hc he x
      exact hFe g h he x
  | @snoc bs ν η μ b hs hh hcard ih =>
    obtain ⟨c,F,hF,hc,hzero,hcount,he⟩ := ih s (shapeTableau η)
    obtain ⟨P,hP,hPe⟩ := pieri_strip_surjective (shapeTableau η) t hh
    let i := tableauInclusion (shapeTableau η) t hh.1
    let c' := extendColor i c (bs.length+1)
    refine ⟨c', F.comp P, hF.comp hP, ?_, ?_, ?_, ?_⟩
    · intro k
      simpa only [List.length_append, List.length_singleton] using extendColor_le i c bs.length hc k
    · intro k
      constructor
      · intro hk
        change extendColor i c (bs.length+1) k = 0 at hk
        have hr : k ∈ Set.range i := (extendColor_mem i c bs.length hc k).mp (by omega)
        obtain ⟨l,rfl⟩ := hr
        have hl : c l = 0 := (extendColor_apply i c _ l).symm.trans hk
        obtain ⟨j,hj⟩ := (hzero l).mp hl
        refine ⟨j, ?_⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        exact congrArg i hj
      · rintro ⟨j,rfl⟩
        rw [← tableauInclusion_trans s (shapeTableau η) t hs.le hh.1]
        change extendColor i c _ (i _) = 0
        rw [extendColor_apply]
        exact (hzero _).mpr ⟨j,rfl⟩
    · intro j hj
      have hjle : j ≤ bs.length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      rcases lt_or_eq_of_le hjle with hjlt | rfl
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = j+1)).card = _
        rw [extendColor_count_old i c (bs.length+1) (j+1) (by omega), hcount j hjlt,
          List.getElem_append_left hjlt]
      · change (Finset.univ.filter (fun x => extendColor i c (bs.length+1) x = bs.length+1)).card = _
        rw [extendColor_count_new i c bs.length hc]
        simp only [List.getElem_append_right le_rfl, Nat.sub_self, List.getElem_singleton]
        have ht : n = μ.card := by
          have := Fintype.card_congr t
          simpa only [Fintype.card_fin, Fintype.card_coe] using this
        omega
    · intro g h hg hgi x
      have hgmem : ∀ k, g k ∈ Set.range i ↔ k ∈ Set.range i := by
        intro k
        rw [← extendColor_mem i c bs.length hc, ← extendColor_mem i c bs.length hc]
        exact (congrArg (fun c => c ≤ bs.length) (hg k)).to_iff
      let k := restrictPerm i g hgmem
      have hik (l) : i (k l) = g (i l) := restrictPerm_apply i g hgmem l
      have hkcolor (l) : c (k l) = c l := by
        rw [← extendColor_apply i c (bs.length+1) (k l), hik, ← extendColor_apply i c (bs.length+1) l]
        exact hg (i l)
      have hkbase (l) : k (tableauInclusion s (shapeTableau η) hs.le l) =
          tableauInclusion s (shapeTableau η) hs.le (h l) := by
        apply i.injective
        rw [hik]
        change g (tableauInclusion (shapeTableau η) t hh.1 _) =
          tableauInclusion (shapeTableau η) t hh.1 _
        rw [tableauInclusion_trans, tableauInclusion_trans]
        exact hgi l
      change F (P (spechtRep t g x)) = _
      rw [hPe g k (fun l => (hik l).symm), he k h hkcolor hkbase]
      rfl

end Saxl

end

end OAI
