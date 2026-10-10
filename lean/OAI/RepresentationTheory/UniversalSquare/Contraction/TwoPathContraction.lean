import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.WordPacking

namespace OAI

/-! Two Path Contraction. -/

section

noncomputable section
namespace Saxl.Columns

lemma dualBlockWord_singleton (r : ℕ) (N : ℕ → Band.Mat) :
    dualBlockWord [r] N = columnWedge r N := by
  classical
  unfold dualBlockWord columnWedge
  change (∑ π : Equiv.Perm (Fin r) × Unit, sg (rs := [r]) π •
    Path.pureWord (fun q => N (row (perm (rs := [r]) π (enumerate [r] q))))) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, sg, mul_one]
  apply Finset.sum_congr rfl
  intro π hπ
  congr 2
  funext j
  change N (row (perm (rs := [r]) (π, ()) (enumerate [r] (Fin.castAdd 0 j)))) = _
  erw [enumerate_left r [] j]
  rfl

lemma dotProduct_cast {m n d : ℕ} (hn : m = n)
    (x : WordSpace m d) (y : WordSpace n d) :
    dotProduct (fun w => x (w ∘ Fin.cast hn)) y =
      dotProduct x (fun w => y (w ∘ Fin.cast hn.symm)) := by
  subst n
  rfl

lemma columnWedge_path_nonzero (r : ℕ) (hr : 2*r+1 ≤ 4) :
    dotProduct (columnWedge (2*r+1) (fun i => Band.conjugation (Band.basis i)))
      (Path.bandWord r) ≠ 0 := by
  have h := odd_path_ordered_contraction r [2*r+1] (by
    intro a ha
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨by omega, hr⟩)
    (by simp)
  rw [dualBlockWord_singleton] at h
  exact h

theorem two_path_contraction (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) :
    dotProduct (dualBlockWord ((2*p+1)::rs)
        (fun i => Band.conjugation (Band.basis i)))
      (positionProduct finSumFinEquiv.symm (Path.bandWord p)
        (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm))) ≠ 0 := by
  rw [dualBlockWord_cons]
  erw [positionProduct_pair]
  apply mul_ne_zero (columnWedge_path_nonzero p hp)
  erw [← dotProduct_cast hr]
  exact odd_path_ordered_contraction r rs hrs hr

theorem two_path_cyclic_support (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
    (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
    (t : Tableau ((2*p+1)+rs.sum) μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep ((2*p+1)+rs.sum) 4)
        (positionProduct finSumFinEquiv.symm (Path.bandWord p)
          (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm)))).toRepresentation,
      F ≠ 0 := by
  obtain ⟨e, he, he'⟩ := place_columns μ hc
  let s : Tableau ((2*p+1)+rs.sum) μ := (enumerate ((2*p+1)::rs)).trans e
  apply specht_to_cyclic_of_vector_pair t
    ⟨polytabloid s, polytabloid_mem_all t s⟩
    (fun i a => Band.conjugation (Band.basis i.val) (Path.parts a).1 (Path.parts a).2)
  change dotProduct (wordMap _ (polytabloid ((enumerate _).trans e))) _ ≠ 0
  erw [mapped_placed_columns e he he' (fun i => Band.conjugation (Band.basis i))]
  exact two_path_contraction p r rs hp hrs hr

lemma positionProduct_move {n a b d : ℕ} (e f : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) :
    positionProduct f x y = wordRep n d (e.trans f.symm) (positionProduct e x y) := by
  funext w
  change x (leftWord f w) * y (rightWord f w) =
    x (leftWord e (w ∘ (e.trans f.symm))) * y (rightWord e (w ∘ (e.trans f.symm)))
  congr 1 <;> apply congrArg
  · funext i
    simp [leftWord]
  · funext i
    simp [rightWord]

theorem two_path_cyclic_support_placed {n : ℕ} (p r : ℕ) (rs : List ℕ)
    (hp : 2*p+1 ≤ 4) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4)
    (hr : rs.sum = 2*r+1) (μ : YoungDiagram)
    (hc : ((2*p+1)::rs).Perm μ.transpose.rowLens)
    (t : Tableau n μ) (e : Fin n ≃ Fin (2*p+1) ⊕ Fin (2*r+1)) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n 4)
        (positionProduct e (Path.bandWord p) (Path.bandWord r))).toRepresentation,
      F ≠ 0 := by
  let d : Fin n ≃ Fin (2*p+1) ⊕ Fin rs.sum :=
    e.trans ((Equiv.refl _).sumCongr (finCongr hr.symm))
  have hd : n = (2*p+1)+rs.sum := by
    simpa only [Fintype.card_fin, Fintype.card_sum] using Fintype.card_congr d
  subst n
  have heq : positionProduct e (Path.bandWord p) (Path.bandWord r) =
      positionProduct d (Path.bandWord p)
        (fun w => Path.bandWord r (w ∘ Fin.cast hr.symm)) := by
    funext w
    change Path.bandWord p (leftWord e w) * Path.bandWord r (rightWord e w) =
      Path.bandWord p (leftWord d w) *
        Path.bandWord r (rightWord d w ∘ Fin.cast hr.symm)
    rfl
  rw [heq, positionProduct_move finSumFinEquiv.symm d, cyclic_action_eq]
  exact two_path_cyclic_support p r rs hp hrs hr μ hc t

theorem odd_column_split (q : ℕ) (μ : YoungDiagram)
    (hn : μ.card = 2*q+2) (hμ : μ.colLen 0 ≤ 4)
    (ho : ∃ j, μ.colLen j % 2 = 1) :
    ∃ p rs, p ≤ q ∧ 2*p+1 ≤ 4 ∧
      (∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) ∧ rs.sum = 2*(q-p)+1 ∧
      ((2*p+1)::rs).Perm μ.transpose.rowLens := by
  classical
  obtain ⟨j,hj⟩ := ho
  have hp : 0 < μ.colLen j := by omega
  have hjlt : j < μ.transpose.colLen 0 := by
    rw [YoungDiagram.colLen_transpose]
    exact YoungDiagram.mem_iff_lt_rowLen.mp (YoungDiagram.mem_iff_lt_colLen.mpr hp)
  have hmem : μ.colLen j ∈ μ.transpose.rowLens := by
    have hjl : j < μ.transpose.rowLens.length := by simpa using hjlt
    have he := List.getElem_mem hjl
    simpa only [YoungDiagram.get_rowLens, YoungDiagram.rowLen_transpose] using he
  let rs := μ.transpose.rowLens.erase (μ.colLen j)
  have hperm : ((μ.colLen j)::rs).Perm μ.transpose.rowLens :=
    (List.perm_cons_erase hmem).symm
  have hs : μ.colLen j + rs.sum = 2*q+2 := by
    have h := hperm.sum_eq
    rw [List.sum_cons, ← card_eq_sum_rowLens, transpose_card, hn] at h
    exact h
  have hu := (μ.colLen_anti 0 j (Nat.zero_le _)).trans hμ
  refine ⟨(μ.colLen j)/2, rs, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro a ha
    have ha' := List.mem_of_mem_erase ha
    exact Path.fourRow_column_lengths μ hμ a ha'
  · omega
  · have he : 2*(μ.colLen j/2)+1 = μ.colLen j := by omega
    simpa only [he] using hperm

end Saxl.Columns
end
end

end OAI
