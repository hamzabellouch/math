import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Band.CommonPath
import OAI.RepresentationTheory.UniversalSquare.Band.BandPath
import OAI.RepresentationTheory.UniversalSquare.Band.BandExtras
import OAI.RepresentationTheory.UniversalSquare.Contraction.FlagDetection

namespace OAI

/-! Band Contractions. -/

section

noncomputable section
namespace Saxl

lemma relabelWord_trans {n m k d : ℕ} (e : Fin n ≃ Fin m) (f : Fin m ≃ Fin k)
    (v : WordSpace n d) : relabelWord f (relabelWord e v) = relabelWord (e.trans f) v := rfl

lemma positionProduct_alphabet {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (P : Fin d → Prop) (v : WordSpace a d) (u : WordSpace b d)
    (hv : v ∈ alphabetSub a d P) (hu : u ∈ alphabetSub b d P) :
    positionProduct e v u ∈ alphabetSub n d P := by
  intro w hw
  obtain ⟨i,hi⟩ := hw
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hv _ ⟨j,hi⟩, zero_mul]
  | inr j =>
    change v (leftWord e w) * u (rightWord e w) = 0
    rw [hu _ ⟨j,hi⟩, mul_zero]

end Saxl
namespace Saxl.FlagColumns

lemma blocks_comp {a b : ℕ} (rs : List ℕ) (N : ℕ → Fin b → ℂ)
    (φ : Fin a → Fin b) (w : Fin rs.sum → Fin a) :
    blocks rs N (φ ∘ w) = blocks rs (fun i x => N i (φ x)) w := by
  simp only [blocks, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, pure, Function.comp_apply]

lemma blocks_lift_relabel_pair {n a b : ℕ} (rs : List ℕ)
    (e : Fin rs.sum ≃ Fin n) (φ : Fin a → Fin b)
    (N : ℕ → Fin b → ℂ) (B : ℕ → Fin a → ℂ)
    (hN : ∀ i x, N i (φ x) = B i x) (v : WordSpace n a) :
    dotProduct (blocks rs N) (relabelWord e.symm (letterLift φ v)) =
      dotProduct (fun w => blocks rs B (w ∘ e)) v := by
  rw [relabelWord_symm_pair e.symm, Equiv.symm_symm,
    dotProduct_comm, letterLift_pair, dotProduct_comm]
  congr 1
  funext w
  change blocks rs N (φ ∘ (w ∘ e)) = _
  rw [blocks_comp, show (fun i x => N i (φ x)) = B from funext (fun i => funext (hN i))]

end Saxl.FlagColumns
namespace UniversalTensorSquare
open Saxl
open Saxl.FlagColumns

lemma bandPairSmallLetter_range {M b δ : ℕ} (hM : 4 ≤ M) (a) :
    candidatePathAlphabet M b δ a ↔ ∃ x, bandPairSmallLetter hM x = a := by
  constructor
  · intro ha
    refine ⟨finProdFinEquiv (⟨(finProdFinEquiv.symm a).1.val,ha.1⟩,
      ⟨(finProdFinEquiv.symm a).2.val,ha.2⟩), ?_⟩
    apply finProdFinEquiv.symm.injective
    simp only [bandPairSmallLetter, pairLetterMap, Equiv.symm_apply_apply,
      bandSmallRowLetter, bandSmallColLetter, bandSmallLetter]
    exact Prod.ext (Fin.ext rfl) (Fin.ext rfl)
  · rintro ⟨x,rfl⟩
    simp only [candidatePathAlphabet, bandPairSmallLetter, pairLetterMap,
      Equiv.symm_apply_apply, bandSmallRowLetter, bandSmallColLetter,
      bandSmallLetter, Fin.val_castLE]
    exact ⟨(finProdFinEquiv.symm x : Fin 2 × Fin 2).1.isLt,
      (finProdFinEquiv.symm x : Fin 2 × Fin 2).2.isLt⟩

theorem candidatePathWord_contraction {n M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (rs : List ℕ) (hrs : ∀ a ∈ rs, 1 ≤ a ∧ a ≤ 4) (hn : rs.sum = 2*M-1) :
    ∃ N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ,
      (∀ i a, ¬candidatePathAlphabet M b δ a → N i a = 0) ∧
      dotProduct (blocks rs N)
        (relabelWord (finCongr hn).symm (candidatePathWord hM t s₁ s₂)) ≠ 0 := by
  classical
  obtain ⟨B,hB⟩ := Band.odd_path_common_basis
  let C : ℕ → Fin 4 → ℂ := fun i a => Band.extendFourBasis B i
    (Path.parts a).1 (Path.parts a).2
  let N : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ :=
    fun i => Function.extend (bandPairSmallLetter hM) (C i) 0
  have hN : ∀ i a, N i (bandPairSmallLetter hM a) = C i a := fun i a =>
    (bandPairSmallLetter_injective hM).extend_apply (C i) 0 a
  refine ⟨N,?_,?_⟩
  · intro i a ha
    exact Function.extend_apply' (f := bandPairSmallLetter hM) (C i) (fun _ => 0) a ((bandPairSmallLetter_range hM a).not.mp ha)
  · rw [candidatePathWord_eq hM hδ, map_smul, dotProduct_smul, smul_eq_mul]
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    rw [relabelWord_letterLift, relabelWord_trans, ← relabelWord_letterLift]
    let e : Fin rs.sum ≃ Fin (2*(M-1)+1) := (finCongr hn).trans (candidatePathEquiv hM).symm
    change dotProduct (blocks rs N) (relabelWord e.symm (letterLift (bandPairSmallLetter hM)
      (Path.bandWord (M-1)))) ≠ 0
    rw [blocks_lift_relabel_pair rs e (bandPairSmallLetter hM) N C hN]
    have hraw : rs.sum = 2*(M-1)+1 := by omega
    convert hB (M-1) rs hrs hraw using 1
    congr 1

lemma bandSWLetter_high {M b δ : ℕ} (hM : 4 ≤ M) (x) :
    2 ≤ ((finProdFinEquiv.symm (@bandSWLetter M b δ hM x)).2).val := by
  simpa only [bandSWLetter, pairLetterMap, Equiv.symm_apply_apply, bandLongColLetter]
    using bandExtraLetter_high hM _ (finProdFinEquiv.symm x).2

lemma candidateExtrasWord_alphabet {M b δ r : ℕ} (hM : 4 ≤ M)
    (s₁ s₂ : Tableau r (ShortColumns.shape b δ)) :
    candidateExtrasWord hM s₁ s₂ ∈ alphabetSub (2*r) _
      (fun a => ¬candidatePathAlphabet M b δ a) := by
  rw [candidateExtrasWord_eq]
  apply positionProduct_alphabet
  · apply letterLift_mem_alphabet
    intro a ha
    exact Nat.not_lt.mpr (bandNELetter_high hM a) ha.1
  · apply letterLift_mem_alphabet
    intro a ha
    exact Nat.not_lt.mpr (bandSWLetter_high hM a) ha.2

theorem candidateExtrasWord_contraction {M b δ r : ℕ} (hM : 4 ≤ M) (hδ : δ ≤ 1)
    (hr : r = 2*b+δ) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (η : YoungDiagram) (hη : η.card = 2*r)
    (he : ∀ i, Even (η.colLen i)) (hd : η.rowLen 0 ≤ 8)
    (rs : List ℕ) (hn : rs.sum = 2*r) (e : Columns.Cells rs ≃ η.cells)
    (er : ∀ c, (e c).val.1 = Columns.row c)
    (ec : ∀ c c', (e c).val.2 = (e c').val.2 ↔ Columns.col c = Columns.col c') :
    ∃ (g : Equiv.Perm (Fin rs.sum))
      (Q : ℕ → Fin ((candidate M b δ).transpose.colLen 0 * (candidate M b δ).colLen 0) → ℂ),
      (∀ i a, candidatePathAlphabet M b δ a → Q i a = 0) ∧
      dotProduct (blocks rs Q) (relabelWord g
        (relabelWord (finCongr hn).symm (candidateExtrasWord hM s₁ s₂))) ≠ 0 := by
  let u := canonicalTableau η hη
  have hs := candidateExtrasWord_support hM hδ hr s₁ s₂ η hη u he hd
  let v : Tableau rs.sum η := (Columns.enumerate rs).trans e
  have hs' := (cyclic_support_relabel_iff (finCongr hn).symm u v
    (candidateExtrasWord hM s₁ s₂)).mpr hs
  obtain ⟨g,Q,hQ,hp⟩ := columns_necessary e er ec v _
    (fun a => ¬candidatePathAlphabet M b δ a)
    (relabelWord_alphabet _ _ _ (candidateExtrasWord_alphabet hM s₁ s₂)) hs'
  exact ⟨g,Q,fun i a ha => hQ i a (not_not_intro ha),hp⟩

end UniversalTensorSquare
end
end

end OAI
