import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.NoMixedColumns
import OAI.RepresentationTheory.UniversalSquare.Contraction.BandContractions

namespace OAI

/-! Band Gluing. -/

section

noncomputable section
namespace Saxl.FlagColumns

def columnsAway (K : ℕ) : List (ℕ × ℕ) → ℕ → Prop
  | [], _ => True
  | (a,b)::ps, o => (b ≠ 0 → 4 ≤ o ∧ o+a+4 ≤ K) ∧ columnsAway K ps (o+a)

lemma clearSlots_of_columnsAway {D K : ℕ} (P : Fin D → Prop)
    (ps : List (ℕ × ℕ)) (o : ℕ) (hs : columnsAway K ps o)
    (w : Fin (ps.map (fun p => p.1+p.2)).sum → Fin D)
    (hw : ∀ i : Fin (ps.map Prod.fst).sum, 4 ≤ o+i.val → o+i.val+4 < K →
      P (w ((splitPositions ps).symm (Sum.inl i)))) : clearSlots P ps w := by
  induction ps generalizing o with
  | nil => trivial
  | cons p ps ih =>
    obtain ⟨a,b⟩ := p
    constructor
    · intro hb i
      have hi := i.isLt
      have h₁ := (hs.1 hb).1
      have h₂ := (hs.1 hb).2
      have H := hw (Fin.castAdd (ps.map Prod.fst).sum i) (by simp only [Fin.val_castAdd]; omega)
        (by simp only [Fin.val_castAdd]; omega)
      erw [splitPositions_left_first] at H
      exact H
    · apply ih (o+a) hs.2 (rightWord finSumFinEquiv.symm w)
      intro i h₁ h₂
      have H := hw (Fin.natAdd a i) (by change 4 ≤ o+(a+i.val); omega)
        (by change o+(a+i.val)+4 < K; omega)
      erw [splitPositions_left_rest] at H
      exact H

end Saxl.FlagColumns
namespace Saxl

def joinedPositionEquiv {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) : Fin n ≃ Fin m :=
  e.trans ((p.sumCongr q).trans f.symm)

lemma joinedPositionEquiv_left {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin a) :
    joinedPositionEquiv e f p q (e.symm (Sum.inl i)) = f.symm (Sum.inl (p i)) := by
  simp [joinedPositionEquiv]

lemma joinedPositionEquiv_right {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin b) :
    joinedPositionEquiv e f p q (e.symm (Sum.inr i)) = f.symm (Sum.inr (q i)) := by
  simp [joinedPositionEquiv]

lemma relabelWord_positionProduct {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B)
    (v : WordSpace a D) (u : WordSpace b D) :
    relabelWord (joinedPositionEquiv e f p q) (positionProduct e v u) =
      positionProduct f (relabelWord p v) (relabelWord q u) := by
  ext w
  change v _ * u _ = v _ * u _
  congr 1
  · congr 1
    funext i
    exact congrArg w (joinedPositionEquiv_left e f p q i)
  · congr 1
    funext i
    exact congrArg w (joinedPositionEquiv_right e f p q i)

lemma joinedPositionEquiv_isLeft {n m a b A B : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (i : Fin n) :
    (f (joinedPositionEquiv e f p q i)).isLeft = (e i).isLeft := by
  simp only [joinedPositionEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  cases e i <;> rfl

lemma wordSector_joinedPositionEquiv {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (P : Fin D → Prop)
    (w : Fin m → Fin D) :
    wordSector (fun i => (e i).isLeft = true) P (w ∘ joinedPositionEquiv e f p q) ↔
      wordSector (fun i => (f i).isLeft = true) P w := by
  change (∀ i, P (w (joinedPositionEquiv e f p q i)) ↔ (e i).isLeft = true) ↔ _
  simp only [← joinedPositionEquiv_isLeft e f p q]
  exact ((joinedPositionEquiv e f p q).surjective.forall
    (p := fun i => P (w i) ↔ (f i).isLeft = true)).symm

lemma coordinateProjection_relabel_split {n m a b A B D : ℕ}
    (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin m ≃ Fin A ⊕ Fin B)
    (p : Fin a ≃ Fin A) (q : Fin b ≃ Fin B) (P : Fin D → Prop)
    (z : WordSpace n D) :
    coordinateProjection (wordSector (fun i => (f i).isLeft = true) P)
      (relabelWord (joinedPositionEquiv e f p q) z) =
    relabelWord (joinedPositionEquiv e f p q)
      (coordinateProjection (wordSector (fun i => (e i).isLeft = true) P) z) := by
  classical
  ext w
  simp only [relabelWord_apply, coordinateProjection_apply,
    wordSector_joinedPositionEquiv e f p q P w]

end Saxl

namespace UniversalTensorSquare
open Saxl Saxl.FlagColumns

theorem candidateBandWord_support_of_columns {n M b δ r d : ℕ}
    (hM : 4 ≤ M) (hδ : δ ≤ 1) (hr : r = 2*b+δ) (hd : d ≤ 4)
    (t : Tableau n (candidate M b δ)) (s₁ s₂ : Tableau r (ShortColumns.shape b δ))
    (ps : List (ℕ × ℕ)) (hp : (ps.map Prod.fst).sum = 2*M-1)
    (he : (ps.map Prod.snd).sum = 2*r)
    (ha : ∀ p ∈ ps, 1 ≤ p.1 ∧ p.1 ≤ d)
    (hb : ∀ p ∈ ps, p.2 ≠ 0 → p.1 = d) (hc : columnsAway (2*M-1) ps 0)
    (μ η : YoungDiagram) (hη : η.card = 2*r)
    (hηe : ∀ i, Even (η.colLen i)) (hηw : η.rowLen 0 ≤ 8)
    (Eμ : Columns.Cells (ps.map (fun p => p.1+p.2)) ≃ μ.cells)
    (Eμr : ∀ c, (Eμ c).val.1 = Columns.row c)
    (Eμc : ∀ c c', (Eμ c).val.2 = (Eμ c').val.2 ↔ Columns.col c = Columns.col c')
    (Eη : Columns.Cells (ps.map Prod.snd) ≃ η.cells)
    (Eηr : ∀ c, (Eη c).val.1 = Columns.row c)
    (Eηc : ∀ c c', (Eη c).val.2 = (Eη c').val.2 ↔ Columns.col c = Columns.col c')
    (s : Tableau (candidateBandSize t) μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep s)
      (cyclic (wordRep _ _) (candidateBandWord hM t)).toRepresentation, F ≠ 0 := by
  obtain ⟨N,hN,hNp⟩ := candidatePathWord_contraction hM hδ t s₁ s₂ (ps.map Prod.fst) (by
    intro a ha'
    obtain ⟨p,hp',rfl⟩ := List.mem_map.mp ha'
    exact ⟨(ha p hp').1,(ha p hp').2.trans hd⟩) hp
  obtain ⟨g,Q,hQ,hQp⟩ := candidateExtrasWord_contraction hM hδ hr s₁ s₂ η hη hηe hηw
    (ps.map Prod.snd) he Eη Eηr Eηc
  let e := candidateBandSplit hM t s₁ s₂
  let f := splitPositions ps
  let p := (finCongr hp).symm
  let q := (finCongr he).symm.trans g
  let E := joinedPositionEquiv e f p q
  let z := relabelWord E (candidateBandWord hM t)
  let v := relabelWord p (candidatePathWord hM t s₁ s₂)
  let u := relabelWord q (candidateExtrasWord hM s₁ s₂)
  let c := signC (candidateBandRowShuffle hM t).val * signC (candidateBandColShuffle hM t).val
  have hz : ∀ w, z w ≠ 0 → clearSlots (candidatePathAlphabet M b δ) ps w := by
    intro w hw
    apply clearSlots_of_columnsAway (candidatePathAlphabet M b δ) ps 0 hc w
    intro i h₁ h₂
    have H := candidateBandWord_path_clearance hM t (w ∘ E) hw
      (e.symm (Sum.inl (finCongr hp i))) (finCongr hp i)
      (candidateBandSplit_path hM t s₁ s₂ _) (by change 4 ≤ i.val; omega)
      (by change i.val+4 < 2*M-1; omega)
    change candidatePathAlphabet M b δ (w (E (e.symm (Sum.inl (finCongr hp i))))) at H
    dsimp only [E] at H
    rw [joinedPositionEquiv_left, show p (finCongr hp i) = i from
      (finCongr hp).symm_apply_apply i] at H
    exact H
  have hsep : coordinateProjection
      (wordSector (fun i => (f i).isLeft = true) (candidatePathAlphabet M b δ)) z =
      c • positionProduct f v u := by
    rw [coordinateProjection_relabel_split e f p q, candidateBandWord_separated hM hδ t s₁ s₂,
      map_smul, relabelWord_positionProduct]
  have hsign {k : ℕ} (g : Equiv.Perm (Fin k)) : signC g ≠ 0 := by
    have H := signC_mul_self g
    intro hz
    rw [hz,zero_mul] at H
    exact zero_ne_one H
  have hc' : c ≠ 0 := mul_ne_zero (hsign _) (hsign _)
  have Hpair := band_contraction_factor N Q (candidatePathAlphabet M b δ) ps
    (fun p hp => (ha p hp).2) hb hN hQ z hz v u c hsep
  have hnon : dotProduct (blocks (ps.map (fun p => p.1+p.2)) (joinedFlag d N Q)) z ≠ 0 := by
    rw [Hpair]
    exact mul_ne_zero hc' (mul_ne_zero hNp (by
      change dotProduct (blocks (ps.map Prod.snd) Q)
        (relabelWord ((finCongr he).symm.trans g) (candidateExtrasWord hM s₁ s₂)) ≠ 0
      rw [← relabelWord_trans]
      exact hQp))
  have hs := columns_sufficient Eμ Eμr Eμc ((Columns.enumerate _).trans Eμ) z
    (joinedFlag d N Q) hnon
  exact (cyclic_support_relabel_iff E s ((Columns.enumerate _).trans Eμ)
    (candidateBandWord hM t)).mp hs

end UniversalTensorSquare
end
end

end OAI
