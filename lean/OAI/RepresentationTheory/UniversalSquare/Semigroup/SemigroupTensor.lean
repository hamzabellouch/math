import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.ContractionNecessary

namespace OAI

/-! Semigroup Tensor. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma wordMap_lifts_pair {n a b A B : ℕ} (f : Fin a → Fin A) (g : Fin b → Fin B)
    (L : Fin A → Fin B → ℂ) (x : WordSpace n a) (y : WordSpace n b) :
    dotProduct (wordMap L (letterLift f x)) (letterLift g y) =
      dotProduct (wordMap (fun i j => L (f i) (g j)) x) y := by
  rw [wordMap_letterLift,wordMap_pair_transpose,dotProduct_comm,
    wordMap_letterLift,wordMap_pair_transpose,dotProduct_comm]

lemma wordMap_lifts_nonzero {n a b A B : ℕ} (f : Fin a → Fin A) (g : Fin b → Fin B)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (x : WordSpace n a) (y : WordSpace n b)
    (h : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L x) y ≠ 0) :
    ∃ L : Fin A → Fin B → ℂ,
      dotProduct (wordMap L (letterLift f x)) (letterLift g y) ≠ 0 := by
  classical
  obtain ⟨L,hL⟩ := h
  refine ⟨Function.extend f (fun i => Function.extend g (L i) 0) 0, ?_⟩
  simpa only [wordMap_lifts_pair,hf.extend_apply,hg.extend_apply] using hL

lemma wordMap_common_two {n m a b : ℕ}
    (x : WordSpace n a) (y : WordSpace n b) (z : WordSpace m a) (w : WordSpace m b)
    (h : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L x) y ≠ 0)
    (h' : ∃ L : Fin a → Fin b → ℂ, dotProduct (wordMap L z) w ≠ 0) :
    ∃ L : Fin a → Fin b → ℂ,
      dotProduct (wordMap L x) y ≠ 0 ∧ dotProduct (wordMap L z) w ≠ 0 := by
  classical
  have hp : pairingPolynomial x y ≠ 0 := by
    obtain ⟨L,hL⟩ := h
    intro hz
    apply hL
    rw [←pairingPolynomial_eval,hz,map_zero]
  have hq : pairingPolynomial z w ≠ 0 := by
    obtain ⟨L,hL⟩ := h'
    intro hz
    apply hL
    rw [←pairingPolynomial_eval,hz,map_zero]
  obtain ⟨v,hv,hv'⟩ := finite_polynomials_common_point (ι := Unit)
    (fun _ => pairingPolynomial z w) (fun _ => hq) (pairingPolynomial x y) hp
  exact ⟨fun a b => v (a,b),
    (pairingPolynomial_eval x y (fun a b => v (a,b))) ▸ hv,
    (pairingPolynomial_eval z w (fun a b => v (a,b))) ▸ hv' ()⟩

lemma relabelWord_polytabloid {n m : ℕ} {μ : YoungDiagram}
    (e : Fin n ≃ Fin m) (t : Tableau n μ) :
    relabelWord e (polytabloid t) = polytabloid (e.symm.trans t) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  exact (polytabloid_action t e).symm

namespace FlagColumns
open Columns

def standardTableau (rs : List ℕ) : Tableau rs.sum (columnShape rs) :=
  (standard_exists_tableau rs).choose

lemma standardTableau_spec (rs : List ℕ) :
    blocks rs (standard ((columnShape rs).colLen 0)) = polytabloid (standardTableau rs) :=
  (standard_exists_tableau rs).choose_spec

def positioned {n d : ℕ} (rs : List ℕ) (e : Fin n ≃ Fin rs.sum)
    (N : ℕ → Fin d → ℂ) : WordSpace n d := relabelWord e.symm (blocks rs N)

lemma positioned_standard {n D : ℕ} (rs : List ℕ) (e : Fin n ≃ Fin rs.sum)
    (hD : (columnShape rs).colLen 0 ≤ D) :
    positioned rs e (standard D) =
      letterLift (Fin.castLE hD) (polytabloid (e.trans (standardTableau rs))) := by
  unfold positioned
  rw [←standard_lift rs le_rfl hD,standardTableau_spec,relabelWord_letterLift,
    relabelWord_polytabloid,Equiv.symm_symm]

lemma tableau_positioned {n D : ℕ} (rs : List ℕ) (t : Tableau n (columnShape rs))
    (hD : (columnShape rs).colLen 0 ≤ D) :
    ∃ e : Fin n ≃ Fin rs.sum,
      positioned rs e (standard D) = letterLift (Fin.castLE hD) (polytabloid t) := by
  refine ⟨t.trans (standardTableau rs).symm,?_⟩
  rw [positioned_standard rs _ hD]
  have he : (t.trans (standardTableau rs).symm).trans (standardTableau rs) = t := by
    apply Equiv.ext
    intro i
    simp
  rw [he]

lemma positioned_append {n m d : ℕ} (rs ss : List ℕ)
    (e : Fin n ≃ Fin rs.sum) (f : Fin m ≃ Fin ss.sum) (N : ℕ → Fin d → ℂ) :
    ∃ g : Fin (n+m) ≃ Fin (rs++ss).sum,
      positioned (rs++ss) g N = positionProduct finSumFinEquiv.symm
        (positioned rs e N) (positioned ss f N) := by
  let g : Fin (n+m) ≃ Fin (rs++ss).sum :=
    finSumFinEquiv.symm.trans ((e.sumCongr f).trans (appendPositions rs ss).symm)
  refine ⟨g,?_⟩
  unfold positioned
  rw [blocks_append]
  funext w
  have hl : leftWord (appendPositions rs ss) (w ∘ g.symm) =
      (leftWord finSumFinEquiv.symm w) ∘ e.symm := by
    funext i
    simp [leftWord,g]
  have hr : rightWord (appendPositions rs ss) (w ∘ g.symm) =
      (rightWord finSumFinEquiv.symm w) ∘ f.symm := by
    funext i
    simp [rightWord,g]
  change blocks rs N _ * blocks ss N _ = _
  rw [hl,hr]
  rfl

lemma kronecker_pos_of_positioned {n D : ℕ} {rs ss ts : List ℕ}
    (a : Tableau n (columnShape rs)) (b : Tableau n (columnShape ss))
    (t : Tableau n (columnShape ts))
    (ea : Fin n ≃ Fin rs.sum) (eb : Fin n ≃ Fin ss.sum) (et : Fin n ≃ Fin ts.sum)
    (ha : (columnShape rs).colLen 0 ≤ D) (hb : (columnShape ss).colLen 0 ≤ D)
    (ht : (columnShape ts).colLen 0 ≤ D) (L : Fin D → Fin (D*D) → ℂ)
    (h : dotProduct (wordMap L (positioned ts et (standard D)))
      (wordTensor _ _ _ (positioned rs ea (standard D) ⊗ₜ[ℂ]
        positioned ss eb (standard D))) ≠ 0) : 0 < kronecker a b t := by
  rw [positioned_standard _ _ ha,positioned_standard _ _ hb,positioned_standard _ _ ht,
    ←letterLift_wordTensor,wordMap_lifts_pair] at h
  exact kronecker_pos_of_contraction a _ b _ t _ _ h

lemma nonzero_positioned_of_kronecker_pos {n D : ℕ} {rs ss ts : List ℕ}
    (a : Tableau n (columnShape rs)) (b : Tableau n (columnShape ss))
    (t : Tableau n (columnShape ts))
    (ha : (columnShape rs).colLen 0 ≤ D) (hb : (columnShape ss).colLen 0 ≤ D)
    (ht : (columnShape ts).colLen 0 ≤ D) (h : 0 < kronecker a b t) :
    ∃ (ea : Fin n ≃ Fin rs.sum) (eb : Fin n ≃ Fin ss.sum) (et : Fin n ≃ Fin ts.sum)
      (L : Fin D → Fin (D*D) → ℂ),
      dotProduct (wordMap L (positioned ts et (standard D)))
        (wordTensor _ _ _ (positioned rs ea (standard D) ⊗ₜ[ℂ]
          positioned ss eb (standard D))) ≠ 0 := by
  obtain ⟨a',b',t',L,hL⟩ := kronecker_contraction_necessary a b t h
  obtain ⟨ea,hea⟩ := tableau_positioned rs a' ha
  obtain ⟨eb,heb⟩ := tableau_positioned ss b' hb
  obtain ⟨et,het⟩ := tableau_positioned ts t' ht
  obtain ⟨M,hM⟩ := wordMap_lifts_nonzero (Fin.castLE ht)
    (pairLetterMap (Fin.castLE ha) (Fin.castLE hb)) (Fin.castLE_injective _)
    (pairLetterMap_injective _ _ (Fin.castLE_injective _) (Fin.castLE_injective _))
    _ _ ⟨L,hL⟩
  refine ⟨ea,eb,et,M,?_⟩
  rwa [hea,heb,het,←letterLift_wordTensor]

end FlagColumns
end Saxl
end
end

end OAI
