import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Polynomial Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def jointContent {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e) :
    (Fin d × Fin e) →₀ ℕ := ∑ i, Finsupp.single (a i, b i) 1

lemma jointContent_apply {n d e : ℕ} (a : Fin n → Fin d) (b : Fin n → Fin e)
    (j : Fin d × Fin e) : jointContent a b j =
      (Finset.univ.filter (fun i => (a i, b i) = j)).card := by
  classical
  simp [jointContent, Finsupp.single_apply, eq_comm]

lemma perm_of_equal_jointContent {n d e : ℕ}
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    ∃ g : Equiv.Perm (Fin n), a' ∘ g = a ∧ b' ∘ g = b := by
  classical
  have hc : ∀ j : Fin (d*e),
      (Finset.univ.filter (fun i => finProdFinEquiv (a i,b i) = j)).card =
      (Finset.univ.filter (fun i => finProdFinEquiv (a' i,b' i) = j)).card := by
    intro j
    have hh := DFunLike.congr_fun h (finProdFinEquiv.symm j)
    simp only [jointContent_apply] at hh
    simpa only [← Equiv.eq_symm_apply] using hh
  obtain ⟨g, hg⟩ := perm_of_equal_content
    (fun i => finProdFinEquiv (a i, b i))
    (fun i => finProdFinEquiv (a' i, b' i)) hc
  refine ⟨g, ?_, ?_⟩
  · funext i
    exact congrArg Prod.fst (finProdFinEquiv.injective (congrFun hg i))
  · funext i
    exact congrArg Prod.snd (finProdFinEquiv.injective (congrFun hg i))

lemma intertwiner_jointContent {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a a' : Fin n → Fin d) (b b' : Fin n → Fin e)
    (h : jointContent a b = jointContent a' b') :
    F (Pi.single a 1) b = F (Pi.single a' 1) b' := by
  classical
  obtain ⟨g, ha, hb⟩ := perm_of_equal_jointContent a a' b b' h
  have hs : wordRep n d g (Pi.single a 1) = Pi.single a' 1 := by
    ext w
    change (Pi.single a 1 : WordSpace n d) (w ∘ g) = (Pi.single a' 1 : WordSpace n d) w
    simp only [Pi.single_apply]
    have he : (w ∘ g = a) ↔ w = a' := by
      rw [← ha]
      exact ⟨fun h => funext (fun i => by
        have hh := congrFun h (g⁻¹ i)
        simpa using hh),
        fun h => by rw [h]⟩
    simp only [he]
  have hh := congrFun (LinearMap.congr_fun (F.isIntertwining' g) (Pi.single a 1)) b'
  simp only [LinearMap.comp_apply] at hh
  rw [hs] at hh
  change F (Pi.single a' 1) b' = F (Pi.single a 1) (b' ∘ g) at hh
  rw [hb] at hh
  exact hh.symm

def pairingPolynomial {n d e : ℕ} (x : WordSpace n d) (y : WordSpace n e) :
    MvPolynomial (Fin d × Fin e) ℂ :=
  ∑ a, ∑ b, MvPolynomial.monomial (jointContent a b) (x a * y b)

lemma eval_jointContent_monomial {n d e : ℕ}
    (a : Fin n → Fin d) (b : Fin n → Fin e)
    (c : ℂ) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2)
      (MvPolynomial.monomial (jointContent a b) c) =
      c * ∏ i, L (a i) (b i) := by
  classical
  rw [jointContent, MvPolynomial.monomial_sum_index]
  simp only [map_mul, MvPolynomial.eval_C, map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  change MvPolynomial.eval _ (MvPolynomial.X (a i, b i)) = _
  exact MvPolynomial.eval_X _

lemma pairingPolynomial_eval {n d e : ℕ}
    (x : WordSpace n d) (y : WordSpace n e) (L : Fin d → Fin e → ℂ) :
    MvPolynomial.eval (fun j => L j.1 j.2) (pairingPolynomial x y) =
      dotProduct (wordMap L x) y := by
  classical
  simp only [pairingPolynomial, map_sum, eval_jointContent_monomial]
  change (∑ a, ∑ b, x a * y b * ∏ i, L (a i) (b i)) =
    ∑ b, (∑ a, x a * ∏ i, L (a i) (b i)) * y b
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

def jointContentWeight {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (m : (Fin d × Fin e) →₀ ℕ) : ℂ :=
  if h : ∃ a b, jointContent a b = m then
    F (Pi.single h.choose 1) h.choose_spec.choose else 0

lemma jointContentWeight_apply {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (a : Fin n → Fin d) (b : Fin n → Fin e) :
    jointContentWeight F (jointContent a b) = F (Pi.single a 1) b := by
  classical
  unfold jointContentWeight
  have hab : ∃ a' b', jointContent a' b' = jointContent a b := ⟨a,b,rfl⟩
  rw [dite_eq_left hab]
  exact intertwiner_jointContent F _ a _ b hab.choose_spec.choose_spec

lemma pairingPolynomial_zero_pair {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e) (h : pairingPolynomial x y = 0) :
    dotProduct (F x) y = 0 := by
  classical
  let w : MvPolynomial (Fin d × Fin e) ℂ →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (jointContentWeight F)).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap
  have he := congrArg w h
  have hw (m : (Fin d × Fin e) →₀ ℕ) (c : ℂ) :
      w (MvPolynomial.monomial m c) = c * jointContentWeight F m := by
    change Finsupp.linearCombination ℂ (jointContentWeight F) (Finsupp.single m c) = _
    simp
  have he' : (∑ a, ∑ b, (x a * y b) * F (Pi.single a 1) b) = 0 := by
    simpa only [pairingPolynomial, map_sum, map_zero, hw, jointContentWeight_apply] using he
  have hx : x = ∑ a, x a • Pi.single a 1 := by
    ext a
    simp [Pi.single_apply]
  rw [hx, map_sum]
  simp only [map_smul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  convert he' using 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem wordMap_detects_intertwiner {n d e : ℕ}
    (F : Representation.IntertwiningMap (wordRep n d) (wordRep n e))
    (x : WordSpace n d) (y : WordSpace n e)
    (h : dotProduct (F x) y ≠ 0) :
    ∃ L : Fin d → Fin e → ℂ, dotProduct (wordMap L x) y ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  apply pairingPolynomial_zero_pair F
  apply MvPolynomial.funext
  intro L
  simpa only [map_zero, pairingPolynomial_eval] using
    (pairingPolynomial_eval x y (fun a b => L (a,b))).trans (hn _)

end Saxl
end
end

end OAI
