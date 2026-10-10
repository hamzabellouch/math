import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Specht.DualPolytabloid

namespace OAI

/-! Common Basis. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem finite_polynomials_common_point {ι σ : Type*} [Fintype ι]
    (p : ι → MvPolynomial σ ℂ) (hp : ∀ i, p i ≠ 0)
    (q : MvPolynomial σ ℂ) (hq : q ≠ 0) :
    ∃ v : σ → ℂ, MvPolynomial.eval v q ≠ 0 ∧
      ∀ i, MvPolynomial.eval v (p i) ≠ 0 := by
  classical
  have hprod : q * ∏ i, p i ≠ 0 := mul_ne_zero hq
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have he : ∃ v : σ → ℂ, MvPolynomial.eval v (q * ∏ i, p i) ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hprod
    exact MvPolynomial.funext (fun v => by simpa only [map_zero] using hn v)
  obtain ⟨v,hv⟩ := he
  simp only [map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
    Finset.mem_univ, forall_const] at hv
  exact ⟨v,hv⟩

theorem wordMap_common_invertible {ι : Type*} [Fintype ι] (n : ι → ℕ) (d : ℕ)
    (x y : ∀ i, WordSpace (n i) d)
    (h : ∀ i, ∃ L : Fin d → Fin d → ℂ,
      dotProduct (wordMap L (x i)) (y i) ≠ 0) :
    ∃ L : Fin d → Fin d → ℂ, (Matrix.of L).det ≠ 0 ∧
      ∀ i, dotProduct (wordMap L (x i)) (y i) ≠ 0 := by
  have hp (i) : pairingPolynomial (x i) (y i) ≠ 0 := by
    obtain ⟨L,hL⟩ := h i
    intro hz
    apply hL
    rw [← pairingPolynomial_eval, hz, map_zero]
  obtain ⟨v,hv,hp⟩ := finite_polynomials_common_point
    (fun i => pairingPolynomial (x i) (y i)) hp
    (Matrix.mvPolynomialX (Fin d) (Fin d) ℂ).det
    (Matrix.det_mvPolynomialX_ne_zero (Fin d) ℂ)
  refine ⟨fun a b => v (a,b), ?_, ?_⟩
  · exact (Matrix.eval_det_mvPolynomialX (Fin d) ℂ v) ▸ hv
  · intro i
    exact (pairingPolynomial_eval (x i) (y i) (fun a b => v (a,b))) ▸ hp i

lemma wordMap_letterLift {n a b c : ℕ} (f : Fin a → Fin b)
    (L : Fin b → Fin c → ℂ) (x : WordSpace n a) :
    wordMap L (letterLift f x) = wordMap (fun i j => L (f i) j) x := by
  classical
  have h : (wordMap L).comp (letterLift f) = wordMap (fun i j => L (f i) j) (n := n) := by
    apply Representation.IntertwiningMap.ext
    apply LinearMap.pi_ext
    intro w c
    have he : (Pi.single w c : WordSpace n a) = c • Pi.single w 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [he, map_smul, map_smul]
    congr 1
    change wordMap L (letterLift f (Pi.single w 1)) = wordMap _ (Pi.single w 1)
    rw [letterLift_single]
    ext v
    simp only [wordMap_single, Function.comp_apply]
  exact congrArg (fun F => F x) h

def extendAlphabetMap {a b : ℕ} (_h : a ≤ b) (L : Fin a → Fin b → ℂ) :
    (Fin b → Fin b → ℂ) := fun i j => if hi : i.val < a then L ⟨i.val,hi⟩ j else 0

lemma extendAlphabetMap_apply {a b : ℕ} (h : a ≤ b)
    (L : Fin a → Fin b → ℂ) (i : Fin a) (j : Fin b) :
    extendAlphabetMap h L (Fin.castLE h i) j = L i j := by
  simp [extendAlphabetMap, i.isLt]

theorem dual_polytabloid_necessary_basis {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d) (hμ : μ.colLen 0 ≤ d)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin d → Fin d → ℂ), (Matrix.of L).det ≠ 0 ∧
      dotProduct (wordMap L (letterLift (Fin.castLE hμ)
        (wordRep n (μ.colLen 0) g (polytabloid t)))) u ≠ 0 := by
  obtain ⟨g,L,hL⟩ := dual_polytabloid_necessary t u f hf
  let x := letterLift (Fin.castLE hμ) (wordRep n (μ.colLen 0) g (polytabloid t))
  have hex : ∃ M : Fin d → Fin d → ℂ, dotProduct (wordMap M x) u ≠ 0 := by
    refine ⟨extendAlphabetMap hμ L, ?_⟩
    simpa only [x, wordMap_letterLift, extendAlphabetMap_apply] using hL
  obtain ⟨M,hM,hm⟩ := wordMap_common_invertible (ι := Unit) (fun _ => n) d
    (fun _ => x) (fun _ => u) (fun _ => hex)
  exact ⟨g,M,hM,hm ()⟩

theorem dual_polytabloid_basis_iff {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d) (hμ : μ.colLen 0 ≤ d) :
    (∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) ↔
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin d → Fin d → ℂ), (Matrix.of L).det ≠ 0 ∧
      dotProduct (wordMap L (letterLift (Fin.castLE hμ)
        (wordRep n (μ.colLen 0) g (polytabloid t)))) u ≠ 0 := by
  constructor
  · rintro ⟨f,hf⟩
    exact dual_polytabloid_necessary_basis t u hμ f hf
  · rintro ⟨g,L,_,h⟩
    rw [wordMap_letterLift] at h
    exact (dual_polytabloid_iff t u).mpr ⟨g,_,h⟩

end Saxl
end
end

end OAI
