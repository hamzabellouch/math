import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Word Relabel. -/

section

noncomputable section
namespace Saxl
open scoped TensorProduct

def relabelWord {n m d : ℕ} (e : Fin n ≃ Fin m) : WordSpace n d ≃ₗ[ℂ] WordSpace m d where
  toFun v := fun w => v (w ∘ e)
  invFun v := fun w => v (w ∘ e.symm)
  left_inv v := by ext w; simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
  right_inv v := by ext w; simp only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma relabelWord_apply {n m d : ℕ} (e : Fin n ≃ Fin m)
    (v : WordSpace n d) (w : Fin m → Fin d) : relabelWord e v w = v (w ∘ e) := rfl

lemma altWord_relabel {n m d : ℕ} {α : Type*} (e : Fin n ≃ Fin m)
    (c : Fin n → α) (a : Fin n → Fin d) :
    relabelWord e (altWord (fiberGroup c) a) =
      altWord (fiberGroup (c ∘ e.symm)) (a ∘ e.symm) := by
  ext w
  exact altWord_fiber_relabel e.symm c a w

lemma relabelWord_letterLift {n m d D : ℕ} (e : Fin n ≃ Fin m) (f : Fin d → Fin D)
    (v : WordSpace n d) : relabelWord e (letterLift f v) = letterLift f (relabelWord e v) := by
  have hnm : n = m := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  subst m
  exact (Representation.IntertwiningMap.isIntertwining _ _ (letterLift f) e v).symm

def pairLetterMap {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d) :
    Fin (a*b) → Fin (c*d) := fun x => finProdFinEquiv (f (finProdFinEquiv.symm x).1,
      g (finProdFinEquiv.symm x).2)

lemma pairLetterMap_injective {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (pairLetterMap f g) :=
  finProdFinEquiv.injective.comp ((hf.prodMap hg).comp finProdFinEquiv.symm.injective)

lemma letterLift_wordTensor {n a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d)
    (x : WordSpace n a) (y : WordSpace n b) :
    letterLift (pairLetterMap f g) (wordTensor n a b (x ⊗ₜ[ℂ] y)) =
      wordTensor n c d (letterLift f x ⊗ₜ[ℂ] letterLift g y) := by
  classical
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n → Fin a)).sum_repr x,
    ← (Pi.basisFun ℂ (Fin n → Fin b)).sum_repr y]
  conv_rhs => rw [← (Pi.basisFun ℂ (Fin n → Fin a)).sum_repr x,
    ← (Pi.basisFun ℂ (Fin n → Fin b)).sum_repr y]
  simp only [TensorProduct.sum_tmul, TensorProduct.tmul_sum, map_sum, map_smul,
    TensorProduct.smul_tmul, TensorProduct.tmul_smul, Pi.basisFun_apply,
    wordTensor_single, letterLift_single]
  have hm (p : Fin n → Fin a) (q : Fin n → Fin b) :
      pairLetterMap f g ∘ mergeWords p q = mergeWords (f ∘ p) (g ∘ q) := by
    funext i
    simp only [Function.comp_apply, pairLetterMap, mergeWords, Equiv.symm_apply_apply]
  simp only [hm]

lemma wordTensor_positionProduct {n k l a b : ℕ} (e : Fin n ≃ Fin k ⊕ Fin l)
    (x : WordSpace k a) (y : WordSpace l a) (v : WordSpace k b) (w : WordSpace l b) :
    wordTensor n a b (positionProduct e x y ⊗ₜ[ℂ] positionProduct e v w) =
      positionProduct e (wordTensor k a b (x ⊗ₜ[ℂ] v))
        (wordTensor l a b (y ⊗ₜ[ℂ] w)) := by
  ext z
  simp only [wordTensor_tmul, positionProduct]
  change (x (splitLeft (leftWord e z)) * y (splitLeft (rightWord e z))) *
    (v (splitRight (leftWord e z)) * w (splitRight (rightWord e z))) = _
  ring

lemma relabelWord_wordTensor {n m a b : ℕ} (e : Fin n ≃ Fin m)
    (x : WordSpace n a) (y : WordSpace n b) :
    relabelWord e (wordTensor n a b (x ⊗ₜ[ℂ] y)) =
      wordTensor m a b (relabelWord e x ⊗ₜ[ℂ] relabelWord e y) := by
  ext z
  rfl

lemma coordinateProjection_wordTensor {n a b : ℕ}
    (P : (Fin n → Fin a) → Prop) (Q : (Fin n → Fin b) → Prop)
    (x : WordSpace n a) (y : WordSpace n b) :
    coordinateProjection (fun w => P (splitLeft w) ∧ Q (splitRight w))
        (wordTensor n a b (x ⊗ₜ[ℂ] y)) =
      wordTensor n a b (coordinateProjection P x ⊗ₜ[ℂ] coordinateProjection Q y) := by
  classical
  ext w
  simp only [coordinateProjection_apply, wordTensor_tmul]
  by_cases hp : P (splitLeft w) <;> by_cases hq : Q (splitRight w) <;> simp [hp,hq]

end Saxl
end
end

end OAI
