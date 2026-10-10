import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.AttachmentTransfer

namespace OAI

/-! Pair Swap. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def tensorCommIntertwiner {G X Y : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ G X) (σ : Representation ℂ G Y) :
    (ρ.tprod σ).Equiv (σ.tprod ρ) where
  __ := TensorProduct.comm ℂ X Y
  isIntertwining' g := by
    ext x y
    rfl

def pairFlip (n d e : ℕ) : (wordRep n (d*e)).Equiv (wordRep n (e*d)) :=
  (wordTensorEquiv n d e).symm.trans
    ((tensorCommIntertwiner (wordRep n d) (wordRep n e)).trans (wordTensorEquiv n e d))

lemma pairFlip_tensor (n d e : ℕ) (x : WordSpace n d) (y : WordSpace n e) :
    pairFlip n d e (wordTensor n d e (x ⊗ₜ[ℂ] y)) =
      wordTensor n e d (y ⊗ₜ[ℂ] x) := by
  change wordTensor n e d (TensorProduct.comm ℂ _ _
    ((wordTensor n d e).symm (wordTensor n d e (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl

def pairWordMap {n a b c d : ℕ}
    (F : Representation.IntertwiningMap (wordRep n a) (wordRep n b))
    (G : Representation.IntertwiningMap (wordRep n c) (wordRep n d)) :
    Representation.IntertwiningMap (wordRep n (a*c)) (wordRep n (b*d)) :=
  (wordTensorEquiv n b d).toIntertwiningMap.comp
    ((F.tensor G).comp (wordTensorEquiv n a c).symm.toIntertwiningMap)

lemma pairWordMap_tensor {n a b c d : ℕ}
    (F : Representation.IntertwiningMap (wordRep n a) (wordRep n b))
    (G : Representation.IntertwiningMap (wordRep n c) (wordRep n d))
    (x : WordSpace n a) (y : WordSpace n c) :
    pairWordMap F G (wordTensor n a c (x ⊗ₜ[ℂ] y)) =
      wordTensor n b d (F x ⊗ₜ[ℂ] G y) := by
  change wordTensor n b d (TensorProduct.map F.toLinearMap G.toLinearMap
    ((wordTensor n a c).symm (wordTensor n a c (x ⊗ₜ[ℂ] y)))) = _
  rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul]
  rfl

lemma pairWordMap_injective {n a b c d : ℕ}
    (F : Representation.IntertwiningMap (wordRep n a) (wordRep n b))
    (G : Representation.IntertwiningMap (wordRep n c) (wordRep n d))
    (hF : Function.Injective F) (hG : Function.Injective G) :
    Function.Injective (pairWordMap F G) :=
  (wordTensor n b d).injective.comp
    ((TensorProduct.map_injective_of_flat_flat _ _ hF hG).comp
      (wordTensor n a c).symm.injective)

lemma polytabloid_doubleTranspose {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose μ)))
      (polytabloid (transposeTableau (transposeTableau t))) = polytabloid t := by
  rw [polytabloid_eq_altWord, letterLift_altWord, polytabloid_eq_altWord]
  rfl

def rowColumnTransposeMap {n : ℕ} {μ : YoungDiagram} (_tableau : Tableau n μ) :
    Representation.IntertwiningMap
      (wordRep n (μ.transpose.transpose.colLen 0 * μ.transpose.colLen 0))
      (wordRep n (μ.transpose.colLen 0 * μ.colLen 0)) :=
  (pairFlip n _ _).toIntertwiningMap.comp
    (pairWordMap (letterLift (Fin.cast (congrArg (fun ν : YoungDiagram => ν.colLen 0)
      (YoungDiagram.transpose_transpose μ)))) (Representation.IntertwiningMap.id _))

lemma rowColumnTransposeMap_word {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    rowColumnTransposeMap t (rowColumnWord (transposeTableau t)) = rowColumnWord t := by
  unfold rowColumnTransposeMap rowColumnWord
  change pairFlip n _ _ (pairWordMap _ _ (wordTensor _ _ _ (_ ⊗ₜ[ℂ] _))) = _
  rw [pairWordMap_tensor, polytabloid_doubleTranspose, pairFlip_tensor]
  rfl

lemma rowColumnTransposeMap_injective {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    Function.Injective (rowColumnTransposeMap t) := by
  apply (pairFlip n _ _).injective.comp
  apply pairWordMap_injective
  · exact letterLift_injective _ (Fin.cast_injective _)
  · exact Function.injective_id

theorem cyclic_support_map {G X Y Z : Type*} [Group G]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y} {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Injective F) (v : X)
    (f : Representation.IntertwiningMap τ (cyclic ρ v).toRepresentation) (hf : f ≠ 0) :
    ∃ g : Representation.IntertwiningMap τ (cyclic σ (F v)).toRepresentation, g ≠ 0 := by
  refine ⟨(cyclicMap F v).comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  apply hF
  have hh := congrArg (fun H => (H x).val) hz
  exact hh.trans (map_zero F).symm

end Saxl
end
end

end OAI
