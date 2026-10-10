import Mathlib
import OAI.RepresentationTheory.Saxl.Main

namespace OAI

/-! Square Detection. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def spechtTensorMap {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) :
    Representation.IntertwiningMap ((spechtRep a).tprod (spechtRep b))
      (wordRep n (α.colLen 0 * β.colLen 0)) :=
  (wordTensorIntertwiner _ _ _).comp ((spechtInclusion a).tensor (spechtInclusion b))

lemma spechtTensorMap_injective {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) : Function.Injective (spechtTensorMap a b) := by
  apply (wordTensor _ _ _).injective.comp
  exact TensorProduct.map_injective_of_flat_flat _ _
    (spechtSub a).toSubmodule.subtype_injective (spechtSub b).toSubmodule.subtype_injective

lemma polytabloidTensor_real {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) :
    star (wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b)) =
      wordTensor _ _ _ (polytabloid a ⊗ₜ[ℂ] polytabloid b) := by
  funext w
  simp only [Pi.star_apply, wordTensor_tmul, star_mul]
  have h₁ := congrFun (polytabloid_real a) (splitLeft w)
  have h₂ := congrFun (polytabloid_real b) (splitRight w)
  change star (polytabloid b (splitRight w)) * star (polytabloid a (splitLeft w)) = _
  rw [show star (polytabloid a (splitLeft w)) = _ from h₁,
    show star (polytabloid b (splitRight w)) = _ from h₂]
  exact mul_comm _ _

lemma polytabloidTensor_cyclic_le_range {n : ℕ} {α β : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) :
    cyclic (wordRep n (α.colLen 0 * β.colLen 0))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≤
        (spechtTensorMap a b).range := by
  apply (cyclic_le _ _ _).mpr
  exact ⟨(⟨polytabloid a', polytabloid_mem_all a a'⟩ : Specht a) ⊗ₜ[ℂ]
    (⟨polytabloid b', polytabloid_mem_all b b'⟩ : Specht b), rfl⟩

attribute [irreducible] spechtTensorMap

theorem kronecker_pos_of_contraction {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t s : Tableau n μ)
    (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ)
    (h : dotProduct (wordMap L (polytabloid s))
      (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0) :
    0 < kronecker a b t := by
  let z := wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')
  let S := cyclic (wordRep n (α.colLen 0 * β.colLen 0)) z
  obtain ⟨f, hf⟩ := hom_to_cyclic_of_pair L (spechtSub t)
    ⟨polytabloid s, polytabloid_mem_all t s⟩ z (polytabloidTensor_real a' b') h
  let F := @intertwiningLiftSubrep (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  have hF : Function.Injective F := @intertwiningLiftSubrep_injective (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  apply (kronecker_pos_iff a b t).mpr
  refine ⟨F.comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have hzero := congrArg (fun H => H x) hz
  change F (f x) = 0 at hzero
  change F (f x) = F 0
  simpa only [map_zero] using hzero

end Saxl
end
end

end OAI
