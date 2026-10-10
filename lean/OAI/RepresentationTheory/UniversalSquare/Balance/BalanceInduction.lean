import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceProjection
import OAI.RepresentationTheory.UniversalSquare.Support.Neighboring
import OAI.RepresentationTheory.UniversalSquare.Balance.PackingSupport

namespace OAI

/-! Balance Induction. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl.Balance

theorem balance_support_of_surjective {n d : ℕ} {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) X)
    (W : Subrepresentation (wordRep n d))
    (c : Fin n → ℕ) (A : Fin d → Prop) (label : Fin d → ℕ)
    (z : Fin d → ℤ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → z a < z b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n d)
    (hm : ∀ y, L y ∈ W) (hs : ∀ y, FixedComponentSums c z σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n d).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (f : Representation.IntertwiningMap
      (ρ.comp ((fiberGroup c).subtype.comp φ)) τ) (hf : f ≠ 0) :
    ∃ F : Representation.IntertwiningMap ρ W.toRepresentation, F ≠ 0 := by
  let K := L.comp f.toLinearMap
  have hK : (coordinateProjection (componentWords c A label)).comp K ≠ 0 := by
    intro h0
    apply hf
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    apply hT
    change T (f x) = T 0
    rw [map_zero, ← he]
    exact LinearMap.congr_fun h0 x
  apply balance_support_transfer ρ W c A label z σ ho K
    (fun x => hm (f x)) (fun x => hs (f x)) hK
  intro g hg x
  obtain ⟨a,ha⟩ := hφ ⟨g,hg⟩
  have hval : (φ a).val = g := congrArg Subtype.val ha
  change coordinateProjection (componentWords c A label) (L (f (ρ g x))) =
    wordRep n d g (coordinateProjection (componentWords c A label) (L (f x)))
  rw [he,he,← hval]
  exact LinearMap.congr_fun ((T.comp f).isIntertwining' a) x

theorem kronecker_pos_of_packing {n : ℕ} {G Y : Type*}
    [Group G] [Finite G] [AddCommGroup Y] [Module ℂ Y]
    {lam μ : YoungDiagram} (a : Tableau n lam) (t : Tableau n μ)
    (c : Fin n → ℕ)
    (A : Fin (lam.colLen 0 * lam.colLen 0) → Prop)
    (label : Fin (lam.colLen 0 * lam.colLen 0) → ℕ) (σ : ℕ → ℤ)
    (ho : ∀ a b, A a → A b → label a < label b → output a < output b)
    (φ : G →* fiberGroup c) (hφ : Function.Surjective φ)
    (τ : Representation ℂ G Y)
    (L : Y →ₗ[ℂ] WordSpace n (lam.colLen 0 * lam.colLen 0))
    (hm : ∀ y, L y ∈ (spechtTensorMap a a).range)
    (hs : ∀ y, FixedComponentSums c (fun a => (output a : ℤ)) σ (L y))
    (T : Representation.IntertwiningMap τ
      ((wordRep n (lam.colLen 0 * lam.colLen 0)).comp ((fiberGroup c).subtype.comp φ)))
    (hT : Function.Injective T)
    (he : ∀ y, coordinateProjection (componentWords c A label) (L y) = T y)
    (θ : YoungDiagram) (hc : μ.card = θ.card) (hd : Dominates μ θ)
    (w : Fin n → Fin (θ.colLen 0)) (e : Equiv.Perm (Fin (θ.colLen 0)))
    (hw : ∀ j, (Finset.univ.filter (fun i => w i = e j)).card = θ.rowLen j)
    (hpack : SupportLE (cyclic (wordRep n (θ.colLen 0)) (Pi.single w 1)).toRepresentation
      (Representation.coind ((fiberGroup c).subtype.comp φ) τ)) :
    0 < kronecker a a t := by
  obtain ⟨F,hF⟩ := young_cyclic_support θ μ t hc hd w e hw
  obtain ⟨Q,hQ⟩ := hpack.detects_map F hF
  obtain ⟨R,hR⟩ := balance_support_of_surjective (spechtRep t)
    (spechtTensorMap a a).range c A label (fun a => (output a : ℤ)) σ
    (fun a b ha hb hab => by exact_mod_cast ho a b ha hb hab)
    φ hφ τ L hm hs T hT he
    (coindEval ((fiberGroup c).subtype.comp φ) Q)
    (coindEval_ne_zero ((fiberGroup c).subtype.comp φ) Q hQ)
  let : AddCommGroup (Specht a ⊗[ℂ] Specht a) := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨i,hi⟩ := subrepresentation_embeds_of_le_range (spechtTensorMap a a)
    (spechtTensorMap a a).range le_rfl
  exact (kronecker_pos_iff a a t).mpr
    ⟨i.comp R,intertwining_comp_ne_zero i hi R hR⟩

end Saxl.Balance
end
end

end OAI
