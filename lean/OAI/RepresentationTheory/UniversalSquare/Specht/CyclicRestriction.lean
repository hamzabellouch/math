import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.AttachmentTransfer
import OAI.RepresentationTheory.UniversalSquare.Specht.DualPolytabloid

namespace OAI

/-! Cyclic Restriction. -/

section

noncomputable section
namespace Saxl

theorem intertwining_reverse_nonzero {G X Y : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (F : Representation.IntertwiningMap ρ σ) (hF : F ≠ 0) :
    ∃ T : Representation.IntertwiningMap σ ρ, T ≠ 0 := by
  obtain ⟨S,hS⟩ := subrepresentation_embeds_of_le_range F F.range le_rfl
  obtain ⟨T,hT⟩ := intertwining_extend_injective (subrepInclusion F.range)
    Subtype.val_injective S
  refine ⟨T, ?_⟩
  intro h0
  apply hF
  ext x
  have he := congrArg (fun H : Representation.IntertwiningMap F.range.toRepresentation ρ =>
    H ⟨F x, x, rfl⟩) hT
  change T (F x) = S ⟨F x, x, rfl⟩ at he
  rw [h0] at he
  have hh : S ⟨F x, x, rfl⟩ = S 0 := by simpa using he.symm
  exact congrArg Subtype.val (hS hh)

def intertwiningRestrict {G H X Y : Type*} [Group G] [Group H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    (φ : H →* G) (F : Representation.IntertwiningMap ρ σ) :
    Representation.IntertwiningMap (ρ.comp φ) (σ.comp φ) where
  toLinearMap := F.toLinearMap
  isIntertwining' h := F.isIntertwining' (φ h)

theorem cyclic_restriction_support {G H X Y Z : Type*}
    [Group G] [Finite G] [Group H] [Finite H]
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup Z] [Module ℂ Z]
    (ρ : Representation ℂ G X) [ρ.IsIrreducible]
    (σ : Representation ℂ H Y) (τ : Representation ℂ G Z)
    (φ : H →* G) (u : Z)
    (T : Representation.IntertwiningMap σ (τ.comp φ)) (hu : u ∈ T.range)
    (F : Representation.IntertwiningMap ρ (cyclic τ u).toRepresentation)
    (hF : F ≠ 0) :
    ∃ Q : Representation.IntertwiningMap (ρ.comp φ) σ, Q ≠ 0 := by
  let E := (subrepInclusion (cyclic τ u)).comp F
  have hEi : Function.Injective E := Subtype.val_injective.comp
    ((Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hF)
  obtain ⟨R,hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id ρ)
  have hRu : R u ≠ 0 := by
    intro h0
    apply hF
    ext x
    have hm := intertwiner_cyclic_mem R u (E x) (F x).property
    rw [h0, cyclic_zero_mem_iff] at hm
    have he := congrArg (fun f : Representation.IntertwiningMap ρ ρ => f x) hR
    change R (E x) = x at he
    rw [he] at hm
    rw [hm, map_zero]
    rfl
  let P := (intertwiningRestrict φ R).comp T
  have hP : P ≠ 0 := by
    obtain ⟨v,hv⟩ := hu
    change T v = u at hv
    intro h0
    apply hRu
    have he := congrArg (fun f : Representation.IntertwiningMap σ (ρ.comp φ) => f v) h0
    change R (T v) = 0 at he
    rwa [hv] at he
  exact intertwining_reverse_nonzero P hP

end Saxl
end
end

end OAI
