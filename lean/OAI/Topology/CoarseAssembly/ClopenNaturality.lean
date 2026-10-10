import OAI.Topology.CoarseAssembly.ClopenRestriction

namespace OAI

/-! # Restriction across a proper map

If the preimage of a compact open component is exactly the specified
compact open component of the source, the corresponding KK restrictions
commute with pushforward. The identity is proved on functions first.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {A B X Y : Type} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace A] [CompactSpace B] [T2Space X] [T2Space Y]

theorem pullback_zeroExtension (e : A ↪ X) (he : IsOpenEmbedding e)
    (d : B ↪ Y) (hd : IsOpenEmbedding d) (f : CocompactMap X Y) (g : CocompactMap A B)
    (commutes : ∀ a, f (e a) = d (g a))
    (preimage : ∀ x, f x ∈ Set.range d ↔ x ∈ Set.range e) :
    (pullback f).comp (zeroExtensionHom d hd) =
      (zeroExtensionHom e he).comp (pullback g) := by
  ext h x
  change zeroExtension d hd h (f x) = zeroExtension e he (pullback g h) x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨a, rfl⟩ := hx
    rw [commutes, zeroExtension_apply, zeroExtension_apply]
    rfl
  · have hfx : f x ∉ Set.range d := fun h => hx ((preimage x).mp h)
    rw [zeroExtension_apply_outside d hd h hfx, zeroExtension_apply_outside e he _ hx]

/-- This is the coordinate restriction identity used by the changing
finite-component index test. It is derived from the geometric preimage
identity, without invoking or assuming a global detection theorem. -/
theorem restrictComponent_natural (e : A ↪ X) (he : IsOpenEmbedding e)
    (d : B ↪ Y) (hd : IsOpenEmbedding d) (f : CocompactMap X Y) (g : CocompactMap A B)
    (commutes : ∀ a, f (e a) = d (g a))
    (preimage : ∀ x, f x ∈ Set.range d ↔ x ∈ Set.range e) :
    (restrictComponent d hd).comp (pushforward f) =
      (pushforward g).comp (restrictComponent e he) := by
  change (precomp (zeroExtensionHom d hd)).comp (precomp (pullback f)) =
    (precomp (pullback g)).comp (precomp (zeroExtensionHom e he))
  rw [← precomp_comp, ← precomp_comp, pullback_zeroExtension e he d hd f g commutes preimage]

end CoarseAssembly.Analytic

end

end OAI
