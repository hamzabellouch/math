import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.LocallyFinite
import OAI.Topology.CoarseAssembly.CirclePairing
import Mathlib.Topology.Algebra.Support

namespace OAI

/-! # Restricting analytic K-homology to a compact open component

Extension by zero is constructed on the actual continuous-function
algebras. Its contravariant action on Fredholm modules is a left inverse
to pushforward of the component inclusion. No additivity theorem is
needed for this restriction calculation.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open Topology
open scoped ZeroAtInfty

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space Y]

theorem continuous_zeroExtension (e : X ↪ Y) (he : IsOpenEmbedding e)
    (f : C₀(X, ℂ)) : Continuous (Function.extend e f 0) := by
  have hs := HasCompactSupport.of_compactSpace (f : X → ℂ)
  apply continuous_of_tsupport
  intro y hy
  obtain ⟨x, _, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous hy
  rw [← he.continuousAt_iff, Function.extend_comp e.injective]
  exact f.continuous.continuousAt

@[simp] theorem zeroExtension_apply (e : X ↪ Y) (he : IsOpenEmbedding e)
    (f : C₀(X, ℂ)) (x : X) : zeroExtension e he f (e x) = f x :=
  e.injective.extend_apply _ _ x

theorem zeroExtension_apply_outside (e : X ↪ Y) (he : IsOpenEmbedding e)
    (f : C₀(X, ℂ)) {y : Y} (hy : y ∉ Set.range e) : zeroExtension e he f y = 0 :=
  Function.extend_apply' _ _ _ hy

def compactOpenInclusion (e : X ↪ Y) (he : IsOpenEmbedding e) : CocompactMap X Y :=
  compactMap ⟨e, he.continuous⟩

def restrictComponent (e : X ↪ Y) (he : IsOpenEmbedding e) :
    LocallyFiniteK1 Y →+ LocallyFiniteK1 X := precomp (zeroExtensionHom e he)

theorem restrictComponent_pushforward (e : X ↪ Y) (he : IsOpenEmbedding e) :
    (restrictComponent e he).comp (pushforward (compactOpenInclusion e he)) =
      AddMonoidHom.id (LocallyFiniteK1 X) := by
  have h : (pullback (compactOpenInclusion e he)).comp (zeroExtensionHom e he) =
      NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
    ext f x
    exact zeroExtension_apply e he f x
  change (precomp (zeroExtensionHom e he)).comp
    (precomp (pullback (compactOpenInclusion e he))) = _
  rw [← precomp_comp, h, precomp_id]

end CoarseAssembly.Analytic

end

end OAI
