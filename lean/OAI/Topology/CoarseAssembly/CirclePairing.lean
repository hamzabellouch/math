import OAI.Topology.CoarseAssembly.LoopCircle
import OAI.Topology.CoarseAssembly.LocallyFinite
import OAI.Topology.CoarseAssembly.FiniteRips
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

namespace OAI

/-! # The precise published circle-index input

Only the scalar-unitary index pairing, its naturality for a parametrized
loop, and the classical winding formula are assumed. The domain groups
are the Fredholm-module groups.

References: Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998),
Proposition 18.7.1 and Corollary 18.10.3; Khalkhali, *Basic Noncommutative
Geometry* (2009), Example 4.2.4, with the sign convention of manuscript §2.3.
-/

noncomputable section

namespace CoarseAssembly

open Analytic unitInterval

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Continuous maps from a compact source are cocompact. -/
def compactMap [CompactSpace X] (f : C(X, Y)) : CocompactMap X Y where
  toContinuousMap := f
  cocompact_tendsto' := by simp only [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot

@[simp] theorem compactMap_apply [CompactSpace X] (f : C(X, Y)) (x : X) :
    compactMap f x = f x := rfl

/-- The scalar unitary represented by a circle-valued map. -/
def circleUnitary (f : C(X, WindingCircle)) : C(X, Circle) :=
  ⟨fun x => AddCircle.toCircle (f x), AddCircle.continuous_toCircle.comp f.continuous⟩

/-- Minimal published analytic data needed to test loops. Each `pairing f`
is the index pairing with the scalar unitary `circleUnitary f`. -/
structure PublishedCircleInput where
  fundamental : LocallyFiniteK1 WindingCircle
  pairing : ∀ {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y],
    C(Y, WindingCircle) → (LocallyFiniteK1 Y →+ ℤ)
  loop_naturality : ∀ {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : C(Y, WindingCircle)) (γ : C(WindingCircle, Y)),
    pairing f (pushforward (compactMap γ) fundamental) = pairing (f.comp γ) fundamental
  winding : ∀ (g : C(WindingCircle, WindingCircle)) (n : ℤ)
    (L : Path (0 : ℝ) (n : ℝ)),
    (∀ t : unitInterval, g (t : ℝ) = (L t : WindingCircle)) →
      pairing g fundamental = n

/-- The constructed real lift is sufficient for the published index formula. -/
theorem PublishedCircleInput.loop_pairing (input : PublishedCircleInput)
    [CompactSpace Y] [T2Space Y] {y : Y}
    (f : C(Y, WindingCircle)) (γ : Path y y) (n : ℤ)
    (L : IntegerPathLift f γ n) :
    input.pairing f (pushforward (compactMap (loopCircle γ)) input.fundamental) = n := by
  rw [input.loop_naturality]
  apply input.winding _ n L.path
  intro t
  exact loopCircle_integerLift γ L t

/-- In particular the normalized circle class has infinite order; this
deduction is not part of the assumed published data. -/
theorem PublishedCircleInput.fundamental_infinite_order (input : PublishedCircleInput)
    (n : ℤ) (hn : n ≠ 0) : n • input.fundamental ≠ 0 := by
  intro h
  have hwind : input.pairing (ContinuousMap.id WindingCircle) input.fundamental = 1 := by
    apply input.winding _ 1 ((Path.segment (0 : ℝ) 1).cast rfl (by simp))
    intro t
    simp [Path.cast, Path.segment_apply, AffineMap.lineMap_apply]
  have h' := congrArg (input.pairing (ContinuousMap.id WindingCircle)) h
  exact hn (by simpa [map_zsmul, hwind] using h')

end CoarseAssembly

end

end OAI
