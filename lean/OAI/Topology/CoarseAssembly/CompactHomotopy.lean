import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.HomotopyFilling
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.CStarAlgebra.Spectrum

namespace OAI

/-! # Compact homotopy invariance in the actual Fredholm presentation

A homotopy of maps gives a point-norm continuous homotopy of pulled-back
representations. Its Fredholm operator stays fixed. This discharges the
homotopy field of the published filling input directly from the definitions.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty CStarAlgebra

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X]

def homotopySlice {f g : C(X, Y)} (F : f.Homotopy g) (t : Interval) : C(X, Y) :=
  F.toContinuousMap.curry t

omit [CompactSpace X] in
@[simp] theorem homotopySlice_start {f g : C(X, Y)} (F : f.Homotopy g) :
    homotopySlice F start = f := by
  ext x
  exact F.map_zero_left x

omit [CompactSpace X] in
@[simp] theorem homotopySlice_finish {f g : C(X, Y)} (F : f.Homotopy g) :
    homotopySlice F finish = g := by
  ext x
  exact F.map_one_left x

theorem pullback_homotopy_continuous {f g : C(X, Y)} (F : f.Homotopy g)
    (a : C₀(Y, ℂ)) : Continuous (fun t : Interval =>
      pullback (compactMap (homotopySlice F t)) a) := by
  have hc : Continuous (fun t : Interval => a.toContinuousMap.comp (homotopySlice F t)) :=
    (ContinuousMap.continuous_postcomp a.toContinuousMap).comp
      F.toContinuousMap.curry.continuous
  have hl : Continuous (compactFunctionLift (X := X) : C(X, ℂ) → C₀(X, ℂ)) :=
    map_continuous _
  exact hl.comp hc

def pullbackCycleHomotopy {f g : C(X, Y)} (F : f.Homotopy g)
    (c : OddCycle C₀(X, ℂ)) : OddHomotopy C₀(Y, ℂ) where
  space := c.space
  representation t := c.representation.comp (pullback (compactMap (homotopySlice F t)))
  operator _ := c.operator
  continuous_representation a :=
    (show Continuous (c.representation : C₀(X, ℂ) → End c.space) from
      map_continuous _).comp (pullback_homotopy_continuous F a)
  continuous_operator := continuous_const
  commutator_compact t a := c.commutator_compact (pullback (compactMap (homotopySlice F t)) a)
  square_compact t a := c.square_compact (pullback (compactMap (homotopySlice F t)) a)
  adjoint_compact t a := c.adjoint_compact (pullback (compactMap (homotopySlice F t)) a)

theorem pullbackCycleHomotopy_start {f g : C(X, Y)} (F : f.Homotopy g)
    (c : OddCycle C₀(X, ℂ)) :
    (pullbackCycleHomotopy F c).eval start = c.precomp (pullback (compactMap f)) := by
  change c.precomp (pullback (compactMap (homotopySlice F start))) = _
  rw [homotopySlice_start]

theorem pullbackCycleHomotopy_finish {f g : C(X, Y)} (F : f.Homotopy g)
    (c : OddCycle C₀(X, ℂ)) :
    (pullbackCycleHomotopy F c).eval finish = c.precomp (pullback (compactMap g)) := by
  change c.precomp (pullback (compactMap (homotopySlice F finish))) = _
  rw [homotopySlice_finish]

theorem compact_homotopy_invariance (f g : C(X, Y)) (F : f.Homotopy g) :
    pushforward (compactMap f) = pushforward (compactMap g) := by
  apply hom_ext
  intro c
  change precomp (pullback (compactMap f)) (cycleClass C₀(X, ℂ) c) =
    precomp (pullback (compactMap g)) (cycleClass C₀(X, ℂ) c)
  rw [precomp_cycleClass, precomp_cycleClass]
  have hh := homotopy_eq (pullbackCycleHomotopy F c)
  rwa [pullbackCycleHomotopy_start, pullbackCycleHomotopy_finish] at hh

end CoarseAssembly.Analytic

end

end OAI
