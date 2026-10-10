import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.AnalyticKHomology
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Algebra.Colimit.Module

namespace OAI

/-!
# Locally finite analytic K-homology and coarsening

The domain is the odd Fredholm-module group of the actual algebra `C₀(Y, ℂ)`.
A proper continuous map acts by pulling back functions and representations.
The coarsening limit is an actual algebraic direct limit of those groups.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open scoped ZeroAtInfty

universe u

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

@[simp] theorem pullback_apply (f : CocompactMap X Y) (a : C₀(Y, ℂ)) (x : X) :
    pullback f a x = a (f x) := rfl

theorem pullback_comp (f : CocompactMap X Y) (g : CocompactMap Y Z) :
    pullback (g.comp f) = (pullback f).comp (pullback g) := by
  ext a x
  rfl

@[simp] theorem pullback_id : pullback (CocompactMap.id X) = NonUnitalStarAlgHom.id ℂ C₀(X, ℂ) := by
  ext a x
  rfl

theorem pushforward_comp (f : CocompactMap X Y) (g : CocompactMap Y Z) :
    pushforward (g.comp f) = (pushforward g).comp (pushforward f) := by
  rw [pushforward, pullback_comp, precomp_comp]
  rfl

@[simp] theorem pushforward_id : pushforward (CocompactMap.id X) = AddMonoidHom.id _ := by
  simp only [pushforward, pullback_id, precomp_id]

attribute [instance] Coarsening.topology

namespace Coarsening

instance (C : Coarsening) :
    DirectedSystem (fun r => LocallyFiniteK1 (C.space r)) (fun r s h => C.map r s h) where
  map_self r x := by simp [map, C.inclusion_self]
  map_map t s r hrs hst x := by
    change (pushforward (C.inclusion s t hst)) ((pushforward (C.inclusion r s hrs)) x) = _
    rw [← AddMonoidHom.comp_apply, ← pushforward_comp, ← C.inclusion_comp]
    rfl

def of (C : Coarsening) (r : ℕ) : LocallyFiniteK1 (C.space r) →+ C.Homology :=
  AddCommGroup.DirectLimit.of (fun n => LocallyFiniteK1 (C.space n))
    (fun n m h => C.map n m h) r

end Coarsening

end CoarseAssembly.Analytic

end

end OAI
