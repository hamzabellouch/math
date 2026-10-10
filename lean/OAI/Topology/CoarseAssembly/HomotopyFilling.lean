import OAI.Topology.CoarseAssembly.CountableAdditivity
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Convex.Basic

namespace OAI

/-! # The precise homotopy and odd-coefficient inputs for filling

Blackadar, *K-Theory for Operator Algebras*, 2nd ed. (1998), Proposition
17.9.1 and §19.8.3 give homotopy invariance in the first variable and
`KK₁(ℂ, ℂ) = 0`. Their required specializations are explicit below.
Vanishing for a compact contractible space, and then for its countable
family, is derived rather than assumed.
-/

noncomputable section

namespace CoarseAssembly.Analytic

open unitInterval

structure PublishedCompactHomotopyInput where
  homotopy : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [CompactSpace Y] (f g : C(X, Y)),
    Nonempty (f.Homotopy g) → pushforward (compactMap f) = pushforward (compactMap g)
  point_odd_zero : Subsingleton (LocallyFiniteK1 Unit)

/-- Actual continuous contraction data; this contains no K-theory assertion. -/
structure CompactContraction (X : Type) [TopologicalSpace X] where
  center : X
  homotopy : (ContinuousMap.id X).Homotopy (ContinuousMap.const X center)

theorem compactMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [CompactSpace X] [CompactSpace Y]
    (f : C(X, Y)) (g : C(Y, Z)) :
    compactMap (g.comp f) = (compactMap g).comp (compactMap f) := by
  apply CocompactMap.ext
  intro x
  rfl

theorem compactMap_id {X : Type} [TopologicalSpace X] [CompactSpace X] :
    compactMap (ContinuousMap.id X) = CocompactMap.id X := by
  apply CocompactMap.ext
  intro x
  rfl

theorem contracted_odd_group_zero (input : PublishedCompactHomotopyInput)
    {X : Type} [TopologicalSpace X] [CompactSpace X] (c : CompactContraction X) :
    Subsingleton (LocallyFiniteK1 X) := by
  let toPoint : C(X, Unit) := ContinuousMap.const X ()
  let fromPoint : C(Unit, X) := ContinuousMap.const Unit c.center
  have hconst : ContinuousMap.const X c.center = fromPoint.comp toPoint := by
    ext x
    rfl
  have hh := input.homotopy (ContinuousMap.id X) (ContinuousMap.const X c.center)
    ⟨c.homotopy⟩
  rw [compactMap_id, pushforward_id, hconst, compactMap_comp, pushforward_comp] at hh
  have hz : ∀ a : LocallyFiniteK1 X, a = 0 := by
    intro a
    have heq := DFunLike.congr_fun hh a
    change a = _ at heq
    have hp : pushforward (compactMap toPoint) a = 0 := input.point_odd_zero.elim _ _
    simpa only [AddMonoidHom.comp_apply, hp, map_zero] using heq
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

theorem contracted_family_odd_group_zero (input : PublishedCompactHomotopyInput)
    (X : ℕ → Type) [∀ j, TopologicalSpace (X j)] [∀ j, CompactSpace (X j)]
    [∀ j, T2Space (X j)] (c : ∀ j, CompactContraction (X j))
    (hadd : CountableAdditivityInput X) : Subsingleton (LocallyFiniteK1 (Sigma X)) := by
  let : ∀ j, Subsingleton (LocallyFiniteK1 (X j)) := fun j => contracted_odd_group_zero input (c j)
  exact sigma_group_subsingleton X hadd

end CoarseAssembly.Analytic

end

end OAI
