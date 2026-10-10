import OAI.SetTheory.PartitionPrinciple.Definability.DecodedFunctionGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.GroundPartialFunctionSpaces

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace InjectionCode

theorem empty (N : ZFSet.{u}) : InjectionCode ∅ N ∅ := by
  refine ⟨⟨ZFSet.empty_subset _, ?_⟩, ?_⟩
  · intro x hx
    exact False.elim (ZFSet.notMem_empty x hx)
  · intro x _ z hx _
    exact False.elim (ZFSet.notMem_empty (ZFSet.pair x z) hx)

theorem decoded_injective {D N f : ZFSet.{u}} (h : InjectionCode D N f) :
    Function.Injective ((SetRealization.SetMembers.presentation D).decodeFunction
      (SetRealization.SetMembers.presentation N) f h.function) := by
  intro x y eq
  apply SetRealization.SetMembers.raw_injective D
  have hx := (SetRealization.SetMembers.presentation D).decodeFunction_mem
    (SetRealization.SetMembers.presentation N) f h.function x
  have hy := (SetRealization.SetMembers.presentation D).decodeFunction_mem
    (SetRealization.SetMembers.presentation N) f h.function y
  rw [eq] at hx
  exact h.injective _ _ _ hx hy

theorem countable_domain {D N f : ZFSet.{u}} (h : InjectionCode D N f)
    [Countable (SetRealization.SetMembers N)] : Countable (SetRealization.SetMembers D) :=
  h.decoded_injective.countable

end InjectionCode

namespace BoundedFormula

open SetFormula

theorem truth_injectionFormula {n} (d c f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (injectionFormula d c f) env ↔ InjectionCode (env d) (env c) (env f) := by
  simp only [injectionFormula, Truth, truth_functionFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨function, injective⟩
    refine ⟨function, ?_⟩
    intro x y z hx hy
    have xz := ZFSet.pair_mem_prod.1 (function.1 hx)
    have yz := ZFSet.pair_mem_prod.1 (function.1 hy)
    exact injective x xz.1 y yz.1 z xz.2 ⟨hx, hy⟩
  · intro h
    exact ⟨h.function, fun x _ y _ z _ ⟨hx, hy⟩ => h.injective x y z hx hy⟩

end BoundedFormula

namespace SetFormula

end SetFormula

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

theorem realize_hasInjectionFormula {n} (d c : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (hasInjectionFormula d c) env ↔ M.groundEmbeddable (env d) (env c) := by
  rw [hasInjectionFormula, realize_ex]
  constructor
  · rintro ⟨f, hf, rel⟩
    exact ⟨f, hf, (BoundedFormula.truth_injectionFormula d.succ c.succ 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hf members)).1 rel)⟩
  · rintro ⟨f, hf, code⟩
    exact ⟨f, hf, (BoundedFormula.realize_toFormula M _ _ (Fin.cases hf members)).2
      ((BoundedFormula.truth_injectionFormula d.succ c.succ 0 _).2 code)⟩

theorem empty_groundEmbeddable (N : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    M.groundEmbeddable ∅ N := ⟨∅, M.empty_mem nonempty, InjectionCode.empty N⟩

theorem groundEmbeddable_countable {D N : ZFSet.{u}} (h : M.groundEmbeddable D N)
    [Countable (SetMembers N)] : Countable (SetMembers D) := by
  obtain ⟨f, _, code⟩ := h
  exact code.countable_domain

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
