import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundSmallFunctionSpaces

namespace OAI

section

namespace PartitionPilot.Forcing.InjectionCode

universe u

theorem restrict {D N f Q : ZFSet.{u}} (h : InjectionCode D N f) (subset : Q ⊆ D) :
    InjectionCode Q N (ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).2, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, rel, unique⟩ := h.function.2 x (subset hx)
    have hy := (ZFSet.pair_mem_prod.1 (h.function.1 rel)).2
    exact ⟨y, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩,
      fun z hz => unique z (ZFSet.mem_sep.1 hz).1⟩
  · intro x y z hx hy
    exact h.injective x y z (ZFSet.mem_sep.1 hx).1 (ZFSet.mem_sep.1 hy).1

end PartitionPilot.Forcing.InjectionCode

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem injection_restriction_mem (separation : SeparationSchema M.sets)
    {Q N f : ZFSet.{u}} (hQ : Q ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) :
    ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f ∈ M.sets := by
  let params := extend Q (extend N Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.productElementFormula 0 1 2).toFormula
    params (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))) hf
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params)) f =
        ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact ⟨hz, (BoundedFormula.truth_productElementFormula 0 1 2 _).1
        ((BoundedFormula.realize_toFormula M _ _ (Fin.cases (M.transitive hf hz)
          (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))))).1 rel)⟩
    · rintro ⟨hz, rel⟩
      exact ⟨hz, (BoundedFormula.realize_toFormula M _ _ (Fin.cases (M.transitive hf hz)
        (Fin.cases hQ (Fin.cases hN (fun j => Fin.elim0 j))))).2
          ((BoundedFormula.truth_productElementFormula 0 1 2 _).2 rel)⟩
  exact eq ▸ selected

theorem groundEmbeddable_restrict (separation : SeparationSchema M.sets)
    {D Q N : ZFSet.{u}} (hQ : Q ∈ M.sets) (hN : N ∈ M.sets) (subset : Q ⊆ D)
    (small : M.groundEmbeddable D N) : M.groundEmbeddable Q N := by
  obtain ⟨f, hf, code⟩ := small
  exact ⟨ZFSet.sep (fun z => z ∈ ZFSet.prod Q N) f,
    M.injection_restriction_mem separation hQ hN hf, code.restrict subset⟩

theorem smallPartialFunctions_restrict (separation : SeparationSchema M.sets)
    {X Y N p q : ZFSet.{u}} (hp : p ∈ M.smallPartialFunctions X Y N)
    (hq : q ∈ M.sets) (hN : N ∈ M.sets) (subset : q ⊆ p) : q ∈ M.smallPartialFunctions X Y N := by
  obtain ⟨_, code, small⟩ := (M.mem_smallPartialFunctions X Y N p).1 hp
  exact (M.mem_smallPartialFunctions X Y N q).2
    ⟨hq, code.mono subset, M.groundEmbeddable_restrict separation hq hN subset small⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
