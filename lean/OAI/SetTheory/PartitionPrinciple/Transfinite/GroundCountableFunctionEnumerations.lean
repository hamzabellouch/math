import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundFunction_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B N f : ZFSet.{u}} (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets)
    (nonempty : B.Nonempty) (small : M.groundEmbeddable B ZFSet.omega)
    (function : ZFSet.IsFunc B N f) :
    ∃ e ∈ M.sets, ∃ names ∈ M.sets,
      ZFSet.IsFunc ZFSet.omega B e ∧ ZFSet.IsFunc ZFSet.omega N names ∧
      (∀ v ∈ B, ∃ n ∈ ZFSet.omega, ZFSet.pair n v ∈ e) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair n tau ∈ names → ZFSet.pair v tau ∈ f) ∧
      (∀ n ∈ ZFSet.omega, ∀ v tau, ZFSet.pair n v ∈ e →
        ZFSet.pair v tau ∈ f → ZFSet.pair n tau ∈ names) := by
  obtain ⟨e, he, enumeration, onto⟩ := M.groundCountable_enumeration
    pairing unions powers separation infinite hB nonempty small
  let names := relationCompose ZFSet.omega B N e f
  have namesGround := M.relationCompose_mem pairing unions powers separation
    (M.omega_mem separation infinite) hB hN he hf
  have namesFunction : ZFSet.IsFunc ZFSet.omega N names :=
    relationCompose_function_of_subset enumeration function (fun _ member => member)
  refine ⟨e, he, names, namesGround, enumeration, namesFunction, onto, ?_, ?_⟩
  · intro n hn v tau nv nt
    obtain ⟨_, _, w, _, nw, wt⟩ := (pair_mem_relationCompose _ _ _ _ _ n tau).1 nt
    obtain ⟨chosen, _, unique⟩ := enumeration.2 n hn
    have equal : w = v := (unique w nw).trans (unique v nv).symm
    exact equal ▸ wt
  · intro n hn v tau nv vt
    have bound := ZFSet.pair_mem_prod.1 (function.1 vt)
    exact (pair_mem_relationCompose _ _ _ _ _ n tau).2 ⟨hn, bound.2, v, bound.1, nv, vt⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
