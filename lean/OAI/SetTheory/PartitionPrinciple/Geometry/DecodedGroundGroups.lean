import OAI.SetTheory.PartitionPrinciple.Definability.DecodedFunctionGraphs

namespace OAI

section

namespace PartitionPilot.Forcing.GroupCode

open SetRealization
universe u
variable {G m i e : ZFSet.{u}} (h : GroupCode G m i e)

noncomputable def mul (x y : SetMembers G) : SetMembers G :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction
    (SetMembers.presentation G) m h.mul_function (x, y)

noncomputable def inv (x : SetMembers G) : SetMembers G :=
  (SetMembers.presentation G).decodeFunction (SetMembers.presentation G) i h.inv_function x

noncomputable def one : SetMembers G := SetMembers.ofMem e h.identity_mem

theorem raw_one : SetMembers.raw h.one = e := SetMembers.raw_ofMem e h.identity_mem

theorem mul_mem (x y : SetMembers G) :
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw (h.mul x y)) ∈ m :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction_mem
    (SetMembers.presentation G) m h.mul_function (x, y)

theorem inv_mem (x : SetMembers G) :
    ZFSet.pair (SetMembers.raw x) (SetMembers.raw (h.inv x)) ∈ i :=
  (SetMembers.presentation G).decodeFunction_mem (SetMembers.presentation G) i h.inv_function x

theorem mul_eq_iff (x y z : SetMembers G) : h.mul x y = z ↔
    ZFSet.pair (ZFSet.pair (SetMembers.raw x) (SetMembers.raw y)) (SetMembers.raw z) ∈ m :=
  ((SetMembers.presentation G).product (SetMembers.presentation G)).decodeFunction_iff
    (SetMembers.presentation G) m h.mul_function (x, y) z

theorem decoded_one_mul (x : SetMembers G) : h.mul h.one x = x := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.one_mul _ (SetMembers.raw_mem x)

theorem decoded_mul_one (x : SetMembers G) : h.mul x h.one = x := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.mul_one _ (SetMembers.raw_mem x)

theorem decoded_inv_mul (x : SetMembers G) : h.mul (h.inv x) x = h.one := by
  apply (h.mul_eq_iff _ _ _).2
  rw [h.raw_one]
  exact h.inv_mul _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem (h.inv x)) (h.inv_mem x)

theorem decoded_mul_assoc (x y z : SetMembers G) :
    h.mul (h.mul x y) z = h.mul x (h.mul y z) := by
  apply Eq.symm
  apply (h.mul_eq_iff _ _ _).2
  exact h.mul_assoc _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) _ (SetMembers.raw_mem z)
    _ (SetMembers.raw_mem (h.mul x y)) _ (SetMembers.raw_mem (h.mul y z))
    _ (SetMembers.raw_mem (h.mul (h.mul x y) z)) (h.mul_mem x y) (h.mul_mem y z)
    (h.mul_mem (h.mul x y) z)

@[instance_reducible] noncomputable def toGroup : Group (SetMembers G) where
  mul := h.mul
  one := h.one
  inv := h.inv
  mul_assoc := h.decoded_mul_assoc
  one_mul := h.decoded_one_mul
  mul_one := h.decoded_mul_one
  inv_mul_cancel := h.decoded_inv_mul

theorem multiplication_graph_eq :
    letI := h.toGroup
    ((SetMembers.presentation G).product (SetMembers.presentation G)).graph
      (SetMembers.presentation G) (fun x => x.1 * x.2) = m := by
  let := h.toGroup
  exact ((SetMembers.presentation G).product (SetMembers.presentation G)).graph_decodeFunction
    (SetMembers.presentation G) m h.mul_function

theorem inverse_graph_eq :
    letI := h.toGroup
    (SetMembers.presentation G).graph (SetMembers.presentation G) (fun x => x⁻¹) = i := by
  let := h.toGroup
  exact (SetMembers.presentation G).graph_decodeFunction (SetMembers.presentation G) i h.inv_function

theorem identity_code_eq :
    letI := h.toGroup
    (SetMembers.presentation G).encode 1 = e := h.raw_one

end PartitionPilot.Forcing.GroupCode

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

@[instance_reducible] noncomputable def decodedGroup {G m i e : ZFSet.{u}}
    (hG : G ∈ M.sets) (hm : m ∈ M.sets) (hi : i ∈ M.sets) (he : e ∈ M.sets)
    (laws : Realize M.sets (BoundedFormula.groupFormula 0 1 2 3).toFormula
      (extend G (extend m (extend i (extend e Fin.elim0))))) : Group (SetMembers G) :=
  ((M.realize_groupCode hG hm hi he).1 laws).toGroup

theorem decoded_group_graphs_mem {G m i e : ZFSet.{u}} (h : GroupCode G m i e)
    (hm : m ∈ M.sets) (hi : i ∈ M.sets) :
    letI := h.toGroup
    ((SetMembers.presentation G).product (SetMembers.presentation G)).graph
      (SetMembers.presentation G) (fun x => x.1 * x.2) ∈ M.sets ∧
      (SetMembers.presentation G).graph (SetMembers.presentation G) (fun x => x⁻¹) ∈ M.sets := by
  let := h.toGroup
  rw [h.multiplication_graph_eq, h.inverse_graph_eq]
  exact ⟨hm, hi⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
