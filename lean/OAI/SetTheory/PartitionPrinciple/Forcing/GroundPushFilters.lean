import OAI.SetTheory.PartitionPrinciple.Definability.PairPushFilterFamilies

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

def pushFilterMemberFormula {n} (y L r S F : Fin n) : BoundedFormula n :=
  .conj (.mem y L) (exMem F (exMem L.succ
    (.conj (pairMembershipFormula 1 0 S.succ.succ)
      (pairMembershipFormula 0 y.succ.succ r.succ.succ))))

theorem truth_pushFilterMemberFormula {n} (y L r S F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pushFilterMemberFormula y L r S F) env ↔
      env y ∈ pushFilterCode (env L) (env r) (env S) (env F) := by
  simp only [pushFilterMemberFormula, Truth, truth_exMem,
    truth_pairMembershipFormula, mem_pushFilterCode]
  rfl

def pushFilterFormula {n} (V L r S F : Fin n) : BoundedFormula n :=
  .conj (.allMem V (pushFilterMemberFormula 0 L.succ r.succ S.succ F.succ))
    (.allMem L (imp (pushFilterMemberFormula 0 L.succ r.succ S.succ F.succ) (.mem 0 V.succ)))

theorem truth_pushFilterFormula {n} (V L r S F : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pushFilterFormula V L r S F) env ↔
      env V = pushFilterCode (env L) (env r) (env S) (env F) := by
  simp only [pushFilterFormula, Truth, truth_imp, truth_pushFilterMemberFormula]
  constructor
  · rintro ⟨sound, complete⟩
    apply ZFSet.ext
    intro y
    exact ⟨sound y, fun hy => complete y (pushFilterCode_subset _ _ _ _ hy) hy⟩
  · intro equal
    refine ⟨fun y hy => equal ▸ hy, ?_⟩
    intro y _ hy
    change y ∈ env V
    exact equal.symm ▸ hy

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem pushFilterCode_mem (separation : SeparationSchema M.sets)
    {L r S F : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hS : S ∈ M.sets) (hF : F ∈ M.sets) : pushFilterCode L r S F ∈ M.sets := by
  let params := extend L (extend r (extend S (extend F Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pushFilterMemberFormula 0 1 2 3 4) params
    (Fin.cases hL (Fin.cases hr (Fin.cases hS (Fin.cases hF (fun i => Fin.elim0 i))))) hL
  have equal : ZFSet.sep (fun y => BoundedFormula.Truth
      (BoundedFormula.pushFilterMemberFormula 0 1 2 3 4) (extend y params)) L =
      pushFilterCode L r S F := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, BoundedFormula.truth_pushFilterMemberFormula]
    exact ⟨And.right, fun hy => ⟨pushFilterCode_subset L r S F hy, hy⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
