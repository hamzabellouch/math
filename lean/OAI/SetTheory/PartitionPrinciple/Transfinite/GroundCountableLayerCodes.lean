import OAI.SetTheory.PartitionPrinciple.Geometry.GrowthLayerSourceCongruence

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

structure CountableLayerCode (L birth t D N injection : ZFSet.{u}) : Prop where
  small : InjectionCode D N injection
  cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → x ∈ D

namespace BoundedFormula

def countableLayerFormula {n} (L birth t D N injection : Fin n) : BoundedFormula n :=
  .conj (injectionFormula D N injection)
    (.allMem L (imp (pairMembershipFormula 0 t.succ birth.succ) (.mem 0 D.succ)))

theorem truth_countableLayerFormula {n} (L birth t D N injection : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (countableLayerFormula L birth t D N injection) env ↔
      CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) := by
  simp only [countableLayerFormula, Truth, truth_injectionFormula, truth_imp,
    truth_pairMembershipFormula]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.small, h.cover⟩⟩

theorem realize_countableLayerFormula (M : TransitiveGround.{u}) {n}
    (L birth t D N injection : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (countableLayerFormula L birth t D N injection).toFormula env ↔
      CountableLayerCode (env L) (env birth) (env t) (env D) (env N) (env injection) :=
  (realize_toFormula M _ env members).trans (truth_countableLayerFormula L birth t D N injection env)

end BoundedFormula

namespace CountableLayerCode

def toLayer {M : TransitiveGround.{u}} {L r μ birth t D N injection : ZFSet.{u}}
    (code : CountableLayerCode L birth t D N injection)
    (Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u})
    (hD : D ∈ M.sets) (hInjection : injection ∈ M.sets) (omega : N = ZFSet.omega) :
    CodedGrowthLayer M Space sourceOrder sourceMeet L r μ birth t :=
  .countablePoints D hD ⟨injection, hInjection, omega ▸ code.small⟩ code.cover

theorem exists_witness {M : TransitiveGround.{u}} {L birth t D : ZFSet.{u}}
    (small : M.groundEmbeddable D ZFSet.omega)
    (cover : ∀ x ∈ L, ZFSet.pair x t ∈ birth → x ∈ D) :
    ∃ injection ∈ M.sets, CountableLayerCode L birth t D ZFSet.omega injection := by
  obtain ⟨injection, hInjection, code⟩ := small
  exact ⟨injection, hInjection, code, cover⟩

end CountableLayerCode

end PartitionPilot.Forcing

end

end OAI
