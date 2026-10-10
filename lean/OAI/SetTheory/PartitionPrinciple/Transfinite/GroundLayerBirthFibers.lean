import OAI.SetTheory.PartitionPrinciple.Definability.ParentSupportCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def layerBirthFiber (L birth t : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x t ∈ birth) L

theorem mem_layerBirthFiber (L birth t x : ZFSet.{u}) :
    x ∈ layerBirthFiber L birth t ↔ x ∈ L ∧ ZFSet.pair x t ∈ birth := ZFSet.mem_sep

namespace BoundedFormula

def layerBirthFiberFormula {n} (F L birth t : Fin n) : BoundedFormula n :=
  .conj (.allMem F (.mem 0 L.succ)) (.allMem L
    (.conj (imp (.mem 0 F.succ) (pairMembershipFormula 0 t.succ birth.succ))
      (imp (pairMembershipFormula 0 t.succ birth.succ) (.mem 0 F.succ))))

theorem truth_layerBirthFiberFormula {n} (F L birth t : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (layerBirthFiberFormula F L birth t) env ↔
      env F = layerBirthFiber (env L) (env birth) (env t) := by
  simp only [layerBirthFiberFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ x ∈ env F, x ∈ env L) ∧ ∀ x ∈ env L,
    (x ∈ env F → ZFSet.pair x (env t) ∈ env birth) ∧
      (ZFSet.pair x (env t) ∈ env birth → x ∈ env F)) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro x
    rw [mem_layerBirthFiber]
    exact ⟨fun hx => ⟨subset x hx, (spec x (subset x hx)).1 hx⟩,
      fun ⟨hx, born⟩ => (spec x hx).2 born⟩
  · intro eq
    rw [eq]
    exact ⟨fun _ hx => (mem_layerBirthFiber _ _ _ _).1 hx |>.1,
      fun x hx => ⟨fun born => (mem_layerBirthFiber _ _ _ _).1 born |>.2,
        fun born => (mem_layerBirthFiber _ _ _ _).2 ⟨hx, born⟩⟩⟩

theorem realize_layerBirthFiberFormula (M : TransitiveGround.{u}) {n}
    (F L birth t : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (layerBirthFiberFormula F L birth t).toFormula env ↔
      env F = layerBirthFiber (env L) (env birth) (env t) :=
  (realize_toFormula M _ env members).trans (truth_layerBirthFiberFormula F L birth t env)
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem layerBirthFiber_mem (separation : SeparationSchema M.sets) {L birth t : ZFSet.{u}}
    (hL : L ∈ M.sets) (hBirth : birth ∈ M.sets) (ht : t ∈ M.sets) :
    layerBirthFiber L birth t ∈ M.sets := by
  let params := extend t (extend birth Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairMembershipFormula 0 1 2)
    params (Fin.cases ht (Fin.cases hBirth (fun i => Fin.elim0 i))) hL
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth (BoundedFormula.pairMembershipFormula 0 1 2)
      (extend x params)) L = layerBirthFiber L birth t := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, mem_layerBirthFiber]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 0 1 2 _)
  exact eq ▸ selected
end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
