import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRowAssignmentCuts

namespace OAI

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {Q P : Type u} (t : Presentation Q) (s : Presentation P)
variable (restrict : Q → P) (row assignments : Q → ZFSet.{u})
variable (levels alpha : ZFSet.{u})
variable (code : ∀ q, t.encode q = ZFSet.pair (row q) (assignments q))
variable (lower_code : ∀ q, s.encode (restrict q) =
  ZFSet.pair (row q) (assignmentCut levels alpha (assignments q)))

include code lower_code in
theorem graph_eq_rowAssignmentCutGraph :
    t.graph s restrict = rowAssignmentCutGraph t.carrier s.carrier levels alpha := by
  apply ZFSet.ext
  intro z
  rw [mem_graph]
  constructor
  · rintro ⟨q, rfl⟩
    rw [code q]
    exact (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).2
      ⟨code q ▸ t.encode_mem q, s.encode_mem (restrict q), lower_code q⟩
  · intro member
    obtain ⟨upper, hu, lower, _, equal⟩ := ZFSet.mem_prod.1
      ((mem_rowAssignmentCutGraph _ _ _ _ z).1 member).1
    obtain ⟨q, eq⟩ := (t.mem_carrier upper).1 hu
    have entry : ZFSet.pair (t.encode q) lower ∈
        rowAssignmentCutGraph t.carrier s.carrier levels alpha := by
      rw [eq, ← equal]
      exact member
    rw [code q] at entry
    have parts := (pair_mem_rowAssignmentCutGraph _ _ _ _ _ _ _).1 entry
    refine ⟨q, ?_⟩
    rw [eq, (lower_code q).trans parts.2.2.symm]
    exact equal.symm

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem presentedRowAssignmentCutGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q P : Type u} (t : Presentation Q) (s : Presentation P)
    (restrict : Q → P) (row assignments : Q → ZFSet.{u}) (levels alpha : ZFSet.{u})
    (code : ∀ q, t.encode q = ZFSet.pair (row q) (assignments q))
    (lower_code : ∀ q, s.encode (restrict q) =
      ZFSet.pair (row q) (assignmentCut levels alpha (assignments q)))
    (upper : t.carrier ∈ M.sets) (lower : s.carrier ∈ M.sets)
    (hLevels : levels ∈ M.sets) (hAlpha : alpha ∈ M.sets) :
    t.graph s restrict ∈ M.sets := by
  rw [t.graph_eq_rowAssignmentCutGraph s restrict row assignments levels alpha code lower_code]
  exact M.rowAssignmentCutGraph_mem pairing unions powers separation upper lower hLevels hAlpha

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
