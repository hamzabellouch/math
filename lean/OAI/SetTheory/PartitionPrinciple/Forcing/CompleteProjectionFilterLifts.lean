import OAI.SetTheory.PartitionPrinciple.Geometry.CompleteProjectionPredensity

namespace OAI

section

namespace PartitionPilot.Forcing.CompleteProjection
universe u v
variable {Upper : Type u} {Lower : Type v}
variable [PartialOrder Upper] [PartialOrder Lower]
variable {restriction : Upper →o Lower} {inclusion : Lower ↪o Upper}
variable (projection : CompleteProjection restriction inclusion)

theorem exists_mem_below_projected (H : ConditionFilter Upper)
    (p : Upper) (hp : H.mem p) (q : Lower)
    (hq : (projection.projectedFilter H).mem q) :
    ∃ r : Upper, H.mem r ∧ r ≤ p ∧ restriction r ≤ q := by
  obtain ⟨r, member, below, included⟩ := H.directed hp hq
  exact ⟨r, member, below, (projection.le_include_iff r q).1 included⟩

end PartitionPilot.Forcing.CompleteProjection

end

end OAI
