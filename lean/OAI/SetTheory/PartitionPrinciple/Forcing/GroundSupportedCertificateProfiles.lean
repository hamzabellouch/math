import OAI.SetTheory.PartitionPrinciple.Definability.SupportedCertificateRelations

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

theorem SupportedEqualityCertificate.basis_nonempty
    {nodes N order R niceEval visibilityEval value F B f : ZFSet.{u}}
    (certificate : SupportedEqualityCertificate nodes N order R niceEval visibilityEval value F B f)
    (nonempty : F.Nonempty) : B.Nonempty := by
  obtain ⟨v, hv⟩ := nonempty
  obtain ⟨w, hw, _⟩ := certificate.2.2.1 v hv
  exact ⟨w, hw⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

theorem supportedCertificate_profile_eq
    (a : PosetAction G P) (s : Presentation P) (b : Presentation L)
    (d : PosetAction G L) (T : ZFSet.{u}) (H : ConditionFilter P)
    {N order R niceEval value F B f : ZFSet.{u}}
    (certificate : SupportedEqualityCertificate b.carrier N order R niceEval
      (Name.eval {p | H.mem p} (M.niceVisibilityEvaluationName a s b T d.principalFix))
      value F B f) :
    F = M.visibleSupportProfile a s b d T H value := by
  have describes (v : L) :
      value ∈ Name.eval {p | H.mem p} (M.niceVisibilityName a s T (d.principalFix v)) ↔
        b.encode v ∈ F :=
    certificate.2.2.2.2.1 (b.encode v) _
      ((M.niceVisibilityEvaluationName_entry a s b T d.principalFix H v _).2 rfl)
      (b.encode_mem v)
  apply ZFSet.ext
  intro x
  constructor
  · intro member
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (certificate.1 member)
    exact (M.encode_mem_visibleSupportProfile a s b d T H value v).2 ((describes v).2 member)
  · intro member
    obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (b.subset_carrier _ member)
    exact (describes v).1 ((M.encode_mem_visibleSupportProfile a s b d T H value v).1 member)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
