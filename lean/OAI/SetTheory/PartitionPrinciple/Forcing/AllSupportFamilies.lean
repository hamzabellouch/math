import OAI.SetTheory.PartitionPrinciple.Definability.TaggedSumPresentations

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization Compression.RecursiveMaps
universe u v

def allSupportFamily (G : Type u) [Group G] : NormalSubgroupFamily G where
  mem := fun _ => True
  top := True.intro
  upward := fun _ _ => True.intro
  inf := fun _ _ => True.intro
  conjugate := fun _ {_} _ => True.intro

def allSupportBasis (G : Type u) [Group G] : ULift.{u} (Fin 1) → Subgroup G :=
  fun _ => ⊥

theorem allSupportFamily_basis (G : Type u) [Group G] (H : Subgroup G) :
    (allSupportFamily G).mem H ↔ ∃ i, allSupportBasis G i ≤ H :=
  ⟨fun _ => ⟨⟨0⟩, bot_le⟩, fun _ => True.intro⟩

namespace PosetAction
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

theorem allSupport_hs (τ : Name s) :
    HereditarilySymmetric a s (allSupportFamily G) τ := by
  induction τ using Name.inductionOn with
  | step τ ih => exact HereditarilySymmetric.mk True.intro ih

theorem symmetricDomain_allSupport (D : Name.NameDomain s) :
    a.symmetricDomain s D (allSupportFamily G) = D := by
  have names : (a.symmetricDomain s D (allSupportFamily G)).names = D.names := by
    apply Set.ext
    intro τ
    exact ⟨fun h => h.1, fun h => ⟨h, a.allSupport_hs s τ⟩⟩
  have ext : ∀ E F : Name.NameDomain s, E.names = F.names → E = F := by
    intro E F same
    cases E
    cases F
    cases same
    rfl
  exact ext _ _ names

end PosetAction

end PartitionPilot.Forcing

end

end OAI
