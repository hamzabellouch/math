import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}
variable {G : Type v} [Group G] (a : PosetAction G P)

theorem act_familySet_transport (T U : ZFSet.{u})
    (validT : ∀ z ∈ T, IsName s z) (validU : ∀ z ∈ U, IsName s z)
    (g : G) (transport : ∀ τ : Name s, (a.act s g τ).val ∈ U ↔ τ.val ∈ T) :
    a.act s g (familySet ⊤ T validT) = familySet ⊤ U validU := by
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T validT)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, equal, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T validT τ q).1 entry
    have target := (transport τ).2 hτ
    change a.act s g τ = σ at equal
    exact ⟨equal ▸ target, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    have back : (a.act s g⁻¹ σ).val ∈ T := (transport _).1 (by
      simpa only [a.act_inv_right] using hσ)
    exact ⟨a.act s g⁻¹ σ, ⊤,
      (entry_familySet ⊤ T validT _ ⊤).2 ⟨back, rfl⟩,
      a.act_inv_right s g σ, (a.iso g).map_top⟩

theorem familySet_support (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (K : Subgroup G) (supported : ∀ τ : Name s, τ.val ∈ T → K ≤ a.stabilizer s τ) :
    K ≤ a.stabilizer s (familySet ⊤ T valid) := by
  intro g hg
  apply Name.ext
  intro σ p
  change Entry σ (rename s (a.iso g) (familySet ⊤ T valid)) p ↔ _
  rw [entry_rename, entry_familySet]
  constructor
  · rintro ⟨τ, q, entry, equal, hp⟩
    obtain ⟨hτ, rfl⟩ := (entry_familySet ⊤ T valid τ q).1 entry
    have fixed := supported τ hτ hg
    change a.act s g τ = σ at equal
    rw [fixed] at equal
    exact ⟨equal ▸ hτ, hp.symm.trans (a.iso g).map_top⟩
  · rintro ⟨hσ, rfl⟩
    exact ⟨σ, ⊤, (entry_familySet ⊤ T valid σ ⊤).2 ⟨hσ, rfl⟩,
      supported σ hσ hg, (a.iso g).map_top⟩

theorem familySet_hs_of_supported (F : NormalSubgroupFamily G)
    (T : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
    (K : Subgroup G) (member : F.mem K)
    (supported : ∀ τ : Name s, τ.val ∈ T → K ≤ a.stabilizer s τ)
    (children : ∀ τ : Name s, τ.val ∈ T → HereditarilySymmetric a s F τ) :
    HereditarilySymmetric a s F (familySet ⊤ T valid) :=
  HereditarilySymmetric.mk (F.upward member (familySet_support a T valid K supported))
    (fun τ p entry => children τ ((entry_familySet ⊤ T valid τ p).1 entry).1)

end PartitionPilot.Forcing.Name

end

end OAI
