import OAI.SetTheory.PartitionPrinciple.Forcing.FinitePrincipalNameSupports

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization Compression.RecursiveMaps
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]
variable {G : Type v} [Group G]
variable (upper : PosetAction G P) (lower : PosetAction G Q)
variable (s : Presentation P) (t : Presentation Q) (inclusion : Q → P)
variable (J : ZFSet.{u}) (valid : ∀ z ∈ J, IsName t z)
variable (equivariant : ∀ g p, inclusion (lower.iso g p) = upper.iso g (inclusion p))
variable (closed : ∀ g (sigma : Name t), sigma.val ∈ J → (lower.act t g sigma).val ∈ J)
include equivariant closed

theorem crossStageMembershipName_act (g : G) (tau : Name s) :
    lower.act t g (crossStageMembershipName s t inclusion J valid tau) =
      crossStageMembershipName s t inclusion J valid (upper.act s g tau) := by
  apply Name.ext
  intro sigma p
  obtain ⟨sigma, rfl⟩ := (lower.nameEquiv t g).surjective sigma
  obtain ⟨p, rfl⟩ := (lower.iso g).surjective p
  change Entry (lower.act t g sigma)
    (lower.act t g (crossStageMembershipName s t inclusion J valid tau)) (lower.iso g p) ↔
    Entry (lower.act t g sigma)
      (crossStageMembershipName s t inclusion J valid (upper.act s g tau)) (lower.iso g p)
  rw [lower.entry_act, entry_crossStageMembershipName, entry_crossStageMembershipName]
  have member : (lower.act t g sigma).val ∈ J ↔ sigma.val ∈ J := by
    constructor
    · intro h
      have back := closed g⁻¹ (lower.act t g sigma) h
      simpa only [lower.act_inv_left] using back
    · exact closed g sigma
  rw [member, equivariant,
    ← lower.act_rename_of_equivariant upper t s inclusion equivariant,
    upper.forcesMem_act_iff]

theorem crossStageMembershipName_stabilizer (tau : Name s) :
    upper.stabilizer s tau ≤
      lower.stabilizer t (crossStageMembershipName s t inclusion J valid tau) := by
  intro g fixed
  change upper.act s g tau = tau at fixed
  change lower.act t g (crossStageMembershipName s t inclusion J valid tau) = _
  rw [crossStageMembershipName_act upper lower s t inclusion J valid equivariant closed, fixed]

theorem crossStageMembershipName_nice (K : Subgroup G) (tau : Name s)
    (supported : K ≤ upper.stabilizer s tau) :
    NiceNameCode lower t J K (crossStageMembershipName s t inclusion J valid tau).val := by
  apply (niceNameCode_iff lower t _).2
  exact ⟨crossStageMembershipCode_subset s t inclusion J tau,
    supported.trans (crossStageMembershipName_stabilizer upper lower s t inclusion J valid
      equivariant closed tau)⟩

theorem crossStageMembershipName_hs (F : NormalSubgroupFamily G) (K : Subgroup G)
    (member : F.mem K)
    (children : ∀ sigma : Name t, sigma.val ∈ J → HereditarilySymmetric lower t F sigma)
    (tau : Name s) (supported : K ≤ upper.stabilizer s tau) :
    HereditarilySymmetric lower t F (crossStageMembershipName s t inclusion J valid tau) := by
  exact niceNameCode_hs lower t F member children
    (crossStageMembershipName_nice upper lower s t inclusion J valid equivariant closed
      K tau supported)

end PartitionPilot.Forcing.Name

end

end OAI
