import OAI.SetTheory.PartitionPrinciple.Forcing.CrossStageMembershipNameActions
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceNameNormalization

namespace OAI

section

namespace PartitionPilot.Forcing.Name
open SetRealization SetFormula
universe u v
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q] [OrderTop Q]
variable {G : Type v} [Group G]

theorem crossStageParameter_support
    (upper : PosetAction G P) (lower : PosetAction G Q)
    (s : Presentation P) (t : Presentation Q) (inclusion : Q → P)
    (equivariant : ∀ g p, inclusion (lower.iso g p) = upper.iso g (inclusion p))
    {n : Nat} (J : Fin n → ZFSet.{u})
    (valid : ∀ i z, z ∈ J i → IsName t z)
    (closed : ∀ i g (sigma : Name t), sigma.val ∈ J i → (lower.act t g sigma).val ∈ J i)
    (tau : Fin n → Name s) (D : NameDomain t) (env : Assignment D (n + 1))
    (names : ∀ i, (env i.castSucc).val = crossStageMembershipName s t inclusion (J i) (valid i) (tau i))
    (T : ZFSet.{u}) (validT : ∀ z ∈ T, IsName t z)
    (closedT : ∀ g (sigma : Name t), sigma.val ∈ T → (lower.act t g sigma).val ∈ T)
    (family : (env (Fin.last n)).val = familySet ⊤ T validT)
    (K : Subgroup G) (supported : ∀ i, K ≤ upper.stabilizer s (tau i)) :
    ∀ j, K ≤ lower.stabilizer t (env j).val := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro g _
    change lower.act t g (env (Fin.last n)).val = (env (Fin.last n)).val
    rw [family]
    exact act_familySet lower T validT closedT g
  · rw [names i]
    exact (supported i).trans
      (crossStageMembershipName_stabilizer upper lower s t inclusion (J i) (valid i)
        equivariant (closed i) (tau i))

end PartitionPilot.Forcing.Name

end

end OAI
