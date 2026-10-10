import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveRowNameActions

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization
universe u
variable (M : TransitiveGround.{u}) {R : Type u} (c : Presentation R)
variable {T stages history : ZFSet.{u}}
variable (run : RecursiveRefinementDataHistory M c.carrier T stages history)
variable (ordinal : ordinalSetProperty stages) (carrier : c.carrier ∈ M.sets)
local notation "upper" => SetMembers.presentation (M.refinementHistoryForcing c.carrier T stages history)
local notation "inclusion" => M.refinementHistoryRowInclusion c run ordinal carrier

theorem refinementHistory_originalRowFamily_eq (X : ZFSet.{u})
    (valid : ∀ z ∈ X, IsName c z) :
    Name.renamedFamily upper inclusion X valid = Name.renamedFamily c.pairEmpty id X valid := by
  have codes (tau : Name c) :
      (Name.rename upper inclusion tau).val = (Name.rename c.pairEmpty id tau).val := by
    have unchanged := M.refinementHistoryRowNameLift_val c run ordinal carrier
      (Name.rename c.pairEmpty id tau)
    change (Name.rename upper inclusion (Name.rename c.pairEmpty id tau)).val = _ at unchanged
    rw [Name.rename_comp] at unchanged
    exact unchanged
  apply ZFSet.ext
  intro z
  rw [Name.mem_renamedFamily, Name.mem_renamedFamily]
  exact ⟨fun ⟨tau, member, equal⟩ => ⟨tau, member, equal.trans (codes tau)⟩,
    fun ⟨tau, member, equal⟩ => ⟨tau, member, equal.trans (codes tau).symm⟩⟩

theorem refinementHistory_originalRowFamilySet_eq
    (one : SetMembers (M.refinementHistoryForcing c.carrier T stages history))
    (X : ZFSet.{u}) (valid : ∀ z ∈ X, IsName c z)
    (validDirect : ∀ z ∈ Name.renamedFamily upper inclusion X valid, IsName upper z)
    (validPairEmpty : ∀ z ∈ Name.renamedFamily c.pairEmpty id X valid, IsName upper z) :
    Name.familySet one (Name.renamedFamily upper inclusion X valid) validDirect =
      Name.familySet one (Name.renamedFamily c.pairEmpty id X valid) validPairEmpty := by
  apply Subtype.ext
  rw [Name.familySet_code, Name.familySet_code,
    M.refinementHistory_originalRowFamily_eq c run ordinal carrier]

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
