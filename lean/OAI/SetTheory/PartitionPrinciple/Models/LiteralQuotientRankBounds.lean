import OAI.SetTheory.PartitionPrinciple.Definability.FixedTopCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem rank_natSetCode_lt (n : Nat) : ZFSet.rank (natSetCode n) < o := by
  induction n with
  | zero => simpa only [natSetCode_zero, ZFSet.rank_empty] using limit.pos
  | succ n ih =>
    rw [natSetCode_succ, ZFSet.rank_insert]
    exact max_lt (limit.succ_lt ih) ih

theorem rank_equivalenceClasses_lt {A : ZFSet.{u}} (E : ZFSet.{u})
    (carrier : ZFSet.rank A < o) : ZFSet.rank (equivalenceClasses A E) < o := by
  have subset : equivalenceClasses A E ⊆ ZFSet.powerset A :=
    fun _ hx => (ZFSet.mem_sep.1 hx).1
  have bound := ZFSet.rank_mono subset
  rw [ZFSet.rank_powerset] at bound
  exact bound.trans_lt (limit.succ_lt carrier)

theorem rank_fixedTopCarrier_lt {P : ZFSet.{u}} (carrier : ZFSet.rank P < o) :
    ZFSet.rank (fixedTopCarrier P) < o := by
  rw [fixedTopCarrier, ZFSet.rank_insert]
  exact max_lt (limit.succ_lt carrier) carrier

end PartitionPilot.Forcing

end

end OAI
