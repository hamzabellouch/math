import OAI.SetTheory.PartitionPrinciple.Geometry.GroundEligibleCaps

namespace OAI

section

namespace PartitionPilot.Forcing
universe u

noncomputable def indexedValueLift (T U Q V F J : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ T, ∃ f ∈ ZFSet.sUnion (ZFSet.sUnion F),
    ∃ e ∈ ZFSet.sUnion (ZFSet.sUnion J),
    ∃ x ∈ U, ∃ q ∈ Q, ∃ v ∈ V,
      z = ZFSet.pair q v ∧ ZFSet.pair i f ∈ F ∧ ZFSet.pair i e ∈ J ∧
      ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f) (ZFSet.prod Q V)

theorem indexedValueLift_subset (T U Q V F J : ZFSet.{u}) :
    indexedValueLift T U Q V F J ⊆ ZFSet.prod Q V := fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_indexedValueLift (T U Q V F J q v : ZFSet.{u}) :
    ZFSet.pair q v ∈ indexedValueLift T U Q V F J ↔
      q ∈ Q ∧ v ∈ V ∧ ∃ i ∈ T, ∃ f e, ∃ x ∈ U,
        ZFSet.pair i f ∈ F ∧ ZFSet.pair i e ∈ J ∧
        ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f := by
  rw [indexedValueLift, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, i, hi, f, _, e, _, x, hx, p, hp, w, hw, equal, value, inclusion, image, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hp, hw, i, hi, f, e, x, hx, value, inclusion, image, entry⟩
  · rintro ⟨hq, hv, i, hi, f, e, x, hx, value, inclusion, image, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hq, hv⟩,
      i, hi, f, pair_second_mem_doubleUnion value, e, pair_second_mem_doubleUnion inclusion,
      x, hx, q, hq, v, hv, rfl, value, inclusion, image, entry⟩

namespace BoundedFormula
open SetFormula

def indexedValueLiftEntryFormula : BoundedFormula 9 :=
  exMem 1 (exMem 8 (exMem 10 (exMem 5 (exMem 7 (exMem 9
    (.conj (orderedPairFormula 6 1 0)
      (.conj (pairMembershipFormula 5 4 11)
        (.conj (pairMembershipFormula 5 3 12)
          (.conj (pairMembershipFormula 2 1 3) (pairMembershipFormula 2 0 4))))))))))

theorem truth_indexedValueLiftEntryFormula (env : Fin 9 → ZFSet.{u}) :
    Truth indexedValueLiftEntryFormula env ↔
      ∃ i ∈ env 1, ∃ f ∈ env 7, ∃ e ∈ env 8, ∃ x ∈ env 2, ∃ q ∈ env 3, ∃ v ∈ env 4,
        env 0 = ZFSet.pair q v ∧ ZFSet.pair i f ∈ env 5 ∧ ZFSet.pair i e ∈ env 6 ∧
        ZFSet.pair x q ∈ e ∧ ZFSet.pair x v ∈ f := by
  simp only [indexedValueLiftEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
