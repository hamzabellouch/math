import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompleteProjectionGenericity

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
variable (s : Presentation P)

theorem generic_meets_ground_predense (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (H : ConditionFilter P) (generic : H.GenericFor (M.codedFamily s))
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (subset : A ⊆ s.carrier)
    (predense : ∀ q ∈ s.carrier, ∃ p ∈ A, ∃ r ∈ s.carrier,
      ZFSet.pair r q ∈ s.conditionOrder ∧ ZFSet.pair r p ∈ s.conditionOrder) :
    ∃ p : P, H.mem p ∧ s.encode p ∈ A := by
  let E : Set P := {r | ∃ p ∈ A, ZFSet.pair (s.encode r) p ∈ s.conditionOrder}
  let raw := ZFSet.sep (fun r => ∃ p ∈ A, ZFSet.pair r p ∈ s.conditionOrder) s.carrier
  let formula : BoundedFormula 3 :=
    BoundedFormula.exMem 1 (BoundedFormula.pairMembershipFormula 1 0 3)
  let params := extend A (extend s.conditionOrder Fin.elim0)
  have selected := M.bounded_separation_mem separation formula params
    (Fin.cases hA (Fin.cases order (fun j => Fin.elim0 j))) carrier
  have rawGround : raw ∈ M.sets := by
    have equal : ZFSet.sep (fun r => BoundedFormula.Truth formula (extend r params)) s.carrier = raw := by
      apply ZFSet.ext
      intro r
      rw [ZFSet.mem_sep, ZFSet.mem_sep]
      apply and_congr_right
      intro _
      simp only [formula, BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
      rfl
    exact equal ▸ selected
  have code : s.subset (fun condition => condition ∈ E) = raw := by
    apply ZFSet.ext
    intro z
    rw [s.mem_subset, ZFSet.mem_sep]
    constructor
    · rintro ⟨r, member, rfl⟩
      exact ⟨s.encode_mem r, member⟩
    · rintro ⟨member, entry⟩
      obtain ⟨r, rfl⟩ := (s.mem_carrier z).1 member
      exact ⟨r, entry, rfl⟩
  have dense : Dense E := by
    intro q
    obtain ⟨p, hp, r, hr, rq, rp⟩ := predense (s.encode q) (s.encode_mem q)
    obtain ⟨r, rfl⟩ := (s.mem_carrier r).1 hr
    exact ⟨r, (s.pair_mem_conditionOrder r q).1 rq, p, hp, rp⟩
  obtain ⟨r, member, p, hp, below⟩ :=
    M.generic_meets_coded_dense s H generic (code.symm ▸ rawGround) dense
  obtain ⟨p, rfl⟩ := (s.mem_carrier p).1 (subset hp)
  exact ⟨p, H.upward member ((s.pair_mem_conditionOrder r p).1 below), hp⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
