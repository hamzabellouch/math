import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Initial
import OAI.Topology.ArtinGroups.Harmonic.PositiveEarlierLinkUpper

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable

noncomputable def earlierLinkSubtypeIso {P : Type*} [PartialOrder P]
    (r : P → P → Prop) (D : Set P) (v : D)
    (hD : ∀ x : WeightEarlierLink r v.val, x.val ∈ D) :
    WeightEarlierLink (fun a b : D => r a.val b.val) v ≃o WeightEarlierLink r v.val where
  toFun x := ⟨x.val.val,x.property⟩
  invFun x := ⟨⟨x.val,hD x⟩,x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by intros; rfl

variable {S : Type*} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
variable (z : M.Group) (hz : ∀ w, M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length z)
variable (inj : Function.Injective (positiveToArtin M))

theorem invariantPositive_contractible (D : Set (PositiveCellPoset M inj))
    (hroot : positiveRootCell M ∈ D)
    (hdown : ∀ {a b : PositiveCellPoset M inj}, a ≤ b → b ∈ D → a ∈ D)
    (hmatch : ∀ a : NoncriticalPositiveCell M, a.val ∈ D →
      (positiveMatch M z hz inj a).val ∈ D)
    (hupper : ∀ a : NoncriticalPositiveCell M, a.val ∈ D → matchingLetter M z hz a ∈ a.val.2.val →
      ContractibleSpace (OrderWeights {x : PositiveCellPoset M inj //
        positiveCellToLifted M x < positiveCellToLifted M a.val ∧
        x ≠ (positiveMatch M z hz inj a).val})) :
    ContractibleSpace (OrderWeights D) := by
  let r : D → D → Prop := fun a b => PositiveEarlier M z hz inj a.val b.val
  have wf : WellFounded r := InvImage.wf Subtype.val (positiveEarlier_wf M z hz inj)
  apply orderWeights_contractible_of_earlier_links r wf
    (fun a b hne => positiveEarlier_total M z hz inj a.val b.val
      (fun h => hne (Subtype.ext h))) ⟨positiveRootCell M,hroot⟩
    (fun a => positiveEarlier_root M z hz inj a.val)
  intro v hv
  have hv' : positiveCellTop M v.val ≠ 1 := by
    intro h
    apply hv
    exact Subtype.ext ((positiveCellTop_eq_one_iff M v.val).mp h)
  let a : NoncriticalPositiveCell M := ⟨v.val,hv'⟩
  by_cases hs : matchingLetter M z hz a ∈ a.val.2.val
  · let e := earlierLinkSubtypeIso (PositiveEarlier M z hz inj) D v (fun x => by
      have hh := (positiveEarlierLink_upper_iff M z hz inj a hs x.val).mp x.property
      exact hdown hh.1.le v.property)
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      ((weightHomeomorph (positiveEarlierLink_upper_iso M z hz inj a hs)).contractibleSpace_iff.mpr
        (hupper a v.property hs))
  · let b : D := ⟨(positiveMatch M z hz inj a).val,hmatch a v.property⟩
    have hab : v < b := positiveMatch_upper_lt M z hz inj a hs
    have hba : r b v := positiveMatch_before M z hz inj a hs
    let top : WeightEarlierLink r v := ⟨b,hba,Or.inr hab.le⟩
    have htop : ∀ x : WeightEarlierLink r v, x ≤ top := by
      intro x
      rcases x.property.2 with h|h
      · exact h.trans hab.le
      · have hne : v.val ≠ x.val.val := by
          intro he
          have hh := x.property.1
          change PositiveEarlier M z hz inj x.val.val v.val at hh
          rw [←he] at hh
          exact (positiveEarlier_wf M z hz inj).irrefl.irrefl _ hh
        obtain ⟨ha,_,he⟩ := positiveEarlier_upper_eq M z hz inj v.val x.val.val
          (lt_of_le_of_ne h hne) x.property.1
        change (x.val.val : PositiveCellPoset M inj) ≤ b.val
        exact le_of_eq he.symm
    let : OrderTop (WeightEarlierLink r v) := { top := top, le_top := htop }
    exact nerveWeightsHomeomorph.contractibleSpace_iff.mp
      (nerve_orderTop_contractible (WeightEarlierLink r v))

end HarmonicArtin

end OAI
