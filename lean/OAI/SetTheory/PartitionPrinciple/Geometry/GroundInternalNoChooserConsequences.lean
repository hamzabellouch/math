import OAI.SetTheory.PartitionPrinciple.Models.GroundInternalRowChoice
import OAI.SetTheory.PartitionPrinciple.Models.GroundSupportedEqualityChoices

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (N : TransitiveGround.{u})

theorem ordinalSurjection_chooses_subsets
    (pairing : Realize N.sets SetFormula.pairing Fin.elim0)
    (unions : Realize N.sets SetFormula.union Fin.elim0)
    (powers : Realize N.sets powerSet Fin.elim0)
    (separation : SeparationSchema N.sets)
    {X T e : ZFSet.{u}} (hX : X ∈ N.sets) (hT : T ∈ N.sets)
    (he : e ∈ N.sets) (ordinal : ordinalSetProperty T)
    (function : ZFSet.IsFunc T X e)
    (covers : ∀ x ∈ X, ∃ i ∈ T, ZFSet.pair i x ∈ e) :
    ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ X → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧
        ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x := by
  let A := N.nonemptyGroundSubsets X
  have hA : A ∈ N.sets := N.nonemptyGroundSubsets_mem powers separation hX
  have meets : ∀ S ∈ A, ∃ i ∈ T, ∃ x ∈ S, ZFSet.pair i x ∈ e := by
    intro S member
    obtain ⟨_ground, subset, x, hx⟩ := (N.mem_nonemptyGroundSubsets X S).1 member
    obtain ⟨i, hi, edge⟩ := covers x (subset hx)
    exact ⟨i, hi, x, hx, edge⟩
  have code := ordinalIndexedChoiceGraph_choice ordinal ⟨X, function⟩ meets
  refine ⟨ordinalIndexedChoiceGraph A T e,
    N.ordinalIndexedChoiceGraph_mem pairing unions powers separation hA hT he, ?_⟩
  intro S hS subset nonempty
  have member : S ∈ A := (N.mem_nonemptyGroundSubsets X S).2 ⟨hS, subset, nonempty⟩
  obtain ⟨x, edge, unique⟩ := code.function.2 S member
  exact ⟨x, code.chosen S x edge, edge, fun z _ hz => unique z hz⟩

theorem noChooser_no_ordinal_surjection_not_choice
    (zf : ZFRealization N.sets) {X : ZFSet.{u}} (hX : X ∈ N.sets)
    (noChooser : ¬ ∃ f ∈ N.sets, ∀ S ∈ N.sets, S ⊆ X → S.Nonempty →
      ∃ x ∈ S, ZFSet.pair S x ∈ f ∧
        ∀ z ∈ S, ZFSet.pair S z ∈ f → z = x) :
    (¬ ∃ T ∈ N.sets, ordinalSetProperty T ∧
      ∃ e ∈ N.sets, ZFSet.IsFunc T X e ∧
        ∀ x ∈ X, ∃ i ∈ T, ZFSet.pair i x ∈ e) ∧
      ¬ Realize N.sets SetFormula.choice Fin.elim0 := by
  have pairing : Realize N.sets SetFormula.pairing Fin.elim0 := zf.1.2.2.2.1
  have unions : Realize N.sets SetFormula.union Fin.elim0 := zf.1.2.2.2.2.1
  have powers : Realize N.sets powerSet Fin.elim0 := zf.1.2.2.2.2.2.1
  constructor
  · rintro ⟨T, hT, ordinal, e, he, function, covers⟩
    exact noChooser (N.ordinalSurjection_chooses_subsets pairing unions powers zf.2.1
      hX hT he ordinal function covers)
  · intro choice
    exact noChooser (N.exists_function_choosing_subsets powers zf.2.1 choice hX)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
