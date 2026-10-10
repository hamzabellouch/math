import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift
import OAI.SetTheory.PartitionPrinciple.Models.GroundChoiceEnumerationSteps
import OAI.SetTheory.PartitionPrinciple.Models.GroundOrdinalPartitionInjectionAssembly

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem choiceEnumerationStep_fresh {A F c a p y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (step : ChoiceEnumerationStep A F c a p y)
    (nonempty : (enumerationRemainder A a p).Nonempty) :
    y ∈ enumerationRemainder A a p := by
  rcases step with ⟨R, _, rfl, entry⟩ | ⟨empty, _⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (empty nonempty)

theorem choiceEnumerationTrace_injection {A F c T f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty T)
    (trace : OrdinalRecursionTrace (ChoiceEnumerationStep A F c) T f)
    (unused : ∀ a ∈ T, (enumerationRemainder A a (graphRestriction a f)).Nonempty) :
    InjectionCode T A f := by
  have fresh : ∀ a ∈ T, ∀ y, ZFSet.pair a y ∈ f →
      y ∈ A ∧ ¬ ∃ b ∈ a, ZFSet.pair b y ∈ f := by
    intro a ha y entry
    have hy := (mem_enumerationRemainder A a (graphRestriction a f) y).1
      (choiceEnumerationStep_fresh choice (trace.2 a ha y entry) (unused a ha))
    exact ⟨hy.1, fun ⟨b, hb, byEntry⟩ =>
      hy.2 ⟨b, hb, pair_mem_graphRestriction.2 ⟨byEntry, hb⟩⟩⟩
  refine ⟨⟨?_, trace.1.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨a, ha, y, rfl⟩ := trace.1.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨ha, (fresh a ha y hz).1⟩
  · intro a b y first second
    have ha := trace.1.pair_source first
    have hb := trace.1.pair_source second
    rcases ordinalSetProperty_mem_compare ordinal ha hb with before | equal | after
    · exact False.elim ((fresh b hb y second).2 ⟨a, before, first⟩)
    · exact equal
    · exact False.elim ((fresh a ha y first).2 ⟨b, after, second⟩)

theorem exists_first_enumerationExhaustion {A T f : ZFSet.{u}}
    (ordinal : ordinalSetProperty T)
    (exhausted : ∃ a ∈ T, ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty) :
    ∃ a ∈ T, ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty ∧
      ∀ b ∈ a, (enumerationRemainder A b (graphRestriction b f)).Nonempty := by
  classical
  obtain ⟨a, ha, exhausted⟩ := exhausted
  induction a using ZFSet.inductionOn with
  | h a ih =>
    by_cases earlier : ∃ b ∈ a, ¬ (enumerationRemainder A b (graphRestriction b f)).Nonempty
    · obtain ⟨b, hb, empty⟩ := earlier
      exact ih b hb (ordinal.1 a ha b hb) empty
    · exact ⟨a, ha, exhausted, fun b hb => by
        by_contra empty
        exact earlier ⟨b, hb, empty⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem exists_groundOrdinalEnumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) :
    ∃ T ∈ M.sets, ∃ f ∈ M.sets, ordinalSetProperty T ∧ InjectionCode T A f ∧
      ∀ x ∈ A, ∃ a ∈ T, ZFSet.pair a x ∈ f := by
  classical
  let F := M.nonemptyGroundSubsets A
  have hF := M.nonemptyGroundSubsets_mem powers separation hA
  obtain ⟨c, hc, chooser⟩ := M.choice_witness choice hF
    (fun R hR => ((M.mem_nonemptyGroundSubsets A R).1 hR).2.2)
  obtain ⟨H, hH, ordinal, _, impossible⟩ := M.exists_groundHartogs
    pairing unions powers separation collection hA
  let params := extend A (extend F (extend c Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hA (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i)))
  let φ : BoundedFormula 6 := BoundedFormula.choiceEnumerationStepFormula 3 4 5 0 1 2
  have recognize (a p y : ZFSet.{u}) (ha : a ∈ M.sets) (hp : p ∈ M.sets)
      (hy : y ∈ M.sets) :
      Realize M.sets φ.toFormula (extend a (extend p (extend y params))) ↔
        ChoiceEnumerationStep A F c a p y :=
    (BoundedFormula.realize_toFormula M φ _
      (Fin.cases ha (Fin.cases hp (Fin.cases hy members)))).trans
      (BoundedFormula.truth_choiceEnumerationStepFormula 3 4 5 0 1 2 _)
  have closure : GroundOrdinalStepClosure M H φ.toFormula params := by
    intro a ha p hp _
    have haM := M.transitive hH ha
    obtain ⟨y, hy, relation, unique⟩ := M.choiceEnumerationStep_exists_unique
      separation hA haM hp chooser
    exact ⟨y, hy, (recognize a p y haM hp hy).2 relation,
      fun z hz step => unique z ((recognize a p z haM hp hz).1 step)⟩
  obtain ⟨f, hf, groundTrace⟩ := M.exists_ordinalRecursionTrace pairing unions separation
    collection hH ordinal φ.toFormula params members closure
  have trace : OrdinalRecursionTrace (ChoiceEnumerationStep A F c) H f := by
    refine ⟨groundTrace.1, ?_⟩
    intro a ha y entry
    have step := groundTrace.2 a ha y entry
    exact (recognize a _ y (M.transitive hH ha) step.1 step.2.1).1 step.2.2
  have exhausted : ∃ a ∈ H,
      ¬ (enumerationRemainder A a (graphRestriction a f)).Nonempty := by
    by_contra none
    apply impossible
    exact ⟨f, hf, choiceEnumerationTrace_injection chooser ordinal trace (fun a ha => by
      by_contra empty
      exact none ⟨a, ha, empty⟩)⟩
  obtain ⟨T, hT, empty, unused⟩ := exists_first_enumerationExhaustion ordinal exhausted
  have ordinalT := ordinalSetProperty_member ordinal hT
  have subset : T ⊆ H := fun a ha => ordinal.1 T hT a ha
  have hTM := M.transitive hH hT
  have restricted := trace.restrict ordinalT subset
  have injection : InjectionCode T A (graphRestriction T f) :=
    choiceEnumerationTrace_injection chooser ordinalT restricted (fun a ha => by
      rw [graphRestriction_restrict (fun b hb => ordinalT.1 a ha b hb)]
      exact unused a ha)
  refine ⟨T, hTM, graphRestriction T f,
    M.graphRestriction_mem unions separation hTM hf, ordinalT, injection, ?_⟩
  intro x hx
  by_contra missing
  apply empty
  refine ⟨x, (mem_enumerationRemainder _ _ _ _).2 ⟨hx, ?_⟩⟩
  exact missing

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula
private def enumerationPairFormula : SetFormula 2 :=
  ex (ex (.conj (orderedPairFormula 3 1 0)
    (.conj (BoundedFormula.ordinalFormula 1).toFormula
      (.conj (BoundedFormula.injectionFormula 1 2 0).toFormula
        (BoundedFormula.allMem 2 (BoundedFormula.exMem 2
          (BoundedFormula.pairMembershipFormula 0 1 2))).toFormula))))
end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
include pairing

private theorem enumerationPair_meaning (X z : ZFSet.{u}) (hX : X ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets enumerationPairFormula (extend X (extend z Fin.elim0)) ↔
      ∃ delta ∈ M.sets, ∃ f ∈ M.sets, z = ZFSet.pair delta f ∧
        ordinalSetProperty delta ∧ InjectionCode delta X f ∧
        ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ f := by
  rw [enumerationPairFormula, realize_ex]
  apply exists_congr
  intro delta
  apply and_congr_right
  intro hDelta
  rw [realize_ex]
  apply exists_congr
  intro f
  apply and_congr_right
  intro hf
  let env := extend f (extend delta (extend X (extend z Fin.elim0)))
  have members : ∀ i, env i ∈ M.sets :=
    Fin.cases hf (Fin.cases hDelta (Fin.cases hX (Fin.cases hz (fun j => Fin.elim0 j))))
  change (Realize M.sets (orderedPairFormula 3 1 0) env ∧
    Realize M.sets (BoundedFormula.ordinalFormula 1).toFormula env ∧
    Realize M.sets (BoundedFormula.injectionFormula 1 2 0).toFormula env ∧
    Realize M.sets (BoundedFormula.allMem 2 (BoundedFormula.exMem 2
      (BoundedFormula.pairMembershipFormula 0 1 2))).toFormula env) ↔ _
  rw [M.realize_orderedPairFormula pairing 3 1 0 env hz hDelta hf,
    BoundedFormula.realize_ordinalFormula M 1 env members,
    ← ordinalSetProperty_iff,
    BoundedFormula.realize_toFormula M _ env members,
    BoundedFormula.truth_injectionFormula,
    BoundedFormula.realize_toFormula M _ env members]
  simp only [BoundedFormula.Truth, BoundedFormula.truth_exMem, BoundedFormula.truth_pairMembershipFormula]
  rfl

theorem exists_groundOrdinalEnumerationFamily
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) :
    ∃ B ∈ M.sets, ∃ selected ∈ M.sets, ZFSet.IsFunc W B selected ∧
      ∀ X z, ZFSet.pair X z ∈ selected →
        ∃ delta ∈ M.sets, ∃ f ∈ M.sets, z = ZFSet.pair delta f ∧
          ordinalSetProperty delta ∧ InjectionCode delta X f ∧
          ∀ x ∈ X, ∃ i ∈ delta, ZFSet.pair i x ∈ f := by
  have total : ∀ X ∈ W, ∃ z ∈ M.sets,
      Realize M.sets enumerationPairFormula (extend X (extend z Fin.elim0)) := by
    intro X member
    have hX := M.transitive hW member
    obtain ⟨delta, hDelta, f, hf, ordinal, injection, onto⟩ :=
      M.exists_groundOrdinalEnumeration pairing unions powers separation collection choice hX
    have hz := M.orderedPair_mem pairing hDelta hf
    exact ⟨ZFSet.pair delta f, hz, (enumerationPair_meaning M pairing X _ hX hz).2
      ⟨delta, hDelta, f, hf, rfl, ordinal, injection, onto⟩⟩
  obtain ⟨B, hB, selected, ground, function, chosen⟩ := M.choose_definable_relation
    pairing unions powers separation collection choice enumerationPairFormula Fin.elim0
    (fun j => Fin.elim0 j) hW total
  refine ⟨B, hB, selected, ground, function, ?_⟩
  intro X z entry
  have shape := ZFSet.pair_mem_prod.1 (function.1 entry)
  exact (enumerationPair_meaning M pairing X z (M.transitive hW shape.1)
    (M.transitive hB shape.2)).1 (chosen X z entry)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
