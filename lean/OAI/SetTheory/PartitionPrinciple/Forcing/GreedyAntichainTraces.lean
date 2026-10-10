import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalFamilyShift

namespace OAI

namespace PartitionPilot.Forcing
universe u

def OrderAntichainCode (Q order D : ZFSet.{u}) : Prop :=
  D ⊆ Q ∧ ∀ p ∈ D, ∀ q ∈ D, ∀ r ∈ Q,
    ZFSet.pair r p ∈ order → ZFSet.pair r q ∈ order → p = q

theorem OrderAntichainCode.eq_of_common_lower {Q order D p q : ZFSet.{u}}
    (antichain : OrderAntichainCode Q order D) (first : p ∈ D) (second : q ∈ D)
    (common : ∃ r ∈ Q, ZFSet.pair r p ∈ order ∧ ZFSet.pair r q ∈ order) : p = q := by
  obtain ⟨r, member, belowFirst, belowSecond⟩ := common
  exact antichain.2 p first q second r member belowFirst belowSecond

def RelativeMaximalAntichainCode (Q order D A : ZFSet.{u}) : Prop :=
  A ⊆ D ∧ OrderAntichainCode Q order A ∧
    ∀ q ∈ D, ∃ p ∈ A, ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order

theorem RelativeMaximalAntichainCode.inclusion_maximal {Q order D A B : ZFSet.{u}}
    (code : RelativeMaximalAntichainCode Q order D A)
    (larger : A ⊆ B) (within : B ⊆ D) (antichain : OrderAntichainCode Q order B) :
    B ⊆ A := by
  intro q member
  obtain ⟨p, hp, common⟩ := code.2.2 q (within member)
  have equal := antichain.eq_of_common_lower member (larger hp) common
  exact equal.symm ▸ hp

noncomputable def antichainEligible (Q order D alpha prior : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun q => ¬ ∃ beta ∈ alpha, ∃ p ∈ D,
    ZFSet.pair beta p ∈ prior ∧ ∃ r ∈ Q,
      ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order) D

theorem mem_antichainEligible (Q order D alpha prior q : ZFSet.{u}) :
    q ∈ antichainEligible Q order D alpha prior ↔ q ∈ D ∧
      ¬ ∃ beta ∈ alpha, ∃ p ∈ D, ZFSet.pair beta p ∈ prior ∧
        ∃ r ∈ Q, ZFSet.pair r q ∈ order ∧ ZFSet.pair r p ∈ order :=
  ZFSet.mem_sep

def GreedyAntichainStep (Q order D F c alpha prior y : ZFSet.{u}) : Prop :=
  (∃ E ∈ F, E = antichainEligible Q order D alpha prior ∧ ZFSet.pair E y ∈ c) ∨
    (¬ (antichainEligible Q order D alpha prior).Nonempty ∧ y = D)

theorem greedyAntichainStep_selected {Q order D F c alpha prior y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c)
    (step : GreedyAntichainStep Q order D F c alpha prior y) (selected : y ∈ D) :
    y ∈ antichainEligible Q order D alpha prior := by
  rcases step with ⟨E, _, rfl, entry⟩ | ⟨_, equal⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (ZFSet.mem_irrefl D (equal ▸ selected))

theorem greedyAntichainStep_of_nonempty {Q order D F c alpha prior y : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c)
    (step : GreedyAntichainStep Q order D F c alpha prior y)
    (nonempty : (antichainEligible Q order D alpha prior).Nonempty) :
    y ∈ antichainEligible Q order D alpha prior := by
  rcases step with ⟨E, _, rfl, entry⟩ | ⟨empty, _⟩
  · exact choice.chosen _ _ entry
  · exact False.elim (empty nonempty)

theorem greedyAntichainTrace_antichain {Q order D F c C f S : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (conditions : D ⊆ Q) (subset : S ⊆ C) :
    OrderAntichainCode Q order (relationImage S D f) := by
  refine ⟨fun p hp => conditions ((mem_relationImage S D f p).1 hp).1, ?_⟩
  intro p hp q hq r hr rp rq
  obtain ⟨hpD, beta, hBeta, bp⟩ := (mem_relationImage S D f p).1 hp
  obtain ⟨hqD, gamma, hGamma, gq⟩ := (mem_relationImage S D f q).1 hq
  rcases ordinalSetProperty_mem_compare ordinal (subset hBeta) (subset hGamma) with
    before | equal | after
  · have eligible := greedyAntichainStep_selected choice
      (trace.2 gamma (subset hGamma) q gq) hqD
    exact False.elim ((mem_antichainEligible Q order D gamma
      (graphRestriction gamma f) q).1 eligible |>.2 <|
      ⟨beta, before, p, hpD, pair_mem_graphRestriction.2 ⟨bp, before⟩, r, hr, rq, rp⟩)
  · subst gamma
    exact trace.1.unique bp gq
  · have eligible := greedyAntichainStep_selected choice
      (trace.2 beta (subset hBeta) p bp) hpD
    exact False.elim ((mem_antichainEligible Q order D beta
      (graphRestriction beta f) p).1 eligible |>.2 <|
      ⟨gamma, after, q, hqD, pair_mem_graphRestriction.2 ⟨gq, after⟩, r, hr, rp, rq⟩)

theorem greedyAntichainTrace_injection {Q order D F c C f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (available : ∀ alpha ∈ C,
      (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty) :
    InjectionCode C D f := by
  have fresh : ∀ alpha ∈ C, ∀ y, ZFSet.pair alpha y ∈ f →
      y ∈ D ∧ ¬ ∃ beta ∈ alpha, ZFSet.pair beta y ∈ f := by
    intro alpha hAlpha y entry
    obtain ⟨hyD, eligible⟩ := (mem_antichainEligible Q order D alpha
      (graphRestriction alpha f) y).1
      (greedyAntichainStep_of_nonempty choice (trace.2 alpha hAlpha y entry)
        (available alpha hAlpha))
    refine ⟨hyD, ?_⟩
    rintro ⟨beta, hBeta, byEntry⟩
    have refl := orderCode.refl y (conditions hyD)
    exact eligible ⟨beta, hBeta, y, hyD, pair_mem_graphRestriction.2 ⟨byEntry, hBeta⟩,
      y, conditions hyD, refl, refl⟩
  refine ⟨⟨?_, trace.1.to_isFunc.2⟩, ?_⟩
  · intro z hz
    obtain ⟨alpha, hAlpha, y, rfl⟩ := trace.1.shape z hz
    exact ZFSet.pair_mem_prod.2 ⟨hAlpha, (fresh alpha hAlpha y hz).1⟩
  · intro alpha beta y first second
    have hAlpha := trace.1.pair_source first
    have hBeta := trace.1.pair_source second
    rcases ordinalSetProperty_mem_compare ordinal hAlpha hBeta with before | equal | after
    · exact False.elim ((fresh beta hBeta y second).2 ⟨alpha, before, first⟩)
    · exact equal
    · exact False.elim ((fresh alpha hAlpha y first).2 ⟨beta, after, second⟩)

theorem greedyAntichainTrace_exhausts {Q order D F c C f : ZFSet.{u}}
    (choice : ChoiceFunctionCode F c) (ordinal : ordinalSetProperty C)
    (trace : OrdinalRecursionTrace (GreedyAntichainStep Q order D F c) C f)
    (orderCode : PartialOrderCode Q order) (conditions : D ⊆ Q)
    (impossible : ¬ InjectionCode C D f) :
    ∃ alpha ∈ C,
      ¬ (antichainEligible Q order D alpha (graphRestriction alpha f)).Nonempty := by
  classical
  by_contra none
  apply impossible
  exact greedyAntichainTrace_injection choice ordinal trace orderCode conditions
    (fun alpha hAlpha => by
      by_contra empty
      exact none ⟨alpha, hAlpha, empty⟩)

end PartitionPilot.Forcing

end OAI
