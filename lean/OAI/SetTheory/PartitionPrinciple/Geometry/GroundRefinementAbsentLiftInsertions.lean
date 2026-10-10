import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementVisibleLiftInsertions

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

include descent in
theorem stageOneSingleTests_absentLift_caps (small : M.sets.Countable)
    (C E K : L) (U Rf Rc u w : (M.nameDomain s).names) (F : ZFSet.{u})
    (p : P) (activeU : Name.ForcesMem p u.val U.val)
    (activeW : Name.ForcesMem p w.val U.val)
    (capPositive : ∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v)
    (capNegative : ∀ v : L, E ≤ v →
      b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T F (cls Rc u).val p →
    Name.ForcesMem p (cls Rf w).val (vis K).val →
    (∀ q, q ≤ p → ¬ Name.ForcesMem q (cls Rf w).val (vis C).val) →
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro decisions capVisible nonvisible
  have negativeC : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![cls Rf w, vis C] p := nonvisible
  refine ⟨⟨activeU, activeW⟩, ?_, ?_⟩
  · intro v above
    apply (M.ordinaryForces_iff_all_joint_generics s small carrier _ _ p).2
    intro H hp coded generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementProfileFormula _ (fun j => ⟨_, rfl⟩)).2
    have capSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense)
      (cls Rf w).property (vis K).property hp capVisible
    have notSeen : Name.eval {q | H.mem q} (cls Rf w).val ∉
        Name.eval {q | H.mem q} (vis C).val :=
      forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![cls Rf w, vis C] hp negativeC
    by_cases member : b.encode v ∈ F
    · have tested := (mem_testedMeetFilter F b.conditionOrder (b.encode E) (b.encode v)).2
        ⟨member, (b.pair_mem_conditionOrder E v).2 above⟩
      have fineSeen := (M.encode_mem_visibleSupportProfile a s b d T H _ v).1
        (M.visibleSupportProfile_upward a s b d T H _ (capPositive v tested)
          ((M.encode_mem_visibleSupportProfile a s b d T H _ K).2 capSeen))
      have coarsePositive : Forces (M.nameDomain s) (.mem 0 1) ![cls Rc u, vis v] p :=
        (decisions v).1 member
      have coarseSeen := forces_sound (M.nameDomain s) H generic (.mem 0 1)
        ![cls Rc u, vis v] hp coarsePositive
      exact ⟨fun _ => fineSeen, fun _ => coarseSeen⟩
    · have notTested : b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) :=
        fun yes => member ((mem_testedMeetFilter F b.conditionOrder (b.encode E) (b.encode v)).1 yes).1
      have coarseNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![cls Rc u, vis v] p :=
        (decisions v).2 member
      have coarseNotSeen := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1))
        ![cls Rc u, vis v] hp coarseNegative
      have fineNotSeen : Name.eval {q | H.mem q} (cls Rf w).val ∉
          Name.eval {q | H.mem q} (vis v).val := by
        intro fineSeen
        have bounded := Name.eval_subset_familySet_of_code_subset H T valid (cls Rf w).val
          (Name.refinementClass_subset T valid Rf.val w.val)
        have overlap := M.visibleSupportProfile_meet a s b d base directed T H valid system generic
          (cls Rf w) bounded meet (descent H coded generic) K v
          ((M.encode_mem_visibleSupportProfile a s b d T H _ K).2 capSeen)
          ((M.encode_mem_visibleSupportProfile a s b d T H _ v).2 fineSeen)
        rw [capNegative v above notTested] at overlap
        exact notSeen ((M.encode_mem_visibleSupportProfile a s b d T H _ C).1 overlap)
      exact ⟨fun yes => False.elim (coarseNotSeen yes), fun yes => False.elim (fineNotSeen yes)⟩
  · apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCompatibilityFormula _ (fun j => ⟨_, rfl⟩)).2
    intro seen
    exact False.elim ((forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1))
      ![cls Rf w, vis C] hp negativeC) seen)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P)
variable (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
  H.GenericFor (M.codedFamily s) →
  H.GenericFor (formulaFamily (M.nameDomain s)) →
  ∀ (v w : L) (x y : (M.nameDomain s).names),
    d.principalFix v ≤ a.stabilizer s x.val →
    d.principalFix w ≤ a.stabilizer s y.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) x.val →
    HereditarilySymmetric a s (d.principalSupportFamily base directed) y.val →
    Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
    ∃ tau : (M.nameDomain s).names,
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau.val ∧
      d.principalFix (meet v w) ≤ a.stabilizer s tau.val ∧
      Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val)

variable (small : M.sets.Countable)
include indices nodes small descent

theorem refinementLevelRawTests_insert_absentLift
    (C E K : L) (U Rf Rc u w : (M.nameDomain s).names) (F : ZFSet.{u})
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (activeU : Name.ForcesMem p u.val U.val) (activeW : Name.ForcesMem p w.val U.val)
    (capPositive : ∀ v : L, b.encode v ∈ testedMeetFilter F b.conditionOrder (b.encode E) → K ≤ v)
    (capNegative : ∀ v : L, E ≤ v →
      b.encode v ∉ testedMeetFilter F b.conditionOrder (b.encode E) → meet K v = C) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T F (cls Rc u).val p →
    Name.ForcesMem p (cls Rf w).val (vis K).val →
    (∀ q, q ≤ p → ¬ Name.ForcesMem q (cls Rf w).val (vis C).val) →
    (∀ (v z : (M.nameDomain s).names), v.val.val ∈ T → z.val.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A →
      (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) ∧
      ∃ profile, M.DecidesVisibilityProfile a s b d.principalFix T profile (cls Rf z).val p ∧
        (b.encode C ∉ profile → b.encode K ∉ profile)) →
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val.val w.val.val) A) (s.encode p) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro decisions capVisible nonvisible oldProfiles
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  have mixed (v z : (M.nameDomain s).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A) :
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc u v w z p ∧
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        Rf Rc v u z w p := by
    obtain ⟨different, profile, profileDecisions, survivor⟩ := oldProfiles v z hv hz old
    have facts := M.refinementAbsentLift_profile_collisions s carrier a b d valid base directed system
      pairing unions powers separation collection order hT small C K Rf Rc u v w z profile p p le_rfl
      profileDecisions survivor capVisible nonvisible different
    exact ⟨facts.2.2.1, facts.2.2.2.1⟩
  apply stageOneRawTests_insert M (M.refinementLevelFormulaData a s b d level T T2 valid) tests
  · exact (single C E U Rf Rc u w member p).2
      (M.stageOneSingleTests_absentLift_caps s pairing unions powers separation collection carrier order hT valid
        a b d base directed system meet descent small C E K U Rf Rc u w F p
        activeU activeW capPositive capNegative decisions capVisible nonvisible)
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc vn u zn w member p).2 (mixed vn zn hv hz old).2
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc u vn w zn member p).2 (mixed vn zn hv hz old).1
  · exact (collision C E U Rf Rc u u w w member p).2
      (M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
        small Rf Rc u w p)

end PartitionPilot.Forcing.TransitiveGround

end OAI
