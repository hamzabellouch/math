import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRefinementCollisionSymmetry
import OAI.SetTheory.PartitionPrinciple.Forcing.StageOneEvaluatedAssignments

namespace OAI

section


namespace PartitionPilot.Forcing.SetFormula

def refinementVisibleLiftFormula : SetFormula 4 :=
  ex (.conj (.mem 0 1) (.conj (.mem 0 2)
    (BoundedFormula.pairMembershipFormula 0 3 4).toFormula))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem refinementVisibleLift_groundTerm_dense (small : M.sets.Countable)
    (U Rf Rc visibility target : (M.nameDomain s).names) (p : P) :
    let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT valid U.val Rf.val U.property Rf.property⟩
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order
      hT valid U Rf Rc
    Forces (M.nameDomain s) refinementVisibleLiftFormula ![quotient, visibility, target, map] p →
    DenseBelow p {q | ∃ w : (M.nameDomain s).names, w.val.val ∈ T ∧
      Name.ForcesMem q w.val U.val ∧
      let fine := M.stageOneClassName s pairing unions powers separation collection carrier order
        hT valid Rf w
      Name.ForcesMem q fine.val visibility.val ∧
      Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
        ![fine, target, map] q} := by
  let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
    M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid U.val Rf.val U.property Rf.property⟩
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  let env : Assignment (M.nameDomain s) 4 := ![quotient, visibility, target, map]
  let phi : SetFormula 5 := .conj (.mem 0 2) (BoundedFormula.pairMembershipFormula 0 3 4).toFormula
  change Forces (M.nameDomain s) (ex (.conj (.mem 0 1) phi)) env p → _
  intro forced r rp
  obtain ⟨q, qr, rho, member, property⟩ :=
    (forces_ex_iff (M.nameDomain s) (.conj (.mem 0 1) phi) env p).1 forced r rp
  change Name.ForcesMem q rho.val quotient.val at member
  obtain ⟨v, vq, sigma, k, entry, vk, equal⟩ := member q le_rfl
  obtain ⟨w, hw, active, same⟩ :=
    (Name.entry_refinementQuotient T valid U.val Rf.val sigma k).1 entry
  let wName : (M.nameDomain s).names := ⟨w, M.transitive hT hw⟩
  let fine := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid Rf wName
  have sameFine : fine.val = sigma := same
  have equality : Name.ForcesEq v rho.val fine.val := sameFine.symm ▸ equal
  have propertyV : Forces (M.nameDomain s) phi (extend rho env) v :=
    forces_mono (M.nameDomain s) phi (extend rho env) property vq
  have selected : Forces (M.nameDomain s) phi (extend fine env) v :=
    (M.ordinaryForces_replace_first s small carrier phi env rho fine v equality).1 propertyV
  refine ⟨v, vq.trans qr, wName, hw, Name.forcesMem_mono active vk, ?_⟩
  exact selected

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

theorem refinementActiveTerm_fineLift (small : M.sets.Countable)
    (U Rf Rc u : (M.nameDomain s).names) (term : u.val.val ∈ T) (p : P)
    (active : Name.ForcesMem p u.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT valid U.val Rf.val U.property Rf.property⟩
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf u).val quotient.val ∧
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf u, cls Rc u, map] p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  have fineEntry := (Name.entry_refinementQuotient T valid U.val Rf.val _ p).2
    ⟨u.val, term, active, rfl⟩
  have mapEntry := (Name.entry_refinementNaturalMap T valid U.val Rf.val Rc.val _ p).2
    ⟨u.val, term, active, rfl⟩
  refine ⟨Name.forcesMem_entry fineEntry, ?_⟩
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  apply (BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).2
  apply (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).2
  have inMap := (Name.mem_eval {q | H.mem q} map.val _).2
    ⟨_, p, mapEntry, hp, rfl⟩
  rw [Name.eval_orderedPair {q | H.mem q} ⊤ H.top_mem] at inMap
  exact inMap

theorem refinementAbsentVisibleLift_nonvisible (small : M.sets.Countable)
    (U Rf Rc u visibility : (M.nameDomain s).names) (term : u.val.val ∈ T) (p : P)
    (active : Name.ForcesMem p u.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT valid U.val Rf.val U.property Rf.property⟩
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Forces (M.nameDomain s) (.neg refinementVisibleLiftFormula)
      ![quotient, visibility, cls Rc u, map] p →
    Name.ForcesMem p (cls Rf u).val quotient.val ∧
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf u, cls Rc u, map] p ∧
    (∀ q, q ≤ p → ¬ Name.ForcesMem q (cls Rf u).val visibility.val) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
    M.refinementQuotient_mem s pairing unions powers separation collection carrier order
      hT valid U.val Rf.val U.property Rf.property⟩
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro absent
  obtain ⟨member, mapped⟩ := M.refinementActiveTerm_fineLift s pairing unions powers separation collection
    carrier order hT valid small U Rf Rc u term p active
  refine ⟨member, mapped, ?_⟩
  intro q qp visible
  apply absent q qp
  apply (forces_ex_iff (M.nameDomain s) _ ![quotient, visibility, cls Rc u, map] q).2
  intro r rq
  refine ⟨r, le_rfl, cls Rf u, Name.forcesMem_mono member (rq.trans qp),
    Name.forcesMem_mono visible rq, ?_⟩
  exact forces_mono (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
    ![cls Rf u, cls Rc u, map] mapped (rq.trans qp)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (small : M.sets.Countable)

include small in
theorem stageOneCollisionTest_self (Rf Rc u w : (M.nameDomain s).names) (p : P) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w p := by
  unfold stageOneCollisionTest
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  apply (evaluated.realize_refinementCollisionFormula _ (fun j => ⟨_, rfl⟩)).2
  exact ⟨fun _ => rfl, fun _ => rfl⟩

include small in
theorem stageOneCollisionTest_diagonal (R u v : (M.nameDomain s).names) (p : P) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      R R u v u v p := by
  unfold stageOneCollisionTest
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  apply (evaluated.realize_refinementCollisionFormula _ (fun j => ⟨_, rfl⟩)).2
  exact Iff.rfl

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include small in
theorem stageOneSingleTests_diagonal (C E : L) (U R u : (M.nameDomain s).names)
    (term : u.val.val ∈ T) (p : P) (active : Name.ForcesMem p u.val U.val) :
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U R R u u p := by
  refine ⟨⟨active, active⟩, ?_, ?_⟩
  · intro v hv
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementProfileFormula _ (fun j => ⟨_, rfl⟩)).2
    exact Iff.rfl
  · apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCompatibilityFormula _ (fun j => ⟨_, rfl⟩)).2
    intro visible
    let cls := Name.refinementClass T valid R.val u.val
    change ZFSet.pair (Name.eval {q | H.mem q} cls) (Name.eval {q | H.mem q} cls) ∈
      Name.eval {q | H.mem q} (Name.refinementNaturalMap T valid U.val R.val R.val)
    apply (Name.mem_eval _ _ _).2
    refine ⟨Name.orderedPair ⊤ cls cls, p, ?_, hp, ?_⟩
    · exact (Name.entry_refinementNaturalMap T valid U.val R.val R.val _ p).2
        ⟨u.val, term, active, rfl⟩
    · exact Name.eval_orderedPair _ ⊤ H.top_mem cls cls

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (s : Presentation P) (carrier : s.carrier ∈ M.sets)
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T : ZFSet.{u}} (valid : ∀ z ∈ T, IsName s z)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include carrier in
theorem absentLift_profile_inequalities (small : M.sets.Countable)
    (C K : L) (moved old : (M.nameDomain s).names) (profile : ZFSet.{u})
    (r q : P) (below : q ≤ r)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T profile old.val r)
    (survivor : b.encode C ∉ profile → b.encode K ∉ profile) :
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    Name.ForcesMem q moved.val (vis K).val →
    (∀ p, p ≤ q → ¬ Name.ForcesMem p moved.val (vis C).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p moved.val old.val) ∧
    (∀ p, p ≤ q → ¬ Name.ForcesEq p old.val moved.val) := by
  dsimp only
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro visible absent
  have negative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![moved, old] q := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ q).2
    intro H hq generic same
    change Name.eval {p | H.mem p} moved.val = Name.eval {p | H.mem p} old.val at same
    classical
    by_cases atC : b.encode C ∈ profile
    · have oldVisible := Name.forcesMem_mono ((decisions C).1 atC) below
      have seen := Name.forcesMem_sound (M.nameDomain s) H
        (fun D hD dense => generic D (Or.inl hD) dense)
        old.property (vis C).property hq oldVisible
      have movedNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![moved, vis C] q := absent
      have unseen : Name.eval {p | H.mem p} moved.val ∉ Name.eval {p | H.mem p} (vis C).val :=
        forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![moved, vis C] hq movedNegative
      exact unseen (same.symm ▸ seen)
    · have oldNegative : Forces (M.nameDomain s) (.neg (.mem 0 1)) ![old, vis K] q :=
        fun p pq => (decisions K).2 (survivor atC) p (pq.trans below)
      have unseen : Name.eval {p | H.mem p} old.val ∉ Name.eval {p | H.mem p} (vis K).val :=
        forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1)) ![old, vis K] hq oldNegative
      have seen := Name.forcesMem_sound (M.nameDomain s) H
        (fun D hD dense => generic D (Or.inl hD) dense)
        moved.property (vis K).property hq visible
      exact unseen (same ▸ seen)
  exact ⟨negative, fun p pq equal => negative p pq (Name.forcesEq_symm equal)⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (order : s.conditionOrder ∈ M.sets) (hT : T ∈ M.sets)

theorem refinementAbsentLift_profile_collisions (small : M.sets.Countable)
    (C K : L) (Rf Rc u oldU w oldW : (M.nameDomain s).names)
    (profile : ZFSet.{u}) (r q : P) (below : q ≤ r) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    M.DecidesVisibilityProfile a s b d.principalFix T profile (cls Rf oldW).val r →
    (b.encode C ∉ profile → b.encode K ∉ profile) →
    Name.ForcesMem q (cls Rf w).val (vis K).val →
    (∀ p, p ≤ q → ¬ Name.ForcesMem p (cls Rf w).val (vis C).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rc u).val (cls Rc oldU).val) →
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rf w).val (cls Rf oldW).val) ∧
    (∀ p, p ≤ q → ¬ Name.ForcesEq p (cls Rf oldW).val (cls Rf w).val) ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc oldU u oldW w q ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w q := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  intro decisions survivor visible absent coarseDifferent
  obtain ⟨fineDifferent, fineDifferent'⟩ := M.absentLift_profile_inequalities s carrier a b d valid
    base directed system small C K (cls Rf w) (cls Rf oldW) profile r q below
    decisions survivor visible absent
  have collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q := by
    constructor
    · intro p pq facts
      exact coarseDifferent p pq facts.1
    · intro p pq facts
      exact fineDifferent p pq facts.1
  exact ⟨fineDifferent, fineDifferent', collision,
    M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u oldU w oldW q collision,
    M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
      small Rf Rc u w q⟩

end PartitionPilot.Forcing.TransitiveGround




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
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementVisibleLift_collisions (small : M.sets.Countable)
    (C E : L) (U Rf Rc u v w oldW visibility : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val visibility.val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    Forces (M.nameDomain s) refinementCompatibilityFormula
      ![cls Rf oldW, visibility, cls Rc v, map] p →
    (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
    (∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rf w).val (cls Rf oldW).val) ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc v u oldW w p ∧
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u w w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected oldGuard different
  have coarseNegative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![cls Rc u, cls Rc v] p := different
  have values (H : ConditionFilter P) (hp : H.mem p)
      (generic : H.GenericFor (formulaFamily (M.nameDomain s))) :
      Name.eval {q | H.mem q} (cls Rc u).val ≠ Name.eval {q | H.mem q} (cls Rc v).val ∧
      Name.eval {q | H.mem q} (cls Rf w).val ≠ Name.eval {q | H.mem q} (cls Rf oldW).val := by
    have coarseDifferent : Name.eval {q | H.mem q} (cls Rc u).val ≠
        Name.eval {q | H.mem q} (cls Rc v).val :=
      forces_sound (M.nameDomain s) H generic (.neg (.equal 0 1)) ![cls Rc u, cls Rc v] hp coarseNegative
    refine ⟨coarseDifferent, ?_⟩
    intro sameFine
    have visibleValue := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense)
      (cls Rf w).property visibility.property hp visible
    have oldVisible : Name.eval {q | H.mem q} (cls Rf oldW).val ∈
        Name.eval {q | H.mem q} visibility.val := sameFine ▸ visibleValue
    have oldEntry := M.refinementCompatibility_eval s
      ![cls Rf oldW, visibility, cls Rc v, map] H generic hp oldGuard oldVisible
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    have selectedTruth := forces_sound (M.nameDomain s) H generic
      (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![cls Rf w, cls Rc u, map] hp selected
    have selectedEntry : ZFSet.pair (Name.eval {q | H.mem q} (cls Rf w).val)
        (Name.eval {q | H.mem q} (cls Rc u).val) ∈ Name.eval {q | H.mem q} map.val :=
      (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
        ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)
    obtain ⟨_, _, _, _, forced⟩ := (indices.typed_entries C E U Rf Rc).1 member
    have objects := M.refinementObjects_eval s pairing carrier hT valid indices.family_ground
      U Rf Rc H generic H.top_mem forced
    have oldEntry' : ZFSet.pair (Name.eval {q | H.mem q} (cls Rf w).val)
        (Name.eval {q | H.mem q} (cls Rc v).val) ∈ Name.eval {q | H.mem q} map.val :=
      sameFine.symm ▸ oldEntry
    exact coarseDifferent ((functionCode_partial objects.function).unique _ _ _ selectedEntry oldEntry')
  have fineNegative : Forces (M.nameDomain s) (.neg (.equal 0 1)) ![cls Rf w, cls Rf oldW] p := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    exact (values H hp generic).2
  have collision : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p := by
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCollisionFormula _ (fun j => ⟨_, rfl⟩)).2
    have differentValues := values H hp generic
    exact ⟨fun eq => False.elim (differentValues.1 eq), fun eq => False.elim (differentValues.2 eq)⟩
  exact ⟨fineNegative, collision,
    M.stageOneCollisionTest_symm s pairing unions powers separation collection carrier order hT valid
      Rf Rc u v w oldW p collision,
    M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
      small Rf Rc u w p⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
