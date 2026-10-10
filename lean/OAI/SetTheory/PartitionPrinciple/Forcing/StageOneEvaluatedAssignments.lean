import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneAssignmentUnions

namespace OAI

section

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

theorem stageOneCollisionTest_eval (Rf Rc u u' w w' : (M.nameDomain s).names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (test : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      Rf Rc u u' w w' p) :
    (Name.eval {q | H.mem q} (Name.refinementClass T valid Rc.val u.val) =
      Name.eval {q | H.mem q} (Name.refinementClass T valid Rc.val u'.val) ↔
    Name.eval {q | H.mem q} (Name.refinementClass T valid Rf.val w.val) =
      Name.eval {q | H.mem q} (Name.refinementClass T valid Rf.val w'.val)) :=
  M.refinementCollision_eval s _ H generic hp test

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneSingleTests_eval (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s)))
    {p : P} (hp : H.mem p)
    (tests : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p) :
    (Name.eval {q | H.mem q} u.val ∈ Name.eval {q | H.mem q} U.val ∧
      Name.eval {q | H.mem q} w.val ∈ Name.eval {q | H.mem q} U.val) ∧
    (∀ v : L, E ≤ v →
      (Name.eval {q | H.mem q} (Name.refinementClass T valid Rc.val u.val) ∈
        Name.eval {q | H.mem q} (M.niceVisibilityName a s T (d.principalFix v)) ↔
      Name.eval {q | H.mem q} (Name.refinementClass T valid Rf.val w.val) ∈
        Name.eval {q | H.mem q} (M.niceVisibilityName a s T (d.principalFix v)))) ∧
    (Name.eval {q | H.mem q} (Name.refinementClass T valid Rf.val w.val) ∈
        Name.eval {q | H.mem q} (M.niceVisibilityName a s T (d.principalFix C)) →
      ZFSet.pair (Name.eval {q | H.mem q} (Name.refinementClass T valid Rf.val w.val))
        (Name.eval {q | H.mem q} (Name.refinementClass T valid Rc.val u.val)) ∈
        Name.eval {q | H.mem q} (Name.refinementNaturalMap T valid U.val Rf.val Rc.val)) :=
  ⟨M.refinementActivity_eval s _ H generic hp tests.1,
    fun v hv => M.refinementProfile_eval s _ H generic hp (tests.2.1 v hv),
    M.refinementCompatibility_eval s _ H generic hp tests.2.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace Name
variable {P : Type u} [PartialOrder P] [OrderTop P] {s : Presentation P}

noncomputable def stageOneEvaluatedAssignments (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (H : Set P) (Rf Rc : Name s) (idx A : ZFSet.{u}) : ZFSet.{u} :=
    ZFSet.range (fun uv : {uv : ↥T × ↥T // stageOneAssignment idx uv.1.val uv.2.val ∈ A} =>
    ZFSet.pair
      (eval H (refinementClass T valid Rc ⟨uv.val.1.val, valid _ uv.val.1.property⟩))
      (eval H (refinementClass T valid Rf ⟨uv.val.2.val, valid _ uv.val.2.property⟩)))

theorem mem_stageOneEvaluatedAssignments (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (H : Set P) (Rf Rc : Name s) (idx A z : ZFSet.{u}) :
    z ∈ stageOneEvaluatedAssignments T valid H Rf Rc idx A ↔
      ∃ u : Name s, u.val ∈ T ∧ ∃ w : Name s, w.val ∈ T ∧
        stageOneAssignment idx u.val w.val ∈ A ∧
        z = ZFSet.pair (eval H (refinementClass T valid Rc u))
          (eval H (refinementClass T valid Rf w)) := by
  rw [stageOneEvaluatedAssignments, ZFSet.mem_range]
  constructor
  · rintro ⟨uv, equal⟩
    exact ⟨⟨uv.val.1.val, valid _ uv.val.1.property⟩, uv.val.1.property,
      ⟨uv.val.2.val, valid _ uv.val.2.property⟩, uv.val.2.property, uv.property, equal.symm⟩
  · rintro ⟨u, hu, w, hw, entry, equal⟩
    exact ⟨⟨(⟨u.val, hu⟩, ⟨w.val, hw⟩), entry⟩, equal.symm⟩

theorem pair_mem_stageOneEvaluatedAssignments (T : ZFSet.{u})
    (valid : ∀ z ∈ T, IsName s z) (H : Set P) (Rf Rc : Name s) (idx A x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ stageOneEvaluatedAssignments T valid H Rf Rc idx A ↔
      ∃ u : Name s, u.val ∈ T ∧ ∃ w : Name s, w.val ∈ T ∧
        stageOneAssignment idx u.val w.val ∈ A ∧
        x = eval H (refinementClass T valid Rc u) ∧
        y = eval H (refinementClass T valid Rf w) := by
  rw [mem_stageOneEvaluatedAssignments]
  simp only [ZFSet.pair_inj]

end Name
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem stageOneTests_partial_injection (T2 A : ZFSet.{u}) (p : P)
    (tests : M.stageOneTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system T2 A p)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily (M.nameDomain s))) (hp : H.mem p) :
    let graph := Name.stageOneEvaluatedAssignments T valid {q | H.mem q} Rf.val Rc.val
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) A
    PartialFunctionCode
      (Name.eval {q | H.mem q} (Name.refinementQuotient T valid U.val Rc.val))
      (Name.eval {q | H.mem q} (Name.refinementQuotient T valid U.val Rf.val)) graph ∧
      (∀ x x' y, ZFSet.pair x y ∈ graph → ZFSet.pair x' y ∈ graph → x = x') := by
  let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let hset : Set P := {q | H.mem q}
  have clauses := tests C E U Rf Rc member
  have active (u w : Name s) (hu : u.val ∈ T) (hw : w.val ∈ T)
      (entry : stageOneAssignment idx u.val w.val ∈ A) :
      Name.eval hset u ∈ Name.eval hset U.val ∧ Name.eval hset w ∈ Name.eval hset U.val := by
    have single := clauses.1 ⟨u, M.transitive hT hu⟩ ⟨w, M.transitive hT hw⟩ hu hw entry
    exact (M.stageOneSingleTests_eval s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc ⟨u, M.transitive hT hu⟩ ⟨w, M.transitive hT hw⟩
      H generic hp single).1
  have collide (u u' w w' : Name s) (hu : u.val ∈ T) (hu' : u'.val ∈ T)
      (hw : w.val ∈ T) (hw' : w'.val ∈ T)
      (entry : stageOneAssignment idx u.val w.val ∈ A)
      (entry' : stageOneAssignment idx u'.val w'.val ∈ A) :
      (Name.eval hset (Name.refinementClass T valid Rc.val u) =
        Name.eval hset (Name.refinementClass T valid Rc.val u') ↔
      Name.eval hset (Name.refinementClass T valid Rf.val w) =
        Name.eval hset (Name.refinementClass T valid Rf.val w')) := by
    exact M.stageOneCollisionTest_eval s pairing unions powers separation collection carrier order hT valid
      Rf Rc ⟨u, M.transitive hT hu⟩ ⟨u', M.transitive hT hu'⟩
      ⟨w, M.transitive hT hw⟩ ⟨w', M.transitive hT hw'⟩ H generic hp
      (clauses.2 _ _ _ _ hu hu' hw hw' entry entry')
  have familyGround := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  have forced := ((M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
    carrier order ∅ T T2 valid familyGround C E U Rf Rc).1 member).2.2.2.2
  have values := M.refinementObjects_eval s pairing carrier hT valid familyGround U Rf Rc
    H generic H.top_mem forced
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨u, hu, w, hw, entry, rfl⟩ :=
      (Name.mem_stageOneEvaluatedAssignments T valid hset Rf.val Rc.val idx A z).1 hz
    have inDomain := active u w hu hw entry
    rw [values.coarse_quotient, values.fine_quotient]
    apply ZFSet.pair_mem_prod.2
    constructor
    · rw [values.coarse_class u hu]
      exact Forcing.equivalenceClass_mem inDomain.1
    · rw [values.fine_class w hw]
      exact Forcing.equivalenceClass_mem inDomain.2
  · intro x y z first second
    obtain ⟨u, hu, w, hw, entry, xe, ye⟩ :=
      (Name.pair_mem_stageOneEvaluatedAssignments T valid hset Rf.val Rc.val idx A x y).1 first
    obtain ⟨u', hu', w', hw', entry', xe', ze⟩ :=
      (Name.pair_mem_stageOneEvaluatedAssignments T valid hset Rf.val Rc.val idx A x z).1 second
    exact ye.trans (((collide u u' w w' hu hu' hw hw' entry entry').1 (xe.symm.trans xe')).trans ze.symm)
  · intro x x' y first second
    obtain ⟨u, hu, w, hw, entry, xe, ye⟩ :=
      (Name.pair_mem_stageOneEvaluatedAssignments T valid hset Rf.val Rc.val idx A x y).1 first
    obtain ⟨u', hu', w', hw', entry', xe', ye'⟩ :=
      (Name.pair_mem_stageOneEvaluatedAssignments T valid hset Rf.val Rc.val idx A x' y).1 second
    exact xe.trans (((collide u u' w w' hu hu' hw hw' entry entry').2 (ye.symm.trans ye')).trans xe'.symm)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
