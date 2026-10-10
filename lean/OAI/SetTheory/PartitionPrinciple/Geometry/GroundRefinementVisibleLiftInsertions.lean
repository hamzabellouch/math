import OAI.SetTheory.PartitionPrinciple.Geometry.GroundAbsentLiftRangeCollisions
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementRawTestMonotonicity

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
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (a : PosetAction G P) (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (terms : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include carrier in
private theorem visibility_forces_upward (small : M.sets.Countable)
    (z : (M.nameDomain s).names) (C v : L) (lower : C ≤ v) (p : P)
    (visible : Name.ForcesMem p z.val
      (M.stageOneVisibilityName s valid a b d base directed system C).val) :
    Name.ForcesMem p z.val
      (M.stageOneVisibilityName s valid a b d base directed system v).val := by
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  change Forces (M.nameDomain s) (.mem 0 1) ![z, vis v] p
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  have seen := Name.forcesMem_sound (M.nameDomain s) H
    (fun D hD dense => generic D (Or.inl hD) dense) z.property (vis C).property hp visible
  exact (M.encode_mem_visibleSupportProfile a s b d T H _ v).1
    (M.visibleSupportProfile_upward a s b d T H _ lower
      ((M.encode_mem_visibleSupportProfile a s b d T H _ C).2 seen))

include maps terms indices in
theorem refinementVisibleLift_forces_coarse_visibility (small : M.sets.Countable)
    (C E : L) (U Rf Rc fine coarse : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) :
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p fine.val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![fine, coarse, map] p →
    Name.ForcesMem p coarse.val (vis C).val := by
  dsimp only
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected
  change Forces (M.nameDomain s) (.mem 0 1) ![coarse, vis C] p
  apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
  intro H hp generic
  have seen := Name.forcesMem_sound (M.nameDomain s) H
    (fun D hD dense => generic D (Or.inl hD) dense) fine.property (vis C).property hp visible
  let evaluated : TransitiveGround.{u} :=
    ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
  have selectedTruth := forces_sound (M.nameDomain s) H generic
    (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![fine, coarse, map] hp selected
  have entry : ZFSet.pair (Name.eval {q | H.mem q} fine.val)
      (Name.eval {q | H.mem q} coarse.val) ∈ Name.eval {q | H.mem q} map.val :=
    (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)
  exact M.niceRefinementIndex_preserves_visibility s pairing unions powers separation collection
    carrier order a t maps b d base directed hT terms system indices C E U Rf Rc member
    le_rfl H generic seen entry

include maps terms indices in
theorem stageOneSingleTests_visible_lift (small : M.sets.Countable)
    (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (p : P) (activeU : Name.ForcesMem p u.val U.val)
    (activeW : Name.ForcesMem p w.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
  intro visible selected
  have coarseVisible := M.refinementVisibleLift_forces_coarse_visibility s pairing unions powers
    separation collection carrier order hT valid a t maps b d base directed terms system level indices
    small C E U Rf Rc (cls Rf w) (cls Rc u) member p visible selected
  have above := ((indices.typed_entries C E U Rf Rc).1 member).1.le
  refine ⟨⟨activeU, activeW⟩, ?_, ?_⟩
  · intro v hv
    have fineAbove := visibility_forces_upward M s carrier valid a b d base directed system
      small (cls Rf w) C v (above.trans hv) p visible
    have coarseAbove := visibility_forces_upward M s carrier valid a b d base directed system
      small (cls Rc u) C v (above.trans hv) p coarseVisible
    apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementProfileFormula _ (fun j => ⟨_, rfl⟩)).2
    have fineSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense) (cls Rf w).property (vis v).property hp fineAbove
    have coarseSeen := Name.forcesMem_sound (M.nameDomain s) H
      (fun D hD dense => generic D (Or.inl hD) dense) (cls Rc u).property (vis v).property hp coarseAbove
    exact ⟨fun _ => fineSeen, fun _ => coarseSeen⟩
  · apply (M.ordinaryForces_iff_all_generics s small carrier _ _ p).2
    intro H hp generic
    let evaluated : TransitiveGround.{u} :=
      ⟨(M.nameDomain s).values {q | H.mem q}, (M.nameDomain s).values_transitive _⟩
    apply (evaluated.realize_refinementCompatibilityFormula _ (fun j => ⟨_, rfl⟩)).2
    intro _
    have selectedTruth := forces_sound (M.nameDomain s) H generic
      (BoundedFormula.pairMembershipFormula 0 1 2).toFormula ![cls Rf w, cls Rc u, map] hp selected
    exact (BoundedFormula.truth_pairMembershipFormula 0 1 2 _).1
      ((BoundedFormula.realize_toFormula evaluated _ _ (fun j => ⟨_, rfl⟩)).1 selectedTruth)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

variable (M : TransitiveGround.{u}) (d : Fin 15 → ZFSet.{u})

theorem stageOneRawTests_insert {A lower t u w : ZFSet.{u}}
    (tests : stageOneRawTests M d A lower)
    (single : stageOneRawSingle M d t u w lower)
    (old_new : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w lower)
    (new_old : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z lower)
    (self : stageOneRawCollision M d t u u w w lower) :
    stageOneRawTests M d (insert (stageOneAssignment t u w) A) lower := by
  refine ⟨?_, ?_⟩
  · intro i hi v hv z hz entry
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v z t u w).1 equal
      exact single
    · exact tests.1 i hi v hv z hz old
  · intro i hi v hv v' hv' z hz z' hz' entry entry'
    rcases ZFSet.mem_insert_iff.1 entry with equal | old
    · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v z t u w).1 equal
      rcases ZFSet.mem_insert_iff.1 entry' with equal' | old'
      · obtain ⟨_, rfl, rfl⟩ := (stageOneAssignment_eq_iff _ _ _ _ _ _).1 equal'
        exact self
      · exact new_old v' hv' z' hz' old'
    · rcases ZFSet.mem_insert_iff.1 entry' with equal' | old'
      · obtain ⟨rfl, rfl, rfl⟩ := (stageOneAssignment_eq_iff i v' z' t u w).1 equal'
        exact old_new v hv z hz old
      · exact tests.2 i hi v hv v' hv' z hz z' hz' old old'

theorem stageOneRawTests_insert_iff {A lower t u w : ZFSet.{u}}
    (index : t ∈ d 0) (first : u ∈ d 6) (second : w ∈ d 6) :
    stageOneRawTests M d (insert (stageOneAssignment t u w) A) lower ↔
      stageOneRawTests M d A lower ∧
      stageOneRawSingle M d t u w lower ∧
      (∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
        stageOneRawCollision M d t v u z w lower) ∧
      (∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
        stageOneRawCollision M d t u v w z lower) ∧
      stageOneRawCollision M d t u u w w lower := by
  constructor
  · intro tests
    have added : stageOneAssignment t u w ∈ insert (stageOneAssignment t u w) A :=
      ZFSet.mem_insert _ _
    refine ⟨stageOneRawTests_transfer M d lower tests (fun _ _ _ _ _ _ h =>
      ZFSet.mem_insert_of_mem _ h), tests.1 t index u first w second added, ?_, ?_, ?_⟩
    · intro v hv z hz old
      exact tests.2 t index v hv u first z hz w second
        (ZFSet.mem_insert_of_mem _ old) added
    · intro v hv z hz old
      exact tests.2 t index u first v hv w second z hz added
        (ZFSet.mem_insert_of_mem _ old)
    · exact tests.2 t index u first u first w second w second added added
  · rintro ⟨tests, single, old_new, new_old, self⟩
    exact stageOneRawTests_insert M d tests single old_new new_old self

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

theorem assignmentCut_insert_current {J stages levels alpha z A : ZFSet.{u}}
    (function : ZFSet.IsFunc J stages levels)
    (level : ZFSet.pair z alpha ∈ levels) :
    assignmentCut levels alpha (insert z A) = assignmentCut levels alpha A := by
  apply ZFSet.ext
  intro x
  rw [mem_assignmentCut, mem_assignmentCut]
  constructor
  · rintro ⟨member, xi, hxi, entry⟩
    rcases ZFSet.mem_insert_iff.1 member with rfl | old
    · have hz := (ZFSet.pair_mem_prod.1 (function.1 level)).1
      obtain ⟨value, _, unique⟩ := function.2 _ hz
      have equal : xi = alpha := (unique xi entry).trans (unique alpha level).symm
      exact False.elim (ZFSet.mem_irrefl alpha (equal ▸ hxi))
    · exact ⟨old, xi, hxi, entry⟩
  · rintro ⟨member, below⟩
    exact ⟨ZFSet.mem_insert_of_mem _ member, below⟩

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem stageTwoConditions_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {rows I levels stages alpha row A t u w : ZFSet.{u}} (d : Fin 15 → ZFSet.{u})
    (function : ZFSet.IsFunc (stageOneAssignments I (d 6)) stages levels)
    (level : ZFSet.pair (stageOneAssignment t u w) alpha ∈ levels)
    (ground : stageOneAssignment t u w ∈ M.sets)
    (member : ZFSet.pair row A ∈ M.stageTwoConditions rows I levels alpha d)
    (single : stageOneRawSingle M d t u w (ZFSet.pair row (assignmentCut levels alpha A)))
    (old_new : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t v u z w (ZFSet.pair row (assignmentCut levels alpha A)))
    (new_old : ∀ v ∈ d 6, ∀ z ∈ d 6, stageOneAssignment t v z ∈ A →
      stageOneRawCollision M d t u v w z (ZFSet.pair row (assignmentCut levels alpha A)))
    (self : stageOneRawCollision M d t u u w w (ZFSet.pair row (assignmentCut levels alpha A))) :
    ZFSet.pair row (insert (stageOneAssignment t u w) A) ∈
      M.stageTwoConditions rows I levels alpha d ∧
    assignmentCut levels alpha (insert (stageOneAssignment t u w) A) =
      assignmentCut levels alpha A := by
  have cut := assignmentCut_insert_current function level (A := A)
  obtain ⟨hrow, hA, subset, small, lower, tests⟩ :=
    (M.pair_mem_stageTwoConditions rows I levels alpha d row A).1 member
  refine ⟨(M.pair_mem_stageTwoConditions rows I levels alpha d row _).2 ?_, cut⟩
  refine ⟨hrow, M.insert_mem pairing unions ground hA, ?_,
    M.groundEmbeddable_insert pairing unions powers separation infinite hA ground small, ?_, ?_⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with rfl | old
    · exact (ZFSet.pair_mem_prod.1 (function.1 level)).1
    · exact subset old
  · simpa only [cut] using lower
  · simpa only [cut] using stageOneRawTests_insert M d tests single old_new new_old self

end TransitiveGround

end PartitionPilot.Forcing




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
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
variable (small : M.sets.Countable)
variable (C E : L) (U R : (M.nameDomain s).names)
variable (member : (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) ∈ M.niceRefinementIndices a s b d level T T2 valid)
include pairing unions powers separation collection carrier order nodes hT indices system small member

theorem refinementLevelRawTests_insert_diagonal {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (diagonal : ∀ v ∈ T, ∀ z ∈ T, stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) v z ∈ A → v = z)
    (u : (M.nameDomain s).names) (term : u.val.val ∈ T)
    (active : Name.ForcesMem p u.val U.val) :
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) u.val.val u.val.val) A) (s.encode p) := by
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  apply stageOneRawTests_insert M (M.refinementLevelFormulaData a s b d level T T2 valid) (A := A) (lower := s.encode p) (t := (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val)) (u := u.val.val) (w := u.val.val) tests
  · have typed := M.stageOneSingleTests_diagonal s pairing unions powers separation collection carrier order hT valid
      small a b d base directed system C E U R u term p active
    have equiv := single C E U R R u u member p
    exact equiv.mpr typed
  · intro v hv z hz entry
    change v ∈ T at hv
    change z ∈ T at hz
    have equal := diagonal v hv z hz entry
    subst z
    let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    exact (collision C E U R R vName u vName u member p).2
      (M.stageOneCollisionTest_diagonal s pairing unions powers separation collection carrier order hT valid
        small R vName u p)
  · intro v hv z hz entry
    change v ∈ T at hv
    change z ∈ T at hz
    have equal := diagonal v hv z hz entry
    subst z
    let vName : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    exact (collision C E U R R u vName u vName member p).2
      (M.stageOneCollisionTest_diagonal s pairing unions powers separation collection carrier order hT valid
        small R u vName p)
  · exact (collision C E U R R u u u u member p).2
      (M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
        small R R u u p)

theorem refinementLevelRawTests_dense_diagonal {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (diagonal : ∀ v ∈ T, ∀ z ∈ T, stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) v z ∈ A → v = z)
    (nonempty : Forces (M.nameDomain s) (ex (.mem 0 1)) ![U] p) :
    DenseBelow p {q | ∃ u : (M.nameDomain s).names, u.val.val ∈ T ∧
      stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E) U.val.val R.val.val R.val.val) u.val.val u.val.val) A) (s.encode q)} := by
  have familyGround := M.familySet_mem s ⊤ pairing unions powers separation hT
    (M.transitive carrier (s.encode_mem ⊤)) valid
  have recognized := (M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
    carrier order level T T2 valid familyGround C E U R R).1 member
  have shape := ((M.name_mem_niceNameCandidates a s T (d.principalFix C) U.val).1 recognized.2.1).2.1
  have active := (forces_nonempty_iff_dense_activeTerms (M.nameDomain s) U T shape p).1 nonempty
  intro r below
  obtain ⟨q, qr, u, term, forced⟩ := active r below
  refine ⟨q, qr, u, term, ?_⟩
  exact M.refinementLevelRawTests_insert_diagonal a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system small C E U R member q
    (M.refinementLevelRawTests_mono a s b d level pairing unions powers separation collection
      carrier order nodes hT valid indices base directed system A tests (qr.trans below))
    diagonal u term forced

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
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
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (terms : ∀ g (sigma : Name s), sigma.val ∈ T → (a.act s g sigma).val ∈ T)
variable (small : M.sets.Countable)
include maps terms indices nodes small

theorem refinementLevelRawTests_insert_visibleLift
    (C E : L) (U Rf Rc u w : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (activeU : Name.ForcesMem p u.val U.val) (activeW : Name.ForcesMem p w.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    Name.ForcesMem p (cls Rf w).val (vis C).val →
    Forces (M.nameDomain s) (BoundedFormula.pairMembershipFormula 0 1 2).toFormula
      ![cls Rf w, cls Rc u, map] p →
    (∀ (v z : (M.nameDomain s).names), v.val.val ∈ T → z.val.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A →
      ∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
    stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) u.val.val w.val.val) A) (s.encode p) := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro visible mapped fresh
  have single := M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system
  have collision := M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices
  have mixed (v z : (M.nameDomain s).names) (hv : v.val.val ∈ T) (hz : z.val.val ∈ T)
      (old : stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A) :=
    M.refinementVisibleLift_collisions s pairing unions powers separation collection carrier order hT valid
      a b d level indices small C E U Rf Rc u v w z (vis C) member p visible mapped
      ((single C E U Rf Rc v z member p).1 (tests.1 _ member _ hv _ hz old)).2.2
      (fresh v z hv hz old)
  apply stageOneRawTests_insert M (M.refinementLevelFormulaData a s b d level T T2 valid) tests
  · exact (single C E U Rf Rc u w member p).2
      (M.stageOneSingleTests_visible_lift s pairing unions powers separation collection carrier order hT valid
        a t maps b d base directed terms system level indices small C E U Rf Rc u w member p
        activeU activeW visible mapped)
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc vn u zn w member p).2 (mixed vn zn hv hz old).2.2.1
  · intro v hv z hz old
    let vn : (M.nameDomain s).names := ⟨⟨v, valid v hv⟩, M.transitive hT hv⟩
    let zn : (M.nameDomain s).names := ⟨⟨z, valid z hz⟩, M.transitive hT hz⟩
    exact (collision C E U Rf Rc u vn w zn member p).2 (mixed vn zn hv hz old).2.1
  · exact (collision C E U Rf Rc u u w w member p).2
      (M.stageOneCollisionTest_self s pairing unions powers separation collection carrier order hT valid
        small Rf Rc u w p)

theorem refinementLevelRawTests_dense_visibleLift
    (C E : L) (U Rf Rc u : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    {A : ZFSet.{u}} (p : P)
    (tests : stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid) A (s.encode p))
    (active : Name.ForcesMem p u.val U.val) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let vis := M.stageOneVisibilityName s valid a b d base directed system
    let quotient : (M.nameDomain s).names := ⟨Name.refinementQuotient T valid U.val Rf.val,
      M.refinementQuotient_mem s pairing unions powers separation collection carrier order
        hT valid U.val Rf.val U.property Rf.property⟩
    let map := M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc
    (∀ (v z : (M.nameDomain s).names), v.val.val ∈ T → z.val.val ∈ T →
      stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val) v.val.val z.val.val ∈ A →
      ∀ q, q ≤ p → ¬ Name.ForcesEq q (cls Rc u).val (cls Rc v).val) →
    Forces (M.nameDomain s) refinementVisibleLiftFormula ![quotient, vis C, cls Rc u, map] p →
    DenseBelow p {q | ∃ w : (M.nameDomain s).names, w.val.val ∈ T ∧
      Name.ForcesMem q u.val U.val ∧ Name.ForcesMem q w.val U.val ∧
      stageOneRawTests M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (insert (stageOneAssignment (refinementIndexCode level (b.encode C) (b.encode E)
          U.val.val Rf.val.val Rc.val.val) u.val.val w.val.val) A) (s.encode q)} := by
  dsimp only
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let vis := M.stageOneVisibilityName s valid a b d base directed system
  intro fresh existsLift r rp
  obtain ⟨q, qr, w, hw, activeW, visible, mapped⟩ :=
    M.refinementVisibleLift_groundTerm_dense s pairing unions powers separation collection carrier order
      hT valid small U Rf Rc (vis C) (cls Rc u) p existsLift r rp
  have qp := qr.trans rp
  have activeU := Name.forcesMem_mono active qp
  refine ⟨q, qr, w, hw, activeU, activeW, ?_⟩
  exact M.refinementLevelRawTests_insert_visibleLift a s t b d level pairing unions powers separation
    collection carrier order nodes hT valid indices base directed system maps terms small C E U Rf Rc u w
    member q
    (M.refinementLevelRawTests_mono a s b d level pairing unions powers separation collection carrier order
      nodes hT valid indices base directed system A tests qp)
    activeU activeW visible mapped (fun v z hv hz old k kq => fresh v z hv hz old k (kq.trans qp))

end PartitionPilot.Forcing.TransitiveGround

end OAI
