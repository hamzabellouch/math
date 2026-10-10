import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedAlignedReferenceCollisions

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

include group nodes supports hT closed in
theorem prepared_insertion_collision_forces (small : M.sets.Countable)
    (F B f : Fin 2 → ZFSet.{u}) (z y : Fin 2 → (M.nameDomain s).names) (p q : P)
    (profiles : ∀ i, F i ⊆ b.carrier) (bases : ∀ i, B i ⊆ F i)
    (coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
    (functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
    (supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
    (decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (z i).val p)
    (equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
      tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
      ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (z i).val tau)
    (h : G) (C K : L) (fixed : h ∈ d.principalFix C)
    (qp : q ≤ p) (qh : q ≤ a.iso h p)
    (good : ∀ i, b.encode C ∉ F i → b.encode K ∉ F i)
    (translatedSupport : ∀ i, d.principalFix K ≤ a.stabilizer s (y i).val)
    (translatedShape : ∀ i, (y i).val.val ⊆ ZFSet.prod T s.carrier)
    (profileTest : Forces (M.nameDomain s) refinementProfileFormula
      ![z 0, z 1, M.stageOneVisibilityName s valid a b d base directed system C] q) :
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (z 0), y 0, moved h (z 1), y 1] q →
    Forces (M.nameDomain s) refinementCollisionFormula ![z 0, y 0, z 1, y 1] q := by
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  dsimp only
  intro referenceTest
  let env : Assignment (M.nameDomain s) 4 := ![z 0, y 0, z 1, y 1]
  let reference : Assignment (M.nameDomain s) 4 := ![moved h (z 0), y 0, moved h (z 1), y 1]
  apply (M.ordinaryForces_iff_all_generics s small carrier refinementCollisionFormula env q).2
  intro H hq generic
  let N : TransitiveGround.{u} := ⟨(M.nameDomain s).values {r | H.mem r},
    (M.nameDomain s).values_transitive _⟩
  let vis (V : L) : (M.nameDomain s).names :=
    M.stageOneVisibilityName s valid a b d base directed system V
  have profileMeaning (i : Fin 2) (V : L) :
      b.encode V ∈ F i ↔ Name.eval {r | H.mem r} (z i).val ∈
        Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix V)) := by
    by_cases member : b.encode V ∈ F i
    · have positive : Forces (M.nameDomain s) (.mem 0 1 : SetFormula 2) ![z i, vis V] p :=
        (decisions i V).1 member
      have truth := forces_sound (M.nameDomain s) H generic (.mem 0 1 : SetFormula 2)
        ![z i, vis V] (H.upward hq qp) positive
      exact ⟨fun _ => truth, fun _ => member⟩
    · have negative : Forces (M.nameDomain s) (.neg (.mem 0 1) : SetFormula 2) ![z i, vis V] p :=
        (decisions i V).2 member
      have truth := forces_sound (M.nameDomain s) H generic (.neg (.mem 0 1) : SetFormula 2)
        ![z i, vis V] (H.upward hq qp) negative
      exact ⟨fun yes => False.elim (member yes), fun yes => False.elim (truth yes)⟩
  have pairProfile := (N.realize_refinementProfileFormula
    (evalAssignment {r | H.mem r} ![z 0, z 1, vis C])
    (fun i => ⟨(![z 0, z 1, vis C] : Assignment (M.nameDomain s) 3) i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementProfileFormula ![z 0, z 1, vis C]
      hq profileTest)
  change (Name.eval {r | H.mem r} (z 0).val ∈ Name.eval {r | H.mem r}
      (M.niceVisibilityName a s T (d.principalFix C)) ↔
    Name.eval {r | H.mem r} (z 1).val ∈ Name.eval {r | H.mem r}
      (M.niceVisibilityName a s T (d.principalFix C))) at pairProfile
  have pairMembers : b.encode C ∈ F 0 ↔ b.encode C ∈ F 1 :=
    (profileMeaning 0 C).trans (pairProfile.trans (profileMeaning 1 C).symm)
  have referenceCollision := (N.realize_refinementCollisionFormula
    (evalAssignment {r | H.mem r} reference) (fun i => ⟨reference i, rfl⟩)).1
    (forces_sound (M.nameDomain s) H generic refinementCollisionFormula reference hq referenceTest)
  change (Name.eval {r | H.mem r} (moved h (z 0)).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (moved h (z 1)).val = Name.eval {r | H.mem r} (y 1).val)
      at referenceCollision
  apply (N.realize_refinementCollisionFormula (evalAssignment {r | H.mem r} env)
    (fun i => ⟨env i, rfl⟩)).2
  change (Name.eval {r | H.mem r} (z 0).val = Name.eval {r | H.mem r} (y 0).val ↔
    Name.eval {r | H.mem r} (z 1).val = Name.eval {r | H.mem r} (y 1).val)
  by_cases member : b.encode C ∈ F 0
  · have both : ∀ i, b.encode C ∈ F i :=
      fun i => Fin.cases member (fun j => Fin.cases (pairMembers.1 member) (fun k => Fin.elim0 k) j) i
    have same (i : Fin 2) : Name.eval {r | H.mem r} (z i).val =
        Name.eval {r | H.mem r} (moved h (z i)).val := by
      have relative : h⁻¹ * 1 ∈ d.principalFix C := by
        simpa only [mul_one] using (d.principalFix C).inv_mem fixed
      have visible : Name.eval {r | H.mem r} (a.act s 1 (z i).val) ∈
          Name.eval {r | H.mem r} (M.niceVisibilityName a s T (d.principalFix (d.iso 1 C))) := by
        simpa only [a.act_one, d.one] using (profileMeaning i C).1 (both i)
      have result := M.preparedValue_eval_agreement a s t b d pairing unions powers separation
        collection carrier group nodes supports maps hT valid closed (F i) (B i) (f i) (z i)
        p q (profiles i) (bases i) (coinitial i) (functions i) (supported i) (decisions i)
        (equalities i) h 1 C relative (by simpa only [a.one] using qp) qh H generic hq visible
      simpa only [a.act_one, moved, stageOneNameAction_val] using result
    exact ⟨fun first => (same 1).trans (referenceCollision.1 ((same 0).symm.trans first)),
      fun second => (same 0).trans (referenceCollision.2 ((same 1).symm.trans second))⟩
  · have absent : ∀ i, b.encode C ∉ F i :=
      fun i => Fin.cases member (fun j => Fin.cases (fun yes => member (pairMembers.2 yes)) (fun k => Fin.elim0 k) j) i
    have different (i : Fin 2) : Name.eval {r | H.mem r} (z i).val ≠
        Name.eval {r | H.mem r} (y i).val := by
      intro equal
      have visible := system.normalization_visible K (y i) (translatedSupport i) H generic
        (Name.eval_subset_familySet_of_code_subset H T valid (y i).val (translatedShape i))
      exact good i (absent i) ((profileMeaning i K).2 (equal.symm ▸ visible))
    exact ⟨fun first => False.elim (different 0 first), fun second => False.elim (different 1 second)⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u

private theorem anchor_of_dataBound {L : Type u} [PartialOrder L]
    (b : Presentation L) (I level T S mu X tuples A : ZFSet.{u})
    (C E D : L) (U Rf Rc u w : ZFSet.{u})
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U Rf Rc) u w) (b.encode D) ∈
      stageOneDataBounds A I T S b.carrier mu X b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples) : E ≤ D := by
  obtain ⟨_, _, _, _, _, rawE, _, fu, _hfu, fw, _hfw, edge, lower, _rest⟩ :=
    (stageOneDataBounds_assignment_entry A I T S b.carrier mu X b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples _ u w (b.encode D)).1 bound
  have same : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier ![level, b.encode C, b.encode E, U, Rf, Rc]
      2 rawE).1 edge).2.2
  subst rawE
  exact (b.pair_mem_conditionOrder E D).1 lower

variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_insertion_reference
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA : ZFSet.{u})
    (h : G) (D K V C E : L) (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val ∈ T) (hw : w.val ∈ T)
    (source : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ sourceA)
    (newU newW : ZFSet.{u})
    (bound : ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      newU newW) (b.encode (d.iso h D)) ∈ stageOneDataBounds
        (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
          (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA)
        I T S b.carrier mu positions b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples)
    (cap : d.iso h D ≤ K) (avoid : E ≤ K → E ≤ V) (fixed : h ∈ d.principalFix V) :
    E ≤ V ∧
    refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∧
    ZFSet.pair (ZFSet.pair (t.encode h) (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val))
      (stageOneAssignment
        (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
        (a.act s h u).val (a.act s h w).val) ∈
      M.structuralAssignmentActionGraph t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history ∧
    stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      (a.act s h u).val (a.act s h w).val ∈
      M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA := by
  let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
  have below : E ≤ d.iso h D := anchor_of_dataBound b I level T S mu positions tuples image
    C E (d.iso h D) U.val.val Rf.val.val Rc.val.val newU newW bound
  have anchor := avoid (below.trans cap)
  have same := M.niceRefinementIndex_copies_agree a s b d level T T2 system.valid1 system.valid2
    system.indices C E U Rf Rc index 1 h V anchor (by simpa only [inv_one, one_mul] using fixed)
  simp only [d.one, a.act_one] at same
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let z := stageOneAssignment idx u.val w.val
  let target := stageOneAssignment idx (a.act s h u).val (a.act s h w).val
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2
  have branchMember : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact (stageOneAssignment_mem_assignments _ _ _ _ _).2 ⟨index, hu, hw⟩
  have graphEq := M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers
    separation collection carrier group nodes order system.inputs.condition_maps system.inputs.node_maps
    supports level T T2 hLevel hT system.valid1 system.valid2 system.inputs.terms_closed
    system.inputs.pairs_closed system.inputs.family_ground system.indices.index_ground
  have branch := (M.refinementAssignmentActionGraph_entry a s b d level T T2 system.valid1
    system.valid2 system.inputs.terms_closed t pairing unions powers separation collection carrier
    order system.inputs.condition_maps system.inputs.pairs_closed system.inputs.family_ground
    h C E U Rf Rc u w index hu hw target).2
      (congrArg (fun i => stageOneAssignment i (a.act s h u).val (a.act s h w).val) same.symm)
  rw [← graphEq h] at branch
  have edge := (M.structuralAssignmentActionGraph_branch_entry t.carrier b.carrier b.conditionOrder
    (supportBasisCode b t d.principalFix) T T2 (d.actionGraph b t) function stored
    branchMember (t.encode h) target).2 ⟨t.encode_mem h, branch⟩
  exact ⟨anchor, same, edge,
    (M.structuralAssignmentImage_entry t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA target).2
      ⟨z, source, edge⟩⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (level T T2 : ZFSet.{u})
variable (system : RefinementStageSystem M a s t b d base directed level T T2)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
include system pairing unions powers separation collection carrier order group nodes supports hLevel hT

theorem structuralAssignment_prepared_insertion_collision
    (small : M.sets.Countable)
    {stages history : ZFSet.{u}} (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤)
      (a.actionGraph s t)) ∈ history)
    (I S mu positions tuples sourceA : ZFSet.{u})
    (positionSupport : ∀ (D : L), ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu positions b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (h : G) (D K V C E : L) (U Rf Rc u w newU newW : (M.nameDomain s).names)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 system.valid1)
    (hu : u.val.val ∈ T) (hw : w.val.val ∈ T)
    (hNewU : newU.val.val ∈ T) (hNewW : newW.val.val ∈ T)
    (p q : P) (qp : q ≤ p) (qh : q ≤ a.iso h p)
    (fixed : h ∈ d.principalFix V) (cap : d.iso h D ≤ K)
    (avoid : E ≤ K → E ≤ V) (F B f e names : Fin 2 → ZFSet.{u})
    (good : ∀ i, b.encode V ∉ F i → b.encode K ∉ F i) :
    let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
    let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
      (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    stageOneAssignment idx u.val.val w.val.val ∈ sourceA →
    ZFSet.pair (stageOneAssignment idx newU.val.val newW.val.val) (b.encode (d.iso h D)) ∈
      stageOneDataBounds image I T S b.carrier mu positions b.conditionOrder
        (refinementIndexFieldGraph I b.carrier 2) tuples →
    stageOneRawTests M fields sourceA (s.encode p) → stageOneRawTests M fields image (s.encode q) →
    (∀ i : Fin 2, PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder)
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega ((![cls Rc u, cls Rf w] : Fin 2 → (M.nameDomain s).names) i).val.val
      (F i) (B i) (f i) (e i) (names i)) →
    E ≤ V ∧
    stageOneRawCollision M fields idx u.val.val newU.val.val w.val.val newW.val.val (s.encode q) ∧
    stageOneRawCollision M fields idx newU.val.val u.val.val newW.val.val w.val.val (s.encode q) := by
  let fields := M.refinementLevelFormulaData a s b d level T T2 system.valid1
  let image := M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
    (supportBasisCode b t d.principalFix) T T2 stages history (t.encode h) sourceA
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier system.inputs.condition_maps
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT system.valid1
  let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
  let original : Fin 2 → (M.nameDomain s).names := ![cls Rc u, cls Rf w]
  let translated : Fin 2 → (M.nameDomain s).names := ![cls Rc newU, cls Rf newW]
  dsimp only
  intro source bound sourceTests translatedTests certificates
  have reference := M.structuralAssignment_insertion_reference a s t b d base directed level T T2
    system pairing unions powers separation collection carrier order group nodes supports hLevel hT
    function stored I S mu positions tuples sourceA h D K V C E U Rf Rc u.val w.val index hu hw
    source newU.val.val newW.val.val bound cap avoid fixed
  have parts := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 reference.2.1
  have fine : moved h Rf = Rf := Subtype.ext (Subtype.ext parts.2.2.2.2.1)
  have coarse : moved h Rc = Rc := Subtype.ext (Subtype.ext parts.2.2.2.2.2)
  obtain ⟨newMember, _, _, _, _, rawE, _, fu, hfu, fw, hfw, anchorEdge, below,
      tu, tw, bu, bw⟩ :=
    (stageOneDataBounds_assignment_entry image I T S b.carrier mu positions b.conditionOrder
      (refinementIndexFieldGraph I b.carrier 2) tuples idx newU.val.val newW.val.val
      (b.encode (d.iso h D))).1 bound
  have sameAnchor : rawE = b.encode E :=
    ((refinementIndexFieldGraph_entry I b.carrier
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val] 2 rawE).1 anchorEdge).2.2
  have belowCap : E ≤ K := ((b.pair_mem_conditionOrder E (d.iso h D)).1 (sameAnchor ▸ below)).trans cap
  have positions : ∀ i : Fin 2, d.principalFix K ≤
      a.stabilizer s ((![newU, newW] : Fin 2 → (M.nameDomain s).names) i).val := by
    have first := le_trans (d.principalFix_antitone cap)
      (positionSupport (d.iso h D) fu hfu newU.val tu bu)
    have second := le_trans (d.principalFix_antitone cap)
      (positionSupport (d.iso h D) fw hfw newW.val tw bw)
    exact Fin.cases first (Fin.cases second (fun j => Fin.elim0 j))
  have classes := M.niceRefinementClasses_supported_by_block a s b d level T T2
    system.valid1 system.valid2 system.indices base directed system.inputs.terms_closed system.terms_hs
    C E K U Rf Rc index belowCap ![newU.val, newW.val]
      (Fin.cases (positions 0) (Fin.cases (positions 1) (fun j => Fin.elim0 j)))
  have single := (M.refinementLevelRawSingle_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT system.valid1 system.indices base directed system.first C E U Rf Rc u w index p).1
    (sourceTests.1 idx index u.val.val hu w.val.val hw source)
  have profile : Forces (M.nameDomain s) refinementProfileFormula
      ![original 0, original 1, M.stageOneVisibilityName s system.valid1 a b d base directed system.first V] q :=
    forces_mono (M.nameDomain s) _ _ (single.2.1 V reference.1) qp
  have referenceRaw := translatedTests.2 idx index
    (moved h u).val.val (system.inputs.terms_closed h u.val hu) newU.val.val hNewU
    (moved h w).val.val (system.inputs.terms_closed h w.val hw) newW.val.val hNewW
    reference.2.2.2 newMember
  have referenceTyped := (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation
    collection carrier order hT system.valid1 system.indices C E U Rf Rc
    (moved h u) newU (moved h w) newW index q).1 referenceRaw
  have classLaw (R v : (M.nameDomain s).names) : moved h (cls R v) = cls (moved h R) (moved h v) :=
    M.stageOneNameAction_class a s t pairing unions powers separation collection carrier
      system.inputs.condition_maps order hT system.valid1 system.inputs.terms_closed h R v
  have referenceFormula : Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (original 0), translated 0, moved h (original 1), translated 1] q := by
    change Forces (M.nameDomain s) refinementCollisionFormula
      ![moved h (cls Rc u), cls Rc newU, moved h (cls Rf w), cls Rf newW] q
    rw [classLaw Rc u, classLaw Rf w, fine, coarse]
    exact referenceTyped
  have recognized (i : Fin 2) := M.preparedCertificateCode_typed a s b T d.principalFix pairing unions powers
    separation collection carrier order hT system.valid1 system.first.visibility_graph_ground
    b.conditionOrder (canonicalMeetGraph b.carrier b.conditionOrder) ZFSet.omega
    (original i) p (F i) (B i) (f i) (e i) (names i) (certificates i)
  have forced := M.prepared_insertion_collision_forces a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps hT system.valid1 system.inputs.terms_closed
    base directed system.first small F B f original translated p q
    (fun i => (recognized i).1.subset) (fun i => (recognized i).2.1.1)
    (fun i => (recognized i).2.1.2) (fun i => (recognized i).2.2.2.1.1)
    (fun i => (recognized i).2.2.2.2.1) (fun i => (recognized i).2.2.2.2.2.1)
    (fun i => (recognized i).2.2.2.2.2.2) h V K fixed qp qh good
    (Fin.cases (classes 0).1 (Fin.cases (classes 1).1 (fun j => Fin.elim0 j)))
    (Fin.cases (Name.refinementClass_subset T system.valid1 Rc.val newU.val)
      (Fin.cases (Name.refinementClass_subset T system.valid1 Rf.val newW.val) (fun j => Fin.elim0 j)))
    profile referenceFormula
  have typed : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT system.valid1
      Rf Rc u newU w newW q := forced
  exact ⟨reference.1, M.refinementLevelRawCollision_both_orders s pairing unions powers separation collection
    carrier order hT system.valid1 a b d level T2 system.indices C E U Rf Rc u newU w newW index q typed⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
