import OAI.SetTheory.PartitionPrinciple.Geometry.StructuralPreparationSourceImages

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable (T : ZFSet.{u})
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
include pairing unions powers separation collection carrier maps closed

theorem groundRelations_act_mem (g : G) (z : Name s)
    (member : z.val ∈ M.groundRelations T s.carrier) :
    (a.act s g z).val ∈ M.groundRelations T s.carrier := by
  obtain ⟨ground, subset⟩ := (M.mem_groundRelations T s.carrier z.val).1 member
  refine (M.mem_groundRelations T s.carrier _).2
    ⟨M.act_mem s a t pairing unions powers separation collection carrier maps g z ground, ?_⟩
  intro x hx
  obtain ⟨sigma, q, rfl⟩ := Name.entries_cover (a.act s g z) hx
  obtain ⟨tau, p, entry, moved, _condition⟩ :=
    (Name.entry_rename s (a.iso g) z sigma q).1 hx
  have child := closed g tau (ZFSet.pair_mem_prod.1 (subset entry)).1
  have same : a.act s g tau = sigma := moved
  exact ZFSet.pair_mem_prod.2 ⟨same ▸ child, s.encode_mem q⟩

theorem groundRelations_nameAction_ground_function
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) (g : G) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    Name.renameFamilyGraph s (a.iso g) N validN ∈ M.sets ∧
      ZFSet.IsFunc N N (Name.renameFamilyGraph s (a.iso g) N validN) := by
  dsimp only
  refine ⟨M.renameFamilyGraph_mem s s pairing unions powers separation collection carrier carrier
    (a.iso g) (M.conditionMap_graph_mem a s t maps g) _
    (M.groundRelations_mem pairing unions powers separation hT carrier) _, ?_⟩
  exact Name.renameFamilyGraph_act_function a s _ _ g
    (M.groundRelations_act_mem a s t pairing unions powers separation collection carrier maps T closed g)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
include pairing unions powers separation collection members valid2

theorem niceAssignmentClassGraphs_function {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (shape : A ⊆ stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T)
    (side : Fin 2) :
    ZFSet.IsFunc A (M.groundRelations T s.carrier)
      (M.niceAssignmentClassGraphs a s b d level T T2 valid A side) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    unfold niceAssignmentClassGraphs assignmentClassGraph at hz
    exact (ZFSet.mem_sep.1 hz).1
  · intro x hx
    obtain ⟨i, hi, rawU, hu, rawW, hw, rfl⟩ :=
      (mem_stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T x).1 (shape hx)
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
      M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
    let u : Name s := ⟨rawU, valid rawU hu⟩
    let w : Name s := ⟨rawW, valid rawW hw⟩
    let R : Name s := Fin.cases Rc.val (fun _ => Rf.val) side
    let v : Name s := Fin.cases u (fun _ => w) side
    let z := Name.refinementClass T valid R v
    have lookup := M.niceAssignmentClassGraphs_entry a s b d level T T2 valid
      pairing unions powers separation collection members hA C E U Rf Rc hi u w hu hw hx side
    exact ⟨z.val, (lookup z.val).2 rfl, fun y edge => (lookup y).1 edge⟩

variable (t : Presentation G)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (closed2 : ∀ g (z : Name s), z.val ∈ T2 → (a.act s g z).val ∈ T2)
include maps closed closed2

theorem niceAssignmentClassGraphs_act_entry
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (g : G)
    (hImage : M.refinementAssignmentImage a s b d level T T2 valid valid2 g A ∈ M.sets)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (idx : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid)
    (u w : Name s) (hu : u.val ∈ T) (hw : w.val ∈ T)
    (member : stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val ∈ A) (side : Fin 2) (z : Name s) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val) (a.act s g z).val ∈
        M.niceAssignmentClassGraphs a s b d level T T2 valid
          (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) side ↔
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val w.val) z.val ∈ M.niceAssignmentClassGraphs a s b d level T T2 valid A side := by
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation (members 6) (members 9) valid
  let move (v : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨a.act s g v.val, M.act_mem s a t pairing unions powers separation collection carrier maps g v.val v.property⟩
  have movedIdx := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation
    collection carrier order maps level T T2 valid closed closed2 family g C E U Rf Rc).2 idx
  have movedMember := (M.refinementAssignmentImage_entry a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 family
    g C E U Rf Rc u w idx hu hw A).2 member
  have oldEntry := M.niceAssignmentClassGraphs_entry a s b d level T T2 valid
    pairing unions powers separation collection members hA C E U Rf Rc idx u w hu hw member side z.val
  have newEntry := M.niceAssignmentClassGraphs_entry a s b d level T T2 valid
    pairing unions powers separation collection members hImage (d.iso g C) (d.iso g E)
    (move U) (move Rf) (move Rc) movedIdx (a.act s g u) (a.act s g w)
    (closed g u hu) (closed g w hw) movedMember side (a.act s g z).val
  rw [newEntry, oldEntry]
  have equivariant :
      a.act s g (Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name s) Rc.val (fun _ => Rf.val) side)
        (Fin.cases (motive := fun _ => Name s) u (fun _ => w) side)) =
      Name.refinementClass T valid
        (Fin.cases (motive := fun _ => Name s) (move Rc).val (fun _ => (move Rf).val) side)
        (Fin.cases (motive := fun _ => Name s) (a.act s g u) (fun _ => a.act s g w) side) := by
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)) side
    · exact Name.act_refinementClass a T valid closed g Rc.val u
    · exact Name.act_refinementClass a T valid closed g Rf.val w
  rw [← equivariant]
  constructor
  · intro equal
    exact congrArg Subtype.val ((a.nameEquiv s g).injective (Subtype.ext equal))
  · intro equal
    exact congrArg (fun v : Name s => (a.act s g v).val) (Subtype.ext equal)

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (closed2 : ∀ g (z : Name s), z.val ∈ T2 → (a.act s g z).val ∈ T2)
include pairing unions powers separation collection members maps nodeMaps closed closed2

theorem niceAssignmentClassImage_act (hLevel : level ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets)
    (shape : A ⊆ stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T)
    (g : G) (side : Fin 2) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    relationImage
      (relationImage A N (M.niceAssignmentClassGraphs a s b d level T T2 valid A side)) N
      (Name.renameFamilyGraph s (a.iso g) N validN) =
    relationImage (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) N
      (M.niceAssignmentClassGraphs a s b d level T T2 valid
        (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) side) := by
  dsimp only
  let N := M.groundRelations T s.carrier
  let validN : ∀ z ∈ N, IsName s z := fun z hz =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation (members 6) (members 9) valid
  have hGraph := M.refinementAssignmentActionGraph_mem a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier maps nodeMaps hLevel (members 6) hT2 (members 0) g
  have hImage := M.relationImage_mem separation hA
    (M.stageOneAssignments_mem pairing unions powers separation (members 0) (members 6)) hGraph
  have action := M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 family g
  have source := M.niceAssignmentClassGraphs_function a s b d level T T2 valid valid2
    pairing unions powers separation collection members hA shape side
  have moved := M.niceAssignmentClassGraphs_function a s b d level T T2 valid valid2
    pairing unions powers separation collection members hImage
    (M.refinementAssignmentImage_subset a s b d level T T2 valid valid2 g A) side
  have names := M.groundRelations_nameAction_ground_function a s t
    pairing unions powers separation collection carrier maps T closed (members 6) valid g
  refine relationImage_commuting_square source moved ?_ names.2 ?_
  · intro x hx
    obtain ⟨y, edge, _⟩ := action.2 x (shape hx)
    exact ⟨y, (ZFSet.pair_mem_prod.1 (action.1 edge)).2, edge⟩
  · intro x hx y x' y' requested acted renamed
    have hy : y ∈ N := (ZFSet.pair_mem_prod.1 (source.1 requested)).2
    let z : Name s := ⟨y, validN y hy⟩
    have movedY : y' = (a.act s g z).val :=
      ((Name.pair_mem_renameFamilyGraph s (a.iso g) N validN z y').1 renamed).2
    obtain ⟨i, hi, rawU, hu, rawW, hw, rfl⟩ :=
      (mem_stageOneAssignments (M.niceRefinementIndices a s b d level T T2 valid) T x).1 (shape hx)
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
      M.exists_niceRefinementIndex_fields a s b d level T T2 valid valid2 hi
    let u : Name s := ⟨rawU, valid rawU hu⟩
    let w : Name s := ⟨rawW, valid rawW hw⟩
    have movedX := (M.refinementAssignmentActionGraph_entry a s b d level T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 family
      g C E U Rf Rc u w hi hu hw x').1 acted
    rw [movedX, movedY]
    exact (M.niceAssignmentClassGraphs_act_entry a s b d level T T2 valid valid2
      pairing unions powers separation collection members t maps closed closed2
      hA g hImage C E U Rf Rc hi u w hu hw hx side z).2 requested

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (closed2 : ∀ g (z : Name s), z.val ∈ T2 → (a.act s g z).val ∈ T2)
include pairing unions powers separation collection members maps nodeMaps closed closed2

theorem storedPreparationRequests_act (hLevel : level ∈ M.sets) (hT2 : T2 ∈ M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (g : G) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    relationImage
      (M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid)) N
      (Name.renameFamilyGraph s (a.iso g) N validN) =
    M.storedPreparationRequests (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A)
      (M.refinementLevelFormulaData a s b d level T T2 valid) := by
  dsimp only
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let selected := assignmentOnIndices I T A
  have selectedGround : selected ∈ M.sets := M.assignmentOnIndices_mem pairing unions powers separation
    (members 0) (members 6) hA
  have selectedShape : selected ⊆ stageOneAssignments I T :=
    fun z hz => ((mem_assignmentOnIndices I T A z).1 hz).2
  have selectedImage : assignmentOnIndices I T
      (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) =
      M.refinementAssignmentImage a s b d level T T2 valid valid2 g A := by
    apply ZFSet.ext
    intro z
    rw [mem_assignmentOnIndices]
    exact and_iff_left_of_imp
      (fun hz => M.refinementAssignmentImage_subset a s b d level T T2 valid valid2 g A hz)
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation (members 6) (members 9) valid
  have action := M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 family g
  have imageSelected : M.refinementAssignmentImage a s b d level T T2 valid valid2 g selected =
      M.refinementAssignmentImage a s b d level T T2 valid valid2 g A :=
    (relationImage_source_selection action A).symm
  have first := M.niceAssignmentClassImage_act a s b d level T T2 valid valid2 t
    pairing unions powers separation collection members maps nodeMaps closed closed2
    hLevel hT2 selectedGround selectedShape g 0
  have second := M.niceAssignmentClassImage_act a s b d level T T2 valid valid2 t
    pairing unions powers separation collection members maps nodeMaps closed closed2
    hLevel hT2 selectedGround selectedShape g 1
  dsimp only at first second
  rw [imageSelected] at first second
  rw [M.storedPreparationRequests_typed, M.storedPreparationRequests_typed]
  dsimp only
  rw [selectedImage, relationImage_source_union]
  exact congrArg₂ (fun left right : ZFSet.{u} => left ∪ right) first second

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (members : ∀ j : Fin 15, (M.refinementLevelFormulaData a s b d level T T2 valid) j ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)
variable (closed2 : ∀ g (z : Name s), z.val ∈ T2 → (a.act s g z).val ∈ T2)
include pairing unions powers separation collection members maps nodeMaps group nodes supports closed closed2 valid2

theorem structuralAssignmentImage_selection_eq_refinement
    (hLevel : level ∈ M.sets) {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level
      (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)) ∈ history)
    (A : ZFSet.{u}) (g : G) :
    assignmentOnIndices (M.niceRefinementIndices a s b d level T T2 valid) T
      (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A) =
    M.refinementAssignmentImage a s b d level T T2 valid valid2 g A := by
  let I := M.niceRefinementIndices a s b d level T T2 valid
  let selected := assignmentOnIndices I T A
  have carrier : s.carrier ∈ M.sets := members 7
  have order : s.conditionOrder ∈ M.sets := members 8
  have family := M.familySet_mem s ⊤ pairing unions powers separation (members 6) (members 9) valid
  have dataEq := M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports maps level T T2 valid valid2
  have graphEq := M.rawStageRefinementAssignmentActionGraph_eq a s t b d
    pairing unions powers separation collection carrier group nodes order maps nodeMaps supports
    level T T2 hLevel (members 6) valid valid2 closed closed2 family (members 0) g
  have selectedEq := M.structuralAssignmentImage_select_branch t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 function stored (t.encode g) A
  dsimp only at selectedEq
  rw [dataEq] at selectedEq
  have selectedShape : selected ⊆ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)
        t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level 0) T := by
    rw [dataEq]
    exact fun z hz => ((mem_assignmentOnIndices I T A z).1 hz).2
  have branchEq := M.structuralAssignmentImage_branch t.carrier b.carrier b.conditionOrder
    (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 function (t.encode_mem g) stored selectedShape
  rw [dataEq, graphEq] at branchEq
  have action := M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
    pairing unions powers separation collection carrier order maps closed2 family g
  exact selectedEq.trans (branchEq.trans (relationImage_source_selection action A).symm)

theorem storedPreparationRequests_structural_act
    (hLevel : level ∈ M.sets) (hT2 : T2 ∈ M.sets) {stages history : ZFSet.{u}}
    (function : FunctionGraphOn stages history)
    (stored : ZFSet.pair level
      (forcingStageCode s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t)) ∈ history)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (g : G) :
    let N := M.groundRelations T s.carrier
    let validN : ∀ z ∈ N, IsName s z := fun z hz =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier z).1 hz).2
    relationImage
      (M.storedPreparationRequests A (M.refinementLevelFormulaData a s b d level T T2 valid)) N
      (Name.renameFamilyGraph s (a.iso g) N validN) =
    M.storedPreparationRequests
      (M.structuralAssignmentImage t.carrier b.carrier b.conditionOrder (d.actionGraph b t)
        (supportBasisCode b t d.principalFix) T T2 stages history (t.encode g) A)
      (M.refinementLevelFormulaData a s b d level T T2 valid) := by
  dsimp only
  have selection := M.structuralAssignmentImage_selection_eq_refinement a s b d level T T2 valid valid2 t
    pairing unions powers separation collection members maps nodeMaps group nodes supports closed closed2
    hLevel function stored A g
  have localSelection : assignmentOnIndices (M.niceRefinementIndices a s b d level T T2 valid) T
      (M.refinementAssignmentImage a s b d level T T2 valid valid2 g A) =
      M.refinementAssignmentImage a s b d level T T2 valid valid2 g A := by
    apply ZFSet.ext
    intro z
    rw [mem_assignmentOnIndices]
    exact and_iff_left_of_imp
      (fun hz => M.refinementAssignmentImage_subset a s b d level T T2 valid valid2 g A hz)
  have requests := M.storedPreparationRequests_act a s b d level T T2 valid valid2 t
    pairing unions powers separation collection members maps nodeMaps closed closed2 hLevel hT2 hA g
  refine requests.trans ?_
  rw [M.storedPreparationRequests_typed, M.storedPreparationRequests_typed]
  dsimp only
  rw [selection, localSelection]

end PartitionPilot.Forcing.TransitiveGround

end OAI
