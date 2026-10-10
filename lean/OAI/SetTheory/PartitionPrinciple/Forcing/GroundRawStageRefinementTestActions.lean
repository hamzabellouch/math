import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageThreeDataBoundFixation

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementIndexActionGraph (g I P maps nodeMaps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets refinementIndexActionEntryFormula ![z,g,I,P,maps,nodeMaps])
    (ZFSet.prod I I)

noncomputable def rawTermActionGraph (g T P maps : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => Realize M.sets termActionEntryFormula ![z,g,T,P,maps]) (ZFSet.prod T T)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def definable_rawRefinementIndexActionGraph :
    GroundDefinableFunction M (fun env : Fin 5 → ZFSet.{u} =>
      M.rawRefinementIndexActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)) := by
  let v := GroundSetTerm.var M (n := 5)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1,v 1]
  let term := GroundSetTerm.app (M.definable_separation separation refinementIndexActionEntryFormula)
    ![bound,v 0,v 1,v 2,v 3,v 4]
  apply term.definition.congr
  intro env
  change ZFSet.sep (fun z => Realize M.sets refinementIndexActionEntryFormula (extend z _)) _ = _
  have args : (fun j : Fin 5 => (![bound,v 0,v 1,v 2,v 3,v 4] j.succ).eval env) = ![env 0,env 1,env 2,env 3,env 4] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))))) j
  rw [args]
  rfl

noncomputable def definable_rawTermActionGraph :
    GroundDefinableFunction M (fun env : Fin 4 → ZFSet.{u} =>
      M.rawTermActionGraph (env 0) (env 1) (env 2) (env 3)) := by
  let v := GroundSetTerm.var M (n := 4)
  let bound := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 1,v 1]
  let term := GroundSetTerm.app (M.definable_separation separation termActionEntryFormula)
    ![bound,v 0,v 1,v 2,v 3]
  apply term.definition.congr
  intro env
  change ZFSet.sep (fun z => Realize M.sets termActionEntryFormula (extend z _)) _ = _
  have args : (fun j : Fin 4 => (![bound,v 0,v 1,v 2,v 3] j.succ).eval env) = ![env 0,env 1,env 2,env 3] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  rw [args]
  rfl

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (level T1 T2 : ZFSet.{u}) (hl : level ∈ M.sets)
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps hl closed1 closed2 familyGround indexGround

theorem rawRefinementIndexActionGraph_eq (g : G) :
    M.rawRefinementIndexActionGraph (t.encode g)
      (M.niceRefinementIndices a s b d level T1 T2 valid1) s.carrier
      (a.conditionMapFamily s t) (d.conditionMapFamily b t) =
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  have bound := M.prod_mem pairing unions powers separation indexGround indexGround
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, entry⟩ := ZFSet.mem_sep.1 hz
    exact (M.realize_refinementIndexActionEntryFormula a s t b d pairing unions powers separation
      collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2
      closed1 closed2 familyGround indexGround g z (M.transitive bound hz)).1 entry
  · intro hz
    have bounded := (ZFSet.mem_sep.1 hz).1
    exact ZFSet.mem_sep.2 ⟨bounded,
      (M.realize_refinementIndexActionEntryFormula a s t b d pairing unions powers separation
        collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2
        closed1 closed2 familyGround indexGround g z (M.transitive bound bounded)).2 hz⟩

omit [OrderTop P] nodes order nodeMaps hl closed2 familyGround indexGround in
include pairing unions powers separation collection carrier group maps closed1 in
theorem rawTermActionGraph_eq (hT1 : T1 ∈ M.sets) (g : G) :
    M.rawTermActionGraph (t.encode g) T1 s.carrier (a.conditionMapFamily s t) =
      Name.renameFamilyGraph s (a.iso g) T1 valid1 := by
  have bound := M.prod_mem pairing unions powers separation hT1 hT1
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨hz, entry⟩ := ZFSet.mem_sep.1 hz
    exact (M.realize_termActionEntryFormula a s t T1 valid1 pairing unions powers separation
      collection carrier group maps hT1 closed1 g z (M.transitive bound hz)).1 entry
  · intro hz
    have bounded : z ∈ ZFSet.prod T1 T1 := by
      obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T1 valid1 z).1 hz
      exact ZFSet.pair_mem_prod.2 ⟨hw, closed1 g w hw⟩
    exact ZFSet.mem_sep.2 ⟨bounded,
      (M.realize_termActionEntryFormula a s t T1 valid1 pairing unions powers separation
        collection carrier group maps hT1 closed1 g z (M.transitive bound bounded)).2 hz⟩

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

noncomputable def rawRefinementAssignmentActionGraph (g I T P maps nodeMaps : ZFSet.{u}) : ZFSet.{u} :=
  relationProduct I (ZFSet.prod T T) I (ZFSet.prod T T)
    (M.rawRefinementIndexActionGraph g I P maps nodeMaps)
    (relationProduct T T T T (M.rawTermActionGraph g T P maps) (M.rawTermActionGraph g T P maps))

theorem pair_mem_rawRefinementAssignmentActionGraph (g I T P maps nodeMaps i u w i' u' w' : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) (stageOneAssignment i' u' w') ∈
      M.rawRefinementAssignmentActionGraph g I T P maps nodeMaps ↔
    i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ i' ∈ I ∧ u' ∈ T ∧ w' ∈ T ∧
      ZFSet.pair i i' ∈ M.rawRefinementIndexActionGraph g I P maps nodeMaps ∧
      ZFSet.pair u u' ∈ M.rawTermActionGraph g T P maps ∧
      ZFSet.pair w w' ∈ M.rawTermActionGraph g T P maps := by
  simp only [rawRefinementAssignmentActionGraph, stageOneAssignment,
    pair_mem_relationProduct, ZFSet.pair_mem_prod]
  tauto

noncomputable def definable_rawRefinementAssignmentActionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 6 → ZFSet.{u} =>
      M.rawRefinementAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let v := GroundSetTerm.var M (n := 6)
  let index := GroundSetTerm.app (M.definable_rawRefinementIndexActionGraph pairing unions powers separation)
    ![v 0,v 1,v 3,v 4,v 5]
  let term := GroundSetTerm.app (M.definable_rawTermActionGraph pairing unions powers separation)
    ![v 0,v 2,v 3,v 4]
  let terms := GroundSetTerm.app (M.definable_product pairing unions powers separation) ![v 2,v 2]
  let termPair := GroundSetTerm.app (M.definable_relationProduct pairing unions powers separation)
    ![v 2,v 2,v 2,v 2,term,term]
  exact (GroundSetTerm.app (M.definable_relationProduct pairing unions powers separation)
    ![v 1,terms,v 1,terms,index,termPair]).definition

noncomputable def rawStageRefinementAssignmentActionGraph
    (g P order top actionGraph G nodes nodeOrder nodeAction basis T T2 level : ZFSet.{u}) : ZFSet.{u} :=
  M.rawRefinementAssignmentActionGraph g
    (M.rawRefinementFormulaData P order top actionGraph G nodes nodeOrder basis T T2 level 0)
    T P (rawActionMapFamily G actionGraph P) (rawActionMapFamily G nodeAction nodes)

noncomputable def definable_rawStageRefinementAssignmentActionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 13 → ZFSet.{u} =>
      M.rawStageRefinementAssignmentActionGraph (env 0) (env 1) (env 2) (env 3) (env 4)
        (env 5) (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12)) := by
  let v := GroundSetTerm.var M (n := 13)
  let maps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 5,v 4,v 1]
  let nodeMaps := GroundSetTerm.app (M.definable_rawActionMapFamily pairing unions powers separation collection)
    ![v 5,v 8,v 6]
  let first := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 6,v 10,v 1,v 5,v 9,maps]
  let second := GroundSetTerm.app (M.definable_rawNiceNameCandidateGraph pairing unions powers separation collection)
    ![v 6,v 11,v 1,v 5,v 9,maps]
  let family := GroundSetTerm.app (M.definable_familySetCode pairing unions powers separation) ![v 10,v 3]
  let indices := GroundSetTerm.app (M.definable_refinementIndices pairing unions powers separation)
    ![v 12,v 6,v 7,first,second,v 10,v 11,family,v 1,v 2,v 3]
  exact (GroundSetTerm.app (M.definable_rawRefinementAssignmentActionGraph pairing unions powers separation)
    ![v 0,indices,v 10,v 1,maps,nodeMaps]).definition

end

section
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (hl : level ∈ M.sets) (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps supports hl hT closed closed2 familyGround indexGround

theorem rawStageRefinementAssignmentActionGraph_eq (g : G) :
    M.rawStageRefinementAssignmentActionGraph (t.encode g) s.carrier s.conditionOrder
      (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
      (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level =
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g := by
  unfold rawStageRefinementAssignmentActionGraph
  rw [M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports maps level T T2 valid valid2, rawActionMapFamily_eq, rawActionMapFamily_eq]
  change M.rawRefinementAssignmentActionGraph (t.encode g)
    (M.niceRefinementIndices a s b d level T T2 valid) T s.carrier
    (a.conditionMapFamily s t) (d.conditionMapFamily b t) = _
  unfold rawRefinementAssignmentActionGraph refinementAssignmentActionGraph
  rw [M.rawRefinementIndexActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order maps nodeMaps level T T2 hl valid valid2 closed closed2 familyGround indexGround g,
    M.rawTermActionGraph_eq (a := a) (s := s) (t := t) (pairing := pairing) (unions := unions)
      (powers := powers) (separation := separation) (collection := collection) (carrier := carrier)
      (group := group) (maps := maps) (T1 := T) (valid1 := valid) (closed1 := closed) hT g]

end

section
open SetRealization SetFormula
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

theorem rawStageRefinementAssignment_fixed_of_dataBound
    (I S mu X tuples A : ZFSet.{u}) (D : L)
    (support : ∀ f ∈ S, ∀ u : Name s, ZFSet.pair f u.val ∈ tuples →
      RowPositionBound mu X b.conditionOrder f (b.encode D) →
      d.principalFix D ≤ a.stabilizer s u)
    (g : G) (actor : g ∈ d.principalFix D) (z : ZFSet.{u})
    (member : z ∈ stageOneAssignments
      (M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤)
        (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
        (supportBasisCode b t d.principalFix) T T2 level 0) T)
    (bound : ZFSet.pair z (b.encode D) ∈ stageOneDataBounds A I T S b.carrier mu X
      b.conditionOrder (refinementIndexFieldGraph I b.carrier 2) tuples) :
    ZFSet.pair z z ∈ M.rawStageRefinementAssignmentActionGraph (t.encode g)
      s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier
      b.conditionOrder (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level := by
  rw [M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation collection
    carrier group nodes order system.inputs.condition_maps system.inputs.node_maps supports level T T2
    hLevel hT system.valid1 system.valid2 system.inputs.terms_closed system.inputs.pairs_closed
    system.inputs.family_ground system.indices.index_ground]
  rw [M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports system.inputs.condition_maps level T T2 system.valid1 system.valid2] at member
  obtain ⟨idx, hi, rawU, hu, rawW, hw, rfl⟩ := (mem_stageOneAssignments _ _ z).1 member
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T T2 system.valid1 system.valid2 hi
  let u : Name s := ⟨rawU, system.valid1 rawU hu⟩
  let w : Name s := ⟨rawW, system.valid1 rawW hw⟩
  exact M.refinementAssignment_fixed_of_dataBound a s b d I level T T2 system.valid1 system.valid2 t
    pairing unions powers separation collection carrier order system.inputs.condition_maps
    system.inputs.terms_closed system.inputs.pairs_closed system.inputs.family_ground
    S mu X tuples A D support g actor C E U Rf Rc u w hi hu hw bound

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (params : StageOneActionParameters M a s t b d T T2 valid)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
local notation "data" => M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤)
  (a.actionGraph s t) t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level
include pairing unions powers separation collection carrier group nodes order supports valid2 params hLevel hT indexGround

theorem rawStageRefinement_relationLaws :
    RelationActionLaws G (stageOneAssignments (data 0) T) branch := by
  have graphs : branch = M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 :=
    funext (fun g => M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation
      collection carrier group nodes order params.condition_maps params.node_maps supports level T T2 hLevel hT
      valid valid2 params.terms_closed params.pairs_closed params.family_ground indexGround g)
  rw [graphs, M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports params.condition_maps level T T2 valid valid2]
  exact M.refinementAssignment_relationLaws a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order params

theorem rawStageRefinement_image_eq (g : G) (A : ZFSet.{u}) :
    relationImage A (stageOneAssignments (data 0) T) (branch g) =
      M.refinementAssignmentImage a s b d level T T2 valid valid2 g A := by
  dsimp only
  rw [M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
    carrier group nodes supports params.condition_maps level T T2 valid valid2,
    M.rawStageRefinementAssignmentActionGraph_eq a s t b d pairing unions powers separation
      collection carrier group nodes order params.condition_maps params.node_maps supports level T T2 hLevel hT
      valid valid2 params.terms_closed params.pairs_closed params.family_ground indexGround g]
  rfl

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets) (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (params : StageOneActionParameters M a s t b d T T2 valid)
variable (hLevel : level ∈ M.sets) (hT : T ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T T2 valid ∈ M.sets)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "data" => M.rawRefinementFormulaData s.carrier s.conditionOrder (s.encode ⊤)
  (a.actionGraph s t) t.carrier b.carrier b.conditionOrder (supportBasisCode b t d.principalFix) T T2 level
local notation "branch" => fun g => M.rawStageRefinementAssignmentActionGraph (t.encode g)
  s.carrier s.conditionOrder (s.encode ⊤) (a.actionGraph s t) t.carrier b.carrier b.conditionOrder
  (d.actionGraph b t) (supportBasisCode b t d.principalFix) T T2 level
include pairing unions powers separation collection carrier group nodes order supports params hLevel hT indexGround indices system

theorem rawStageRefinementTests_image_iff (g : G) (A : ZFSet.{u}) (p : P) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) (s.encode (a.iso g p)) ↔
      stageOneRawTests M data A (s.encode p) := by
  rw [M.rawStageRefinement_image_eq a s t b d pairing unions powers separation collection
    carrier group nodes order supports level T T2 valid valid2 params hLevel hT indexGround,
    M.rawRefinementFormulaData_eq a s t b d pairing unions powers separation collection
      carrier group nodes supports params.condition_maps level T T2 valid valid2]
  rw [M.refinementLevelRawTests_iff a s b d level pairing unions powers separation collection
    carrier order nodes hT valid indices base directed system,
    M.refinementLevelRawTests_iff a s b d level pairing unions powers separation collection
      carrier order nodes hT valid indices base directed system]
  exact M.refinementLevelTests_image_iff a s b d level T T2 valid valid2 t pairing unions powers separation
    collection carrier order params.condition_maps hT params.terms_closed params.pairs_closed params.family_ground
    base directed system g A p

theorem rawStageRefinementTests_actionGraph_iff (g : G) (A p q : ZFSet.{u})
    (edge : ZFSet.pair (ZFSet.pair (t.encode g) p) q ∈ a.actionGraph s t) :
    stageOneRawTests M data (relationImage A (stageOneAssignments (data 0) T) (branch g)) q ↔
      stageOneRawTests M data A p := by
  obtain ⟨⟨g', p'⟩, equal⟩ := ((t.product s).mem_graph s (fun x => a.iso x.1 x.2) _).1 edge
  obtain ⟨inputs, output⟩ := ZFSet.pair_inj.1 equal.symm
  obtain ⟨actors, source⟩ := ZFSet.pair_inj.1 inputs
  have actor : g = g' := t.injective actors
  have target : q = s.encode (a.iso g p') := by
    simpa only [← actor] using output
  rw [source, target]
  exact M.rawStageRefinementTests_image_iff a s t b d pairing unions powers separation collection
    carrier group nodes order supports level T T2 valid valid2 params hLevel hT indexGround
    indices base directed system g A p'

end PartitionPilot.Forcing.TransitiveGround

end OAI
