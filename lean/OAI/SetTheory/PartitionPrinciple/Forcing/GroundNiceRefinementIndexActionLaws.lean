import OAI.SetTheory.PartitionPrinciple.Definability.TupleRelationProducts
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundStageOneAssignmentUnions

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)

include pairing unions powers separation collection carrier order maps in
theorem niceRefinementIndex_act_iff (level T1 T2 : ZFSet.{u})
    (valid : ∀ z ∈ T1, IsName s z)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid).val ∈ M.sets)
    (g : G) (C E : L) (U Rf Rc : (M.nameDomain s).names) :
    refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid ↔
      refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid := by
  let groundClosed := fun g (w : Name s) (hw : w ∈ (M.nameDomain s).names) =>
    M.act_mem s a t pairing unions powers separation collection carrier maps g w hw
  let moved := a.domainEquiv s (M.nameDomain s) groundClosed g
  let whole : (M.nameDomain s).names := ⟨Name.familySet ⊤ T1 valid, familyGround⟩
  let env := extend U (extend Rf (extend Rc (extend whole Fin.elim0)))
  have sameWhole : moved whole = whole :=
    Subtype.ext (Name.act_familySet a T1 valid closed1 g)
  have envEq : a.actAssignment s (M.nameDomain s) groundClosed g env =
      extend (moved U) (extend (moved Rf) (extend (moved Rc) (extend whole Fin.elim0))) := by
    funext j
    refine Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases ?_
      (fun k => Fin.elim0 k)))) j
    exact sameWhole
  have force := a.formula_forces_act_iff s (M.nameDomain s) groundClosed g
    BoundedFormula.refinementValidityFormula.toFormula env ⊤
  rw [(a.iso g).map_top, envEq] at force
  change refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (moved U).val.val (moved Rf).val.val (moved Rc).val.val ∈
        M.niceRefinementIndices a s b d level T1 T2 valid ↔ _
  rw [M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid familyGround (d.iso g C) (d.iso g E)
      (moved U) (moved Rf) (moved Rc),
    M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
      carrier order level T1 T2 valid familyGround C E U Rf Rc]
  exact and_congr (d.iso g).lt_iff_lt
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed1 d g C U.val)
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed2 d g C Rf.val)
    (and_congr (M.niceNameCandidates_principal_act_iff a s t pairing unions powers separation
      collection carrier maps closed2 d g C Rc.val) force)))

omit [OrderTop P] in
theorem niceRefinementIndex_fixed (level T1 T2 : ZFSet.{u}) (C E : L)
    (U Rf Rc : Name s) (lower : C ≤ E)
    (domain : U.val ∈ M.niceNameCandidates a s T1 (d.principalFix C))
    (fine : Rf.val ∈ M.niceNameCandidates a s T2 (d.principalFix C))
    (coarse : Rc.val ∈ M.niceNameCandidates a s T2 (d.principalFix C))
    (g : G) (fixed : g ∈ d.principalFix E) :
    refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U).val (a.act s g Rf).val (a.act s g Rc).val =
        refinementIndexCode level (b.encode C) (b.encode E) U.val Rf.val Rc.val := by
  have atC : g ∈ d.principalFix C := d.principalFix_antitone lower fixed
  have getSupport {X : ZFSet.{u}} (w : Name s)
      (member : w.val ∈ M.niceNameCandidates a s X (d.principalFix C)) :
      a.act s g w = w := by
    have code := ((M.mem_niceNameCandidates a s X (d.principalFix C) w.val).1 member).2
    obtain ⟨σ, equal, _, support⟩ := code
    have same : σ = w := Subtype.ext equal
    subst σ
    exact support atC
  rw [fixed C lower, fixed E le_rfl, getSupport U domain, getSupport Rf fine, getSupport Rc coarse]

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u}
variable [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)

noncomputable def stageOneNameAction (g : G) : (M.nameDomain s).names ≃ (M.nameDomain s).names :=
  a.domainEquiv s (M.nameDomain s)
    (fun g w hw => M.act_mem s a t pairing unions powers separation collection carrier maps g w hw) g

theorem stageOneNameAction_val (g : G) (w : (M.nameDomain s).names) :
    (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g w).val =
      a.act s g w.val := rfl

theorem stageOneNameAction_one (w : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps 1 w = w :=
  Subtype.ext (a.act_one s w.val)

theorem stageOneNameAction_mul (g h : G) (w : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps (g * h) w =
      M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
        (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps h w) :=
  Subtype.ext (a.act_mul s g h w.val)

theorem stageOneNameAction_forces_iff (g : G) {n : Nat} (φ : SetFormula n)
    (env : Assignment (M.nameDomain s) n) (p : P) :
    Forces (M.nameDomain s) φ
      (fun j => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g (env j))
      (a.iso g p) ↔ Forces (M.nameDomain s) φ env p :=
  a.formula_forces_act_iff s (M.nameDomain s)
    (fun g w hw => M.act_mem s a t pairing unions powers separation collection carrier maps g w hw)
    g φ env p

variable [OrderTop P] (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

include closed in
theorem stageOneNameAction_class (g : G) (R w : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneClassName s pairing unions powers separation collection carrier order hT valid R w) =
    M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g R)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g w) :=
  Subtype.ext (Name.act_refinementClass a T valid closed g R.val w.val)

include closed in
theorem stageOneNameAction_map (g : G) (U Rf Rc : (M.nameDomain s).names) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc) =
    M.stageOneMapName s pairing unions powers separation collection carrier order hT valid
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g U)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g Rf)
      (M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g Rc) :=
  Subtype.ext (Name.act_refinementNaturalMap a T valid closed g U.val Rf.val Rc.val)

variable {L : Type u} [PartialOrder L]
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

theorem stageOneNameAction_visibility (system : NiceNameSystem M a s b d base directed T valid)
    (g : G) (v : L) :
    M.stageOneNameAction a s t pairing unions powers separation collection carrier maps g
      (M.stageOneVisibilityName s valid a b d base directed system v) =
      M.stageOneVisibilityName s valid a b d base directed system (d.iso g v) :=
  Subtype.ext (system.visibility_action g v)

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
variable (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
local notation "move" => M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
local notation "cls" => M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
local notation "vis" => M.stageOneVisibilityName s valid a b d base directed system
local notation "mapName" => M.stageOneMapName s pairing unions powers separation collection carrier order hT valid

omit [OrderTop P] in
theorem stageOneActivity_act_iff (g : G) (U u w : (M.nameDomain s).names) (p : P) :
    Forces (M.nameDomain s) refinementActivityFormula ![move g u, move g w, move g U] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementActivityFormula ![u, w, U] p := by
  have envEq : (fun j => move g (![u, w, U] j)) =
      ![move g u, move g w, move g U] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) j
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementActivityFormula ![u, w, U] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneProfile_act_iff (g : G) (Rc Rf u w : (M.nameDomain s).names) (v : L) (p : P) :
    Forces (M.nameDomain s) refinementProfileFormula ![cls (move g Rc) (move g u), cls (move g Rf) (move g w), vis (d.iso g v)] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p := by
  have envEq : (fun j => move g (![cls Rc u, cls Rf w, vis v] j)) =
      ![cls (move g Rc) (move g u), cls (move g Rf) (move g w), vis (d.iso g v)] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_visibility a s t pairing unions powers separation collection carrier maps valid b d base directed system g _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementProfileFormula ![cls Rc u, cls Rf w, vis v] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneCompatibility_act_iff (g : G) (U Rf Rc u w : (M.nameDomain s).names) (C : L) (p : P) :
    Forces (M.nameDomain s) refinementCompatibilityFormula ![cls (move g Rf) (move g w), vis (d.iso g C), cls (move g Rc) (move g u), mapName (move g U) (move g Rf) (move g Rc)] (a.iso g p) ↔
      Forces (M.nameDomain s) refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] p := by
  have envEq : (fun j => move g (![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] j)) =
      ![cls (move g Rf) (move g w), vis (d.iso g C), cls (move g Rc) (move g u), mapName (move g U) (move g Rf) (move g Rc)] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_visibility a s t pairing unions powers separation collection carrier maps valid b d base directed system g _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_map a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _ _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementCompatibilityFormula ![cls Rf w, vis C, cls Rc u, mapName U Rf Rc] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneCollisionTest_act_iff (g : G) (Rf Rc u u' w w' : (M.nameDomain s).names) (p : P) :
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      (move g Rf) (move g Rc) (move g u) (move g u') (move g w) (move g w') (a.iso g p) ↔
    M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid Rf Rc u u' w w' p := by
  change Forces (M.nameDomain s) refinementCollisionFormula ![cls (move g Rc) (move g u), cls (move g Rc) (move g u'), cls (move g Rf) (move g w), cls (move g Rf) (move g w')] (a.iso g p) ↔
    Forces (M.nameDomain s) refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p
  have envEq : (fun j => move g (![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] j)) =
      ![cls (move g Rc) (move g u), cls (move g Rc) (move g u'), cls (move g Rf) (move g w), cls (move g Rf) (move g w')] := by
    funext j
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => Fin.elim0 k)))) j
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
    · exact M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps order hT valid closed g _ _
  have law := M.stageOneNameAction_forces_iff a s t pairing unions powers separation collection
    carrier maps g refinementCollisionFormula ![cls Rc u, cls Rc u', cls Rf w, cls Rf w'] p
  rw [envEq] at law
  exact law

include closed in
theorem stageOneSingleTests_act_iff (g : G) (C E : L)
    (U Rf Rc u w : (M.nameDomain s).names) (p : P) :
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system (d.iso g C) (d.iso g E)
        (move g U) (move g Rf) (move g Rc) (move g u) (move g w) (a.iso g p) ↔
    M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
      a b d base directed system C E U Rf Rc u w p := by
  have activity := M.stageOneActivity_act_iff a s t pairing unions powers separation collection
    carrier maps g U u w p
  have compatible := M.stageOneCompatibility_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g U Rf Rc u w C p
  have profile := fun v => M.stageOneProfile_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system g Rc Rf u w v p
  constructor
  · intro tests
    refine ⟨activity.mp tests.1, ?_, compatible.mp tests.2.2⟩
    intro v above
    exact (profile v).mp (tests.2.1 (d.iso g v) ((d.iso g).monotone above))
  · intro tests
    refine ⟨activity.mpr tests.1, ?_, compatible.mpr tests.2.2⟩
    intro v above
    obtain ⟨v, rfl⟩ := (d.iso g).surjective v
    exact (profile v).mpr (tests.2.1 v ((d.iso g).le_iff_le.mp above))

end

section
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)

noncomputable def niceRefinementIndexCoordinateGraphs (g : G) : Fin 6 → ZFSet.{u} :=
  ![identityFunctionGraph {level}, b.graph b (d.iso g), b.graph b (d.iso g),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T1 s.carrier)
      (fun z hz => Name.isName_of_subset valid1 ((M.mem_groundRelations T1 s.carrier z).1 hz).2),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T2 s.carrier)
      (fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2),
    Name.renameFamilyGraph s (a.iso g) (M.groundRelations T2 s.carrier)
      (fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2)]

noncomputable def niceRefinementIndexActionGraph (g : G) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∈ tupleRelationProduct 5
    (M.niceRefinementIndexCoordinateGraphs a s b d level T1 T2 valid1 valid2 g))
    (ZFSet.prod (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndices a s b d level T1 T2 valid1))

theorem pair_mem_niceRefinementIndexActionGraph (g : G) (x y : Fin 6 → ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode 5 x) (nonemptyTupleCode 5 y) ∈
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g ↔
    nonemptyTupleCode 5 x ∈ M.niceRefinementIndices a s b d level T1 T2 valid1 ∧
    nonemptyTupleCode 5 y ∈ M.niceRefinementIndices a s b d level T1 T2 valid1 ∧
      ∀ j, ZFSet.pair (x j) (y j) ∈
        M.niceRefinementIndexCoordinateGraphs a s b d level T1 T2 valid1 valid2 g j := by
  rw [niceRefinementIndexActionGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod,
    pair_mem_tupleRelationProduct]
  exact and_assoc

theorem niceRefinementIndexActionGraph_mem (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hl : level ∈ M.sets) (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (indexGround : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets)
    (g : G) : M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g ∈ M.sets := by
  have identity := M.identityFunctionGraph_mem pairing unions powers separation
    (show ({level} : ZFSet.{u}) ∈ M.sets from by
      simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hl hl)
  have nodes := M.conditionMap_graph_mem d b t nodeMaps g
  have condition := M.conditionMap_graph_mem a s t maps g
  have first := M.renameFamilyGraph_mem s s pairing unions powers separation collection
    carrier carrier (a.iso g) condition (M.groundRelations T1 s.carrier)
    (M.groundRelations_mem pairing unions powers separation hT1 carrier)
    (fun z hz => Name.isName_of_subset valid1 ((M.mem_groundRelations T1 s.carrier z).1 hz).2)
  have second := M.renameFamilyGraph_mem s s pairing unions powers separation collection
    carrier carrier (a.iso g) condition (M.groundRelations T2 s.carrier)
    (M.groundRelations_mem pairing unions powers separation hT2 carrier)
    (fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2)
  have coordinates : ∀ j, M.niceRefinementIndexCoordinateGraphs a s b d level T1 T2 valid1 valid2 g j ∈ M.sets :=
    Fin.cases identity (Fin.cases nodes (Fin.cases nodes (Fin.cases first
      (Fin.cases second (Fin.cases second (fun j => Fin.elim0 j))))))
  have whole := M.tupleRelationProduct_mem pairing unions powers separation 5 _ coordinates
  exact M.separation_mem separation (.mem 0 1) (extend _ Fin.elim0)
    (Fin.cases whole (fun j => Fin.elim0 j))
    (M.prod_mem pairing unions powers separation indexGround indexGround)

theorem niceRefinementIndexActionGraph_entry (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
    (g : G) (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (source : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (y : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) y ∈
      M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g ↔
    y = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  have input := ((M.niceRefinementIndex_mem_iff a s b d pairing unions powers separation collection
    carrier order level T1 T2 valid1 familyGround C E U Rf Rc).1 source)
  have hU := M.niceNameCandidates_subset a s T1 _ input.2.1
  have hf := M.niceNameCandidates_subset a s T2 _ input.2.2.1
  have hc := M.niceNameCandidates_subset a s T2 _ input.2.2.2.1
  have domainValid : ∀ z ∈ M.groundRelations T1 s.carrier, IsName s z :=
    fun z hz => Name.isName_of_subset valid1 ((M.mem_groundRelations T1 s.carrier z).1 hz).2
  have relationValid : ∀ z ∈ M.groundRelations T2 s.carrier, IsName s z :=
    fun z hz => Name.isName_of_subset valid2 ((M.mem_groundRelations T2 s.carrier z).1 hz).2
  constructor
  · intro entry
    have target := (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 entry).1).2
    obtain ⟨C', E', U', Rf', Rc', rfl⟩ :=
      M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 target
    have coordinates := ((M.pair_mem_niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
      ![level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val]).1 entry).2.2
    have nodeC := (b.pair_mem_graph b (d.iso g) C C').1 (coordinates 1)
    have nodeE := (b.pair_mem_graph b (d.iso g) E E').1 (coordinates 2)
    have domain := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ domainValid U.val U'.val.val).1
      (coordinates 3)).2
    have fine := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rf.val Rf'.val.val).1
      (coordinates 4)).2
    have coarse := ((Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rc.val Rc'.val.val).1
      (coordinates 5)).2
    rw [← nodeC, ← nodeE, domain, fine, coarse]
    rfl
  · rintro rfl
    apply (M.pair_mem_niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g
      ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
      ![level, b.encode (d.iso g C), b.encode (d.iso g E), (a.act s g U.val).val,
        (a.act s g Rf.val).val, (a.act s g Rc.val).val]).2
    refine ⟨source, (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
      carrier order maps level T1 T2 valid1 closed1 closed2 familyGround g C E U Rf Rc).2 source, ?_⟩
    refine Fin.cases ((pair_mem_identityFunctionGraph {level} level level).2
      ⟨rfl, ZFSet.mem_singleton.2 rfl⟩) (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_
        (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))))))
    · exact (b.pair_mem_graph b (d.iso g) C _).2 rfl
    · exact (b.pair_mem_graph b (d.iso g) E _).2 rfl
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ domainValid U.val _).2 ⟨hU, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rf.val _).2 ⟨hf, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) _ relationValid Rc.val _).2 ⟨hc, rfl⟩

theorem niceRefinementIndexActionGraph_function (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets)
    (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets) (g : G) :
    ZFSet.IsFunc (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hx
  have meaning := M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g C E U Rf Rc hx
  exact ⟨_, (meaning _).2 rfl, fun y hy => (meaning y).1 hy⟩

end

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
local notation "I" => M.niceRefinementIndices a s b d level T1 T2 valid1
local notation "graph" => M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2
include pairing unions powers separation collection carrier order maps closed1 closed2 familyGround

private theorem inverse_edge (g : G) {x y : ZFSet.{u}}
    (entry : ZFSet.pair x y ∈ graph g) : ZFSet.pair y x ∈ graph g⁻¹ := by
  have shape := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 entry).1
  obtain ⟨C, E, U, Rf, Rc, rfl⟩ :=
    M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 shape.1
  have equal := (M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g C E U Rf Rc shape.1 y).1 entry
  subst y
  let move (w : (M.nameDomain s).names) : (M.nameDomain s).names :=
    ⟨a.act s g w.val, M.act_mem s a t pairing unions powers separation collection carrier maps g w.val w.property⟩
  apply (M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
    g⁻¹ (d.iso g C) (d.iso g E) (move U) (move Rf) (move Rc) shape.2 _).2
  change refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val =
    refinementIndexCode level (b.encode (d.iso g⁻¹ (d.iso g C))) (b.encode (d.iso g⁻¹ (d.iso g E)))
      (a.act s g⁻¹ (a.act s g U.val)).val (a.act s g⁻¹ (a.act s g Rf.val)).val
      (a.act s g⁻¹ (a.act s g Rc.val)).val
  rw [a.act_inv_left, a.act_inv_left, a.act_inv_left, ← d.mul, ← d.mul, inv_mul_cancel,
    d.one, d.one]

theorem niceRefinementIndexActionGraph_inverse_iff (g : G) (x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ graph g ↔ ZFSet.pair y x ∈ graph g⁻¹ := by
  constructor
  · exact M.inverse_edge a s b d level T1 T2 valid1 valid2 t pairing unions powers separation
      collection carrier order maps closed1 closed2 familyGround g
  · intro entry
    simpa only [inv_inv] using M.inverse_edge a s b d level T1 T2 valid1 valid2 t pairing unions powers separation
      collection carrier order maps closed1 closed2 familyGround g⁻¹ entry

theorem niceRefinementIndexActionGraph_injection (g : G) : InjectionCode I I (graph g) := by
  refine ⟨M.niceRefinementIndexActionGraph_function a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g, ?_⟩
  intro x y z first second
  have back := M.niceRefinementIndexActionGraph_function a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g⁻¹
  have zx := (M.niceRefinementIndexActionGraph_inverse_iff a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g x z).1 first
  have zy := (M.niceRefinementIndexActionGraph_inverse_iff a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g y z).1 second
  obtain ⟨v, _, unique⟩ := back.2 z (ZFSet.pair_mem_prod.1 (back.1 zx)).1
  exact (unique x zx).trans (unique y zy).symm

end PartitionPilot.Forcing.TransitiveGround

end OAI
