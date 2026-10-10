import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceRefinementClassSupports
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundStageOneRawNames
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainFinalSeparatedActors
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundPreparedMixedCollisions

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)
variable (valid2 : ∀ z ∈ T2, IsName s z)
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem niceRefinementIndex_copies_agree (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (g h : G) (V : L) (anchor : E ≤ V) (relative : g⁻¹ * h ∈ d.principalFix V) :
    refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
      (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
    refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  obtain ⟨lower, hU, hRf, hRc, _⟩ := (indices.typed_entries C E U Rf Rc).1 member
  have point (x : L) (below : x ≤ V) : d.iso h x = d.iso g x := by
    have equal := congrArg (d.iso g) (relative x below)
    rw [d.mul, d.point_inv_right] at equal
    exact equal
  have atC : g⁻¹ * h ∈ d.principalFix C :=
    d.principalFix_antitone (le_trans (le_of_lt lower) anchor) relative
  have name {A : ZFSet.{u}} (tau : Name s)
      (candidate : tau.val ∈ M.niceNameCandidates a s A (d.principalFix C)) :
      a.act s h tau = a.act s g tau := by
    have fixed := ((M.name_mem_niceNameCandidates a s A (d.principalFix C) tau).1 candidate).2.2 atC
    change a.act s (g⁻¹ * h) tau = tau at fixed
    have equal := congrArg (a.act s g) fixed
    rw [a.act_mul, a.act_inv_right] at equal
    exact equal
  rw [point C (le_trans (le_of_lt lower) anchor), point E anchor,
    name U.val hU, name Rf.val hRf, name Rc.val hRc]

include indices in
theorem niceRefinementIndex_copies_agree_of_shared_anchor
    (meet : L → L → L)
    (greatest : ∀ x v w : L, x ≤ v → x ≤ w → x ≤ meet v w)
    (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (g h : G) (V D X : L) (bound : E ≤ D) (shared : d.iso h E ≤ X)
    (overlap : meet (d.iso h D) X = d.iso h V)
    (relative : g⁻¹ * h ∈ d.principalFix V) :
    E ≤ V ∧
      refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
        (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
      refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  have both := greatest (d.iso h E) (d.iso h D) X ((d.iso h).monotone bound) shared
  rw [overlap] at both
  have anchor : E ≤ V := (d.iso h).le_iff_le.1 both
  exact ⟨anchor, M.niceRefinementIndex_copies_agree a s b d level T T2 valid valid2
    indices C E U Rf Rc member g h V anchor relative⟩

end TransitiveGround

namespace TransitiveGround
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

variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelFormulaData_fields (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) :
    let idx := refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.refinementLevelFormulaData a s b d level T T2 valid
    (∀ z, ZFSet.pair idx z ∈ data 1 ↔ z = b.encode C) ∧
    (∀ z, ZFSet.pair idx z ∈ data 2 ↔ z = b.encode E) ∧
    (∀ z, ZFSet.pair idx z ∈ data 3 ↔ z = U.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 4 ↔ z = Rf.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 5 ↔ z = Rc.val.val) :=
  ⟨M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 1,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 2,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 3,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 4,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 5⟩

include indices in
theorem refinementLevelFormulaData_map (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (z : ZFSet.{u}) :
    ZFSet.pair (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) z ∈
      M.refinementLevelFormulaData a s b d level T T2 valid 12 ↔
      z = (M.stageOneMapName s pairing unions powers separation collection carrier order hT valid U Rf Rc).val.val :=
  M.niceRefinementNameGraph_entry a s b d indices pairing unions powers separation collection hT carrier order
    2 C E U Rf Rc member z

variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem refinementLevelFormulaData_visibility (v : L) (z : ZFSet.{u}) :
    ZFSet.pair (b.encode v) z ∈ M.refinementLevelFormulaData a s b d level T T2 valid 13 ↔
      z = (M.stageOneVisibilityName s valid a b d base directed system v).val.val :=
  system.visibility_entries v z

end TransitiveGround

namespace TransitiveGround
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
variable {T T2 : ZFSet.{u}} (hT : T ∈ M.sets)
variable (valid : ∀ z ∈ T, IsName s z) {valid2 : ∀ z ∈ T2, IsName s z}
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include indices in
theorem refinementLevelRawCollision_iff (C E : L) (U Rf Rc u u' w w' : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T T2 valid) (p : P) :
    stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)
      u.val.val u'.val.val w.val.val w'.val.val (s.encode p) ↔
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid Rf Rc u u' w w' p := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let env : Assignment (M.nameDomain s) 4 := ![cls Rc u, cls Rc u', cls Rf w, cls Rf w']
  have codes : (fun j => (env j).val.val) =
      ![(cls Rc u).val.val, (cls Rc u').val.val, (cls Rf w).val.val, (cls Rf w').val.val] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) j
  have forcing := M.stageOneRawForces_iff s pairing unions powers separation collection carrier order
    refinementCollisionFormula p env
  rw [codes] at forcing
  have fields := M.refinementLevelFormulaData_fields s valid a b d level indices C E U Rf Rc member
  constructor
  · rintro ⟨f, ground, body⟩
    obtain ⟨_, _, _, _, ff, fr, bu, bu', aw, aw', forced⟩ := body
    have ef := (fields.2.2.2.1 _).1 ff
    have er := (fields.2.2.2.2 _).1 fr
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u.val.val (f 2) at bu
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 1) u'.val.val (f 3) at bu'
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w.val.val (f 4) at aw
    change stageOneRawClass M T s.carrier s.conditionOrder (s.encode ⊤) (f 0) w'.val.val (f 5) at aw'
    rw [er] at bu bu'
    rw [ef] at aw aw'
    have eb := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (ground 2)).1 bu
    have eb' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (ground 3)).1 bu'
    have ea := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (ground 4)).1 aw
    have ea' := (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (ground 5)).1 aw'
    rw [eb, eb', ea, ea'] at forced
    exact forcing.1 forced
  · intro forced
    refine ⟨![Rf.val.val, Rc.val.val, (cls Rc u).val.val, (cls Rc u').val.val,
      (cls Rf w).val.val, (cls Rf w').val.val], ?_, ?_⟩
    · exact Fin.cases Rf.property (Fin.cases Rc.property (Fin.cases (cls Rc u).property
        (Fin.cases (cls Rc u').property (Fin.cases (cls Rf w).property
          (Fin.cases (cls Rf w').property (fun j => Fin.elim0 j))))))
    · refine ⟨M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rc u',
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w,
        M.stageOneClassName_mem_bound s pairing unions powers separation collection carrier order hT valid Rf w',
        (fields.2.2.2.1 _).2 rfl, (fields.2.2.2.2 _).2 rfl, ?_, ?_, ?_, ?_, forcing.2 forced⟩
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u _ (cls Rc u).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rc u' _ (cls Rc u').property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w _ (cls Rf w).property).2 rfl
      · exact (M.stageOneRawClass_iff s pairing unions powers separation collection carrier order hT valid Rf w' _ (cls Rf w').property).2 rfl

end TransitiveGround

namespace GroundMainFinalGeometry
open SetRealization SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)
variable {P : Type u} [PartialOrder P] [OrderTop P]

theorem copied_refinement_index_shared_anchor (s : Presentation P) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let b := SetMembers.presentation geometry.carrier
    let d := geometry.decodedAction
    ∀ (a : PosetAction (SetMembers geometry.actors) P) (level T T2 : ZFSet.{u})
      (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
      (_indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)
      (C E : SetMembers geometry.carrier) (U Rf Rc : (M.nameDomain s).names)
      (_member : refinementIndexCode level (b.encode C) (b.encode E)
        U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
      (g h : SetMembers geometry.actors) (V B X : SetMembers geometry.carrier)
      (_bound : E ≤ B) (_shared : d.iso h E ≤ X)
      (_overlap : geometry.meet.smallMeet (d.iso h B) X = d.iso h V)
      (_relative : g⁻¹ * h ∈ d.principalFix V),
      E ≤ V ∧
        refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (a.act s h U.val).val (a.act s h Rf.val).val (a.act s h Rc.val).val =
        refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
          (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro a level T T2 valid valid2 indices C E U Rf Rc member g h V B X bound shared overlap relative
  exact M.niceRefinementIndex_copies_agree_of_shared_anchor a s
    (SetMembers.presentation geometry.carrier) geometry.decodedAction level T T2 valid valid2 indices
    geometry.meet.smallMeet (fun _ _ _ left right => geometry.meet.toSmallMeetOrder.le_meet left right)
    C E U Rf Rc member g h V B X bound shared overlap relative

end GroundMainFinalGeometry

namespace TransitiveGround
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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
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

variable {T2 : ZFSet.{u}} (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed2 : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include group nodes supports closed closed2 descent indices in
theorem prepared_joint_refinementCollision_tests (small : M.sets.Countable)
    (C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (F B f : Fin 2 → ZFSet.{u}) (p q : P) (g h : G) (V A X : L)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (overlap : meet A X = d.iso h V) (anchor : d.iso h E ≤ meet A X) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    let original := ![cls Rc u, cls Rf w]
    let newPair := ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
    let oldPair := ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
    ∀ (_profiles : ∀ i, F i ⊆ b.carrier) (_bases : ∀ i, B i ⊆ F i)
      (_coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
      (_functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
      (_supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
      (_decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (original i).val p)
      (_equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
        tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
        ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (original i).val tau)
      (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (newPair i).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (oldPair i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (newPair i).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (oldPair i).val)
      (_single : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p)
      (_reference : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW q),
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q ∧
      stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val)
        (moved h u).val.val oldU.val.val (moved h w).val.val oldW.val.val (s.encode q) := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  let original : Fin 2 → (M.nameDomain s).names := ![cls Rc u, cls Rf w]
  let newPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
  let oldPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
  dsimp only
  intro profiles bases coinitial functions supported decisions equalities newSupport oldSupport newHS oldHS single reference
  have above : E ≤ V := (d.iso h).le_iff_le.1 (overlap ▸ anchor)
  have indexEq := M.niceRefinementIndex_copies_agree a s b d level T T2 valid valid2
    indices C E U Rf Rc member g h V above relative
  have fields := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 indexEq
  have fine : moved h Rf = moved g Rf := Subtype.ext (Subtype.ext fields.2.2.2.2.1)
  have coarse : moved h Rc = moved g Rc := Subtype.ext (Subtype.ext fields.2.2.2.2.2)
  have classLaw (k : G) (R v : (M.nameDomain s).names) :
      moved k (cls R v) = cls (moved k R) (moved k v) :=
    M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps
      order hT valid closed k R v
  have newLaw (i : Fin 2) : moved h (original i) = newPair i := by
    exact Fin.cases (classLaw h Rc u) (Fin.cases (classLaw h Rf w) (fun j => Fin.elim0 j)) i
  have shape (i : Fin 2) : (moved h (original i)).val.val ⊆ ZFSet.prod T s.carrier := by
    rw [newLaw]
    exact Fin.cases (Name.refinementClass_subset T valid (moved h Rc).val (moved h u).val)
      (Fin.cases (Name.refinementClass_subset T valid (moved h Rf).val (moved h w).val)
        (fun j => Fin.elim0 j)) i
  have transported := (M.stageOneProfile_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system h Rc Rf u w V p).2
    (single.2.1 V above)
  have profile : Forces (M.nameDomain s) refinementProfileFormula
      ![moved h (original 0), moved h (original 1),
        M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q := by
    rw [newLaw 0, newLaw 1]
    exact forces_mono (M.nameDomain s) _ _ transported qh
  have referenceFormula : Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (original 0), oldPair 0, moved g (original 1), oldPair 1] q := by
    change Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (cls Rc u), cls (moved h Rc) oldU,
        moved g (cls Rf w), cls (moved h Rf) oldW] q
    rw [classLaw g Rc u, classLaw g Rf w, ← fine, ← coarse]
    exact reference
  have forced := M.prepared_joint_mixed_collision_forces a s t b d pairing unions powers separation collection
    carrier group nodes supports maps hT valid closed base directed system meet descent small F B f
    original oldPair p q profiles bases coinitial functions supported decisions equalities g h V A X
    relative qh qg overlap (fun i => (newLaw i).symm ▸ newSupport i) oldSupport
    (fun i => (newLaw i).symm ▸ newHS i) oldHS shape profile referenceFormula
  have typed : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q := by
    rw [newLaw 0, newLaw 1] at forced
    exact forced
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 indices.family_ground h C E U Rf Rc).2 member
  refine ⟨typed, ?_⟩
  exact (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices (d.iso h C) (d.iso h E) (moved h U) (moved h Rf) (moved h Rc)
    (moved h u) oldU (moved h w) oldW movedMember q).2 typed

end TransitiveGround

namespace TransitiveGround
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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)
variable (meet : L → L → L)
variable (descent : ∀ (H : ConditionFilter P),
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

variable {T2 : ZFSet.{u}} (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed2 : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include group nodes supports closed closed2 descent indices in
theorem prepared_refinementCollision_tests (small : M.sets.Countable)
    (C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (F B f : Fin 2 → ZFSet.{u}) (p q : P) (g h : G) (V A X : L)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (overlap : meet A X = d.iso h V) (anchor : d.iso h E ≤ meet A X) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    let original := ![cls Rc u, cls Rf w]
    let newPair := ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
    let oldPair := ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
    ∀ (_profiles : ∀ i, F i ⊆ b.carrier) (_bases : ∀ i, B i ⊆ F i)
      (_coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
      (_functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
      (_supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
      (_decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (original i).val p)
      (_equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
        tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
        ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (original i).val tau)
      (_newSupport : ∀ i, d.principalFix A ≤ a.stabilizer s (newPair i).val)
      (_oldSupport : ∀ i, d.principalFix X ≤ a.stabilizer s (oldPair i).val)
      (_newHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (newPair i).val)
      (_oldHS : ∀ i, HereditarilySymmetric a s (d.principalSupportFamily base directed) (oldPair i).val)
      (_single : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p)
      (_reference : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW q),
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q ∧
      stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val)
        (moved h u).val.val oldU.val.val (moved h w).val.val oldW.val.val (s.encode q) := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  let original : Fin 2 → (M.nameDomain s).names := ![cls Rc u, cls Rf w]
  let newPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
  let oldPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
  dsimp only
  intro profiles bases coinitial functions supported decisions equalities newSupport oldSupport newHS oldHS single reference
  have above : E ≤ V := (d.iso h).le_iff_le.1 (overlap ▸ anchor)
  have indexEq := M.niceRefinementIndex_copies_agree a s b d level T T2 valid valid2
    indices C E U Rf Rc member g h V above relative
  have fields := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 indexEq
  have fine : moved h Rf = moved g Rf := Subtype.ext (Subtype.ext fields.2.2.2.2.1)
  have coarse : moved h Rc = moved g Rc := Subtype.ext (Subtype.ext fields.2.2.2.2.2)
  have classLaw (k : G) (R v : (M.nameDomain s).names) :
      moved k (cls R v) = cls (moved k R) (moved k v) :=
    M.stageOneNameAction_class a s t pairing unions powers separation collection carrier maps
      order hT valid closed k R v
  have newLaw (i : Fin 2) : moved h (original i) = newPair i := by
    exact Fin.cases (classLaw h Rc u) (Fin.cases (classLaw h Rf w) (fun j => Fin.elim0 j)) i
  have shape (i : Fin 2) : (moved h (original i)).val.val ⊆ ZFSet.prod T s.carrier := by
    rw [newLaw]
    exact Fin.cases (Name.refinementClass_subset T valid (moved h Rc).val (moved h u).val)
      (Fin.cases (Name.refinementClass_subset T valid (moved h Rf).val (moved h w).val)
        (fun j => Fin.elim0 j)) i
  have transported := (M.stageOneProfile_act_iff a s t pairing unions powers separation collection
    carrier order maps hT valid closed b d base directed system h Rc Rf u w V p).2
    (single.2.1 V above)
  have profile : Forces (M.nameDomain s) refinementProfileFormula
      ![moved h (original 0), moved h (original 1),
        M.stageOneVisibilityName s valid a b d base directed system (d.iso h V)] q := by
    rw [newLaw 0, newLaw 1]
    exact forces_mono (M.nameDomain s) _ _ transported qh
  have referenceFormula : Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (original 0), oldPair 0, moved g (original 1), oldPair 1] q := by
    change Forces (M.nameDomain s) refinementCollisionFormula
      ![moved g (cls Rc u), cls (moved h Rc) oldU,
        moved g (cls Rf w), cls (moved h Rf) oldW] q
    rw [classLaw g Rc u, classLaw g Rf w, ← fine, ← coarse]
    exact reference
  have forced := M.prepared_mixed_collision_forces a s t b d pairing unions powers separation collection
    carrier group nodes supports maps hT valid closed base directed system meet descent small F B f
    original oldPair p q profiles bases coinitial functions supported decisions equalities g h V A X
    relative qh qg overlap (fun i => (newLaw i).symm ▸ newSupport i) oldSupport
    (fun i => (newLaw i).symm ▸ newHS i) oldHS shape profile referenceFormula
  have typed : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
      (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q := by
    rw [newLaw 0, newLaw 1] at forced
    exact forced
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 indices.family_ground h C E U Rf Rc).2 member
  refine ⟨typed, ?_⟩
  exact (M.refinementLevelRawCollision_iff a s b d level pairing unions powers separation collection
    carrier order hT valid indices (d.iso h C) (d.iso h E) (moved h U) (moved h Rf) (moved h Rc)
    (moved h u) oldU (moved h w) oldW movedMember q).2 typed

end TransitiveGround

namespace TransitiveGround
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
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets)
variable (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
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

variable {T2 : ZFSet.{u}} (valid2 : ∀ z ∈ T2, IsName s z)
variable (closed2 : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2)
variable (level : ZFSet.{u})
variable (indices : NiceRefinementIndexSystem M a s b d level T T2 valid valid2)

include group nodes supports closed closed2 descent indices in
theorem prepared_joint_refinementCollision_of_position_supports (small : M.sets.Countable)
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (C E : L) (U Rf Rc u w oldU oldW : (M.nameDomain s).names)
    (member : refinementIndexCode level (b.encode C) (b.encode E)
      U.val.val Rf.val.val Rc.val.val ∈ M.niceRefinementIndices a s b d level T T2 valid)
    (F B f : Fin 2 → ZFSet.{u}) (p q : P) (g h : G) (V A X : L)
    (relative : g⁻¹ * h ∈ d.principalFix V)
    (qh : q ≤ a.iso h p) (qg : q ≤ a.iso g p)
    (overlap : meet A X = d.iso h V) (anchor : d.iso h E ≤ meet A X)
    (meetLeft : meet A X ≤ A) (meetRight : meet A X ≤ X) :
    let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
    let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
    let original := ![cls Rc u, cls Rf w]
    ∀ (_profiles : ∀ i, F i ⊆ b.carrier) (_bases : ∀ i, B i ⊆ F i)
      (_coinitial : ∀ i, ∀ x ∈ F i, ∃ v ∈ B i, ZFSet.pair v x ∈ b.conditionOrder)
      (_functions : ∀ i, ZFSet.IsFunc (B i) (M.niceSupportNameCodes a s T d.principalFix) (f i))
      (_supported : ∀ i, f i ⊆ M.niceSupportRelation a s b T d.principalFix)
      (_decisions : ∀ i, M.DecidesVisibilityProfile a s b d.principalFix T (F i) (original i).val p)
      (_equalities : ∀ i, ∀ v ∈ B i, ∀ tau : Name s,
        tau.val ∈ M.niceSupportNameCodes a s T d.principalFix →
        ZFSet.pair v tau.val ∈ f i → Name.ForcesEq p (original i).val tau)
      (_newPositions : ∀ i : Fin 2, d.principalFix A ≤
        a.stabilizer s (![ (moved h u).val, (moved h w).val ] i))
      (_oldPositions : ∀ i : Fin 2, d.principalFix X ≤
        a.stabilizer s (![oldU.val, oldW.val] i))
      (_single : M.stageOneSingleTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system C E U Rf Rc u w p)
      (_reference : M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved g u) oldU (moved g w) oldW q),
      M.stageOneCollisionTest s pairing unions powers separation collection carrier order hT valid
        (moved h Rf) (moved h Rc) (moved h u) oldU (moved h w) oldW q ∧
      stageOneRawCollision M (M.refinementLevelFormulaData a s b d level T T2 valid)
        (refinementIndexCode level (b.encode (d.iso h C)) (b.encode (d.iso h E))
          (moved h U).val.val (moved h Rf).val.val (moved h Rc).val.val)
        (moved h u).val.val oldU.val.val (moved h w).val.val oldW.val.val (s.encode q) := by
  let cls := M.stageOneClassName s pairing unions powers separation collection carrier order hT valid
  let moved := M.stageOneNameAction a s t pairing unions powers separation collection carrier maps
  let newPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) (moved h u), cls (moved h Rf) (moved h w)]
  let oldPair : Fin 2 → (M.nameDomain s).names :=
    ![cls (moved h Rc) oldU, cls (moved h Rf) oldW]
  dsimp only
  intro profiles bases coinitial functions supported decisions equalities newPositions oldPositions single reference
  have movedMember := (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
    carrier order maps level T T2 valid closed closed2 indices.family_ground h C E U Rf Rc).2 member
  have newSupports := M.niceRefinementClasses_supported_by_block a s b d level T T2 valid valid2
    indices base directed closed children (d.iso h C) (d.iso h E) A
    (moved h U) (moved h Rf) (moved h Rc) movedMember (anchor.trans meetLeft)
    ![(moved h u).val, (moved h w).val] newPositions
  have oldSupports := M.niceRefinementClasses_supported_by_block a s b d level T T2 valid valid2
    indices base directed closed children (d.iso h C) (d.iso h E) X
    (moved h U) (moved h Rf) (moved h Rc) movedMember (anchor.trans meetRight)
    ![oldU.val, oldW.val] oldPositions
  have newFacts : ∀ i, d.principalFix A ≤ a.stabilizer s (newPair i).val ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed) (newPair i).val :=
    Fin.cases (newSupports 0) (Fin.cases (newSupports 1) (fun j => Fin.elim0 j))
  have oldFacts : ∀ i, d.principalFix X ≤ a.stabilizer s (oldPair i).val ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed) (oldPair i).val :=
    Fin.cases (oldSupports 0) (Fin.cases (oldSupports 1) (fun j => Fin.elim0 j))
  exact M.prepared_joint_refinementCollision_tests a s t b d pairing unions powers separation collection
    carrier order group nodes supports maps hT valid closed base directed system meet descent
    valid2 closed2 level indices small C E U Rf Rc u w oldU oldW member F B f p q g h V A X
    relative qh qg overlap anchor profiles bases coinitial functions supported decisions equalities
    (fun i => (newFacts i).1) (fun i => (oldFacts i).1)
    (fun i => (newFacts i).2) (fun i => (oldFacts i).2) single reference

end TransitiveGround

end PartitionPilot.Forcing

end OAI
