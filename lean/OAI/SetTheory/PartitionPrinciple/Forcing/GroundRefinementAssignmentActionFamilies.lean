import OAI.SetTheory.PartitionPrinciple.Definability.GroundRelationProductFamilies
import OAI.SetTheory.PartitionPrinciple.Definability.RefinementIndexActionFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundNiceRefinementIndexActionLaws

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)

theorem realize_refinementIndexActionFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (level : ZFSet.{u}) (hl : level ∈ M.sets) (g : G) (C E C' E' : L)
    (U Rf Rc U' Rf' Rc' : (M.nameDomain s).names) :
    Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5)
      ![refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val,
        refinementIndexCode level (b.encode C') (b.encode E') U'.val.val Rf'.val.val Rc'.val.val,
        t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      d.iso g C = C' ∧ d.iso g E = E' ∧ a.act s g U.val = U'.val ∧
        a.act s g Rf.val = Rf'.val ∧ a.act s g Rc.val = Rc'.val := by
  let oldFields : Fin 6 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val]
  let newFields : Fin 6 → ZFSet.{u} := ![level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val]
  have groundNodes (c : L) := M.transitive nodes (b.encode_mem c)
  have oldGround : ∀ j, oldFields j ∈ M.sets :=
    Fin.cases hl (Fin.cases (groundNodes C) (Fin.cases (groundNodes E)
      (Fin.cases U.property (Fin.cases Rf.property (Fin.cases Rc.property (fun j => Fin.elim0 j))))))
  have newGround : ∀ j, newFields j ∈ M.sets :=
    Fin.cases hl (Fin.cases (groundNodes C') (Fin.cases (groundNodes E')
      (Fin.cases U'.property (Fin.cases Rf'.property (Fin.cases Rc'.property (fun j => Fin.elim0 j))))))
  let env : Fin 6 → ZFSet.{u} := ![nonemptyTupleCode 5 oldFields, nonemptyTupleCode 5 newFields,
    t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t]
  have envGround : ∀ j, env j ∈ M.sets :=
    Fin.cases (M.nonemptyTupleCode_mem pairing 5 oldFields oldGround)
      (Fin.cases (M.nonemptyTupleCode_mem pairing 5 newFields newGround)
      (Fin.cases (M.transitive group (t.encode_mem g)) (Fin.cases carrier
      (Fin.cases maps (Fin.cases nodeMaps (fun j => Fin.elim0 j))))))
  change Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5) env ↔ _
  rw [refinementIndexActionFormula, realize_exBlock]
  have raw (w : Fin 13 → ZFSet.{u}) (ground : ∀ j, w j ∈ M.sets) :=
    M.realize_refinementIndexActionRawFormula pairing
      (suffixIndex 6 13 0) (suffixIndex 6 13 1) (suffixIndex 6 13 2)
      (suffixIndex 6 13 3) (suffixIndex 6 13 4) (suffixIndex 6 13 5)
      (prefixIndex 6 13) (extendMany 13 w env) (extendMany_members 13 w env ground envGround)
  simp only [extendMany_prefix, extendMany_suffix] at raw
  constructor
  · rintro ⟨w, ground, formula⟩
    obtain ⟨oldEq, newEq, _, nodeEntry, ce, ee, ue, fe, re⟩ := (raw w ground).1 formula
    have oldAt (j : Fin 6) : w (j.castAdd 7) = oldFields j :=
      (congrFun (nonemptyTupleCode_injective 5 oldEq) j).symm
    have newAt (j : Fin 6) : w ((Fin.natAdd 6 j).castAdd 1) = newFields j :=
      (congrFun (nonemptyTupleCode_injective 5 newEq) j).symm
    have graphEq := (d.pair_mem_conditionMapFamily b t g (w 12)).1 nodeEntry
    have cEq : w 1 = b.encode C := oldAt 1
    have eEq : w 2 = b.encode E := oldAt 2
    have uEq : w 3 = U.val.val := oldAt 3
    have fEq : w 4 = Rf.val.val := oldAt 4
    have rEq : w 5 = Rc.val.val := oldAt 5
    have cEq' : w 7 = b.encode C' := newAt 1
    have eEq' : w 8 = b.encode E' := newAt 2
    have uEq' : w 9 = U'.val.val := newAt 3
    have fEq' : w 10 = Rf'.val.val := newAt 4
    have rEq' : w 11 = Rc'.val.val := newAt 5
    rw [cEq, cEq', graphEq] at ce
    rw [eEq, eEq', graphEq] at ee
    rw [uEq, uEq'] at ue
    rw [fEq, fEq'] at fe
    rw [rEq, rEq'] at re
    exact ⟨(b.pair_mem_graph b (d.iso g) C C').1 ce,
      (b.pair_mem_graph b (d.iso g) E E').1 ee,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g U.val U'.val U.property U'.property).1 ue,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rf.val Rf'.val Rf.property Rf'.property).1 fe,
      (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rc.val Rc'.val Rc.property Rc'.property).1 re⟩
  · rintro ⟨ce, ee, ue, fe, re⟩
    let w : Fin 13 → ZFSet.{u} := ![level, b.encode C, b.encode E, U.val.val, Rf.val.val, Rc.val.val,
      level, b.encode C', b.encode E', U'.val.val, Rf'.val.val, Rc'.val.val, b.graph b (d.iso g)]
    have ground : ∀ j, w j ∈ M.sets :=
      Fin.cases hl (Fin.cases (groundNodes C) (Fin.cases (groundNodes E)
      (Fin.cases U.property (Fin.cases Rf.property (Fin.cases Rc.property
      (Fin.cases hl (Fin.cases (groundNodes C') (Fin.cases (groundNodes E')
      (Fin.cases U'.property (Fin.cases Rf'.property (Fin.cases Rc'.property
      (Fin.cases (M.conditionMap_graph_mem d b t nodeMaps g) (fun j => Fin.elim0 j)))))))))))))
    refine ⟨w, ground, (raw w ground).2 ⟨?_, ?_, rfl,
      (d.pair_mem_conditionMapFamily b t g _).2 rfl,
      (b.pair_mem_graph b (d.iso g) C C').2 ce,
      (b.pair_mem_graph b (d.iso g) E E').2 ee, ?_, ?_, ?_⟩⟩
    · apply congrArg (nonemptyTupleCode 5)
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    · apply congrArg (nonemptyTupleCode 5)
      funext j
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
        (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g U.val U'.val U.property U'.property).2 ue
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rf.val Rf'.val Rf.property Rf'.property).2 fe
    · exact (M.realize_nameActionFormula a s t pairing unions powers separation collection
        carrier group maps g Rc.val Rc'.val Rc.property Rc'.property).2 re

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementIndexActionEntryFormula : SetFormula 6 :=
  .ex (.ex (.conj (.mem 1 4) (.conj (.mem 0 4)
    (.conj (orderedPairFormula 2 1 0)
      (reindex ![1, 0, 3, 5, 6, 7] (refinementIndexActionFormula 0 1 2 3 4 5))))))

def refinementIndexActionSetFormula : SetFormula 6 :=
  exactSetFormula 0 (reindex (extend 0 (fun j : Fin 5 => j.succ.succ)) refinementIndexActionEntryFormula)

end SetFormula
namespace TransitiveGround
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

theorem realize_refinementIndexActionEntryFormula (g : G) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets refinementIndexActionEntryFormula
      ![z, t.encode g, M.niceRefinementIndices a s b d level T1 T2 valid1,
        s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      z ∈ M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  have action (x y : ZFSet.{u}) (hx : x ∈ I) (hy : y ∈ I) :
      Realize M.sets (refinementIndexActionFormula 0 1 2 3 4 5)
        ![x, y, t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      ZFSet.pair x y ∈ M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
    obtain ⟨C, E, U, Rf, Rc, rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hx
    obtain ⟨C', E', U', Rf', Rc', rfl⟩ := M.exists_niceRefinementIndex_fields a s b d level T1 T2 valid1 valid2 hy
    rw [M.realize_refinementIndexActionFormula a s t b d pairing unions powers separation collection
      carrier group nodes maps nodeMaps level hl g C E C' E' U Rf Rc U' Rf' Rc',
      M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
        pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
        g C E U Rf Rc hx, refinementIndexCode_eq_iff]
    constructor
    · rintro ⟨ce, ee, ue, fe, re⟩
      exact ⟨rfl, congrArg b.encode ce.symm, congrArg b.encode ee.symm,
        congrArg Subtype.val ue.symm, congrArg Subtype.val fe.symm, congrArg Subtype.val re.symm⟩
    · rintro ⟨_, ce, ee, ue, fe, re⟩
      exact ⟨b.injective ce.symm, b.injective ee.symm,
        Subtype.ext ue.symm, Subtype.ext fe.symm, Subtype.ext re.symm⟩
  let env : Fin 6 → ZFSet.{u} := ![z, t.encode g, I, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t]
  have args (x y : ZFSet.{u}) :
      (fun j : Fin 6 => (extend y (extend x env)) (![1, 0, 3, 5, 6, 7] j)) =
      ![x, y, t.encode g, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
  change Realize M.sets refinementIndexActionEntryFormula env ↔ _
  simp only [refinementIndexActionEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hxm, y, hym, hx, hy, paired, acted⟩
    have eq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).1 paired
    change z = ZFSet.pair x y at eq
    rw [realize_reindex, args] at acted
    exact eq.symm ▸ (action x y hx hy).1 acted
  · intro entry
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    have hxm := M.transitive indexGround hx
    have hym := M.transitive indexGround hy
    refine ⟨x, hxm, y, hym, hx, hy,
      (M.realize_orderedPairFormula pairing 2 1 0 _ hz hxm hym).2 eq, ?_⟩
    rw [realize_reindex, args]
    exact (action x y hx hy).2 (eq ▸ entry)

theorem realize_refinementIndexActionSetFormula
    (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets)
    (g : G) (F : ZFSet.{u}) (hF : F ∈ M.sets) :
    Realize M.sets refinementIndexActionSetFormula
      ![F, t.encode g, M.niceRefinementIndices a s b d level T1 T2 valid1,
        s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] ↔
      F = M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  have graphGround := M.niceRefinementIndexActionGraph_mem a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier maps nodeMaps hl hT1 hT2 indexGround g
  apply M.realize_exactSetFormula 0 _ _ hF (fun _ h => M.transitive graphGround h)
  intro z hz
  rw [realize_reindex, map_extend]
  exact M.realize_refinementIndexActionEntryFormula a s t b d pairing unions powers separation collection
    carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2 closed1 closed2 familyGround indexGround g z hz

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "J" => stageOneAssignments I T
local notation "indexGraph" => M.niceRefinementIndexActionGraph a s b d ∅ T T2 valid valid2
local notation "termGraph" => Name.renameFamilyGraph s (a.iso ·) T valid

noncomputable def stageOneAssignmentActionGraph (g : G) : ZFSet.{u} :=
  relationProduct I (ZFSet.prod T T) I (ZFSet.prod T T) (indexGraph g)
    (relationProduct T T T T (Name.renameFamilyGraph s (a.iso g) T valid)
      (Name.renameFamilyGraph s (a.iso g) T valid))

theorem pair_mem_stageOneAssignmentActionGraph (g : G) (i u w i' u' w' : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) (stageOneAssignment i' u' w') ∈
      M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g ↔
    i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ i' ∈ I ∧ u' ∈ T ∧ w' ∈ T ∧
      ZFSet.pair i i' ∈ indexGraph g ∧
      ZFSet.pair u u' ∈ Name.renameFamilyGraph s (a.iso g) T valid ∧
      ZFSet.pair w w' ∈ Name.renameFamilyGraph s (a.iso g) T valid := by
  simp only [stageOneAssignmentActionGraph, stageOneAssignment,
    pair_mem_relationProduct, ZFSet.pair_mem_prod]
  tauto

variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

omit [OrderTop P] in
include closed in
theorem stageOneTermAction_function (g : G) :
    ZFSet.IsFunc T T (Name.renameFamilyGraph s (a.iso g) T valid) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := (Name.mem_renameFamilyGraph s (a.iso g) T valid z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hw, closed g w hw⟩
  · intro x hx
    let w : Name s := ⟨x, valid x hx⟩
    refine ⟨(a.act s g w).val,
      (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w _).2 ⟨hx, rfl⟩, ?_⟩
    intro y hy
    exact ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w y).1 hy).2

omit [OrderTop P] in
include closed in
theorem stageOneTermAction_injection (g : G) :
    InjectionCode T T (Name.renameFamilyGraph s (a.iso g) T valid) := by
  refine ⟨stageOneTermAction_function a s T valid closed g, ?_⟩
  intro x y z hx hy
  have func := stageOneTermAction_function a s T valid closed g
  let wx : Name s := ⟨x, valid x (ZFSet.pair_mem_prod.1 (func.1 hx)).1⟩
  let wy : Name s := ⟨y, valid y (ZFSet.pair_mem_prod.1 (func.1 hy)).1⟩
  have ex := ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid wx z).1 hx).2
  have ey := ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid wy z).1 hy).2
  have equal : a.act s g wx = a.act s g wy := Subtype.ext (ex.symm.trans ey)
  exact congrArg Subtype.val ((a.nameEquiv s g).injective equal)

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem stageOneAssignmentActionGraph_function (g : G) :
    ZFSet.IsFunc J J (M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g) :=
  relationProduct_function
    (M.niceRefinementIndexActionGraph_function a s b d ∅ T T2 valid valid2 t
      pairing unions powers separation collection carrier order maps closed closed2 familyGround g)
    (relationProduct_function (stageOneTermAction_function a s T valid closed g)
      (stageOneTermAction_function a s T valid closed g))

include pairing unions powers separation collection carrier maps in
theorem stageOneAssignmentActionGraph_mem
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI : I ∈ M.sets) (g : G) :
    M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g ∈ M.sets := by
  have hi := M.niceRefinementIndexActionGraph_mem a s b d ∅ T T2 valid valid2 t
    pairing unions powers separation collection carrier maps nodeMaps (M.empty_mem ⟨T, hT⟩) hT hT2 hI g
  have ht := M.renameFamilyGraph_mem s s pairing unions powers separation collection carrier carrier
    (a.iso g) (M.conditionMap_graph_mem a s t maps g) T hT valid
  have htt := M.prod_mem pairing unions powers separation hT hT
  exact M.relationProduct_mem pairing unions powers separation hI htt hI htt hi
    (M.relationProduct_mem pairing unions powers separation hT hT hT hT ht ht)

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem stageOneAssignmentActionGraph_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val) y ∈
      M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g ↔
    y = stageOneAssignment (refinementIndexCode ∅ (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val := by
  have idx := M.niceRefinementIndexActionGraph_entry a s b d ∅ T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g C E U Rf Rc index
  constructor
  · intro entry
    have func := M.stageOneAssignmentActionGraph_function a s b d T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround g
    obtain ⟨i', _, u', _, w', _, rfl⟩ := (mem_stageOneAssignments I T y).1
      (ZFSet.pair_mem_prod.1 (func.1 entry)).2
    obtain ⟨_, _, _, _, _, _, ei, eu, ew⟩ :=
      (M.pair_mem_stageOneAssignmentActionGraph a s b d T T2 valid valid2 g _ _ _ _ _ _).1 entry
    rw [(idx i').1 ei, ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u u').1 eu).2,
      ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w w').1 ew).2]
    rfl
  · rintro rfl
    apply (M.pair_mem_stageOneAssignmentActionGraph a s b d T T2 valid valid2 g _ _ _ _ _ _).2
    refine ⟨index, hu, hw, ?_, closed g u hu, closed g w hw, (idx _).2 rfl, ?_, ?_⟩
    · exact (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
        carrier order maps ∅ T T2 valid closed closed2 familyGround g C E U Rf Rc).2 index
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u _).2 ⟨hu, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w _).2 ⟨hw, rfl⟩

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace SetFormula

def refinementIndexActionFamilyEntryFormula : SetFormula 6 :=
  .ex (.ex (.conj (.mem 1 3) (.conj (orderedPairFormula 2 1 0)
    (reindex ![0, 1, 4, 5, 6, 7] refinementIndexActionSetFormula))))

end SetFormula
namespace TransitiveGround
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (level T1 T2 : ZFSet.{u})
variable (valid1 : ∀ z ∈ T1, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)

noncomputable def niceRefinementIndexActionFamily : ZFSet.{u} :=
  familyCodeGraph t.encode (M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2)

noncomputable def niceRefinementIndexFullActionGraph : ZFSet.{u} :=
  mapFamilyApplicationGraph t.carrier
    (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndices a s b d level T1 T2 valid1)
    (M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2)

theorem pair_mem_niceRefinementIndexActionFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 ↔
      F = M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g :=
  pair_mem_familyCodeGraph _ _ t.injective g F

theorem niceRefinementIndexActionFamily_function :
    FunctionGraphOn t.carrier (M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2) := by
  have equal : ZFSet.range t.encode = t.carrier := by
    apply ZFSet.ext
    intro x
    exact ZFSet.mem_range.trans (t.mem_carrier x).symm
  simpa only [niceRefinementIndexActionFamily, equal] using familyCodeGraph_function t.encode
    (M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2) t.injective

theorem pair_mem_niceRefinementIndexFullActionGraph (g : G) (x y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) x) y ∈
      M.niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2 ↔
      ZFSet.pair x y ∈ M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2 g := by
  rw [niceRefinementIndexFullActionGraph, pair_mem_mapFamilyApplicationGraph]
  constructor
  · rintro ⟨_, _, _, F, indexed, entry⟩
    exact (M.pair_mem_niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 g F).1 indexed ▸ entry
  · intro entry
    have bounds := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 entry).1
    exact ⟨t.encode_mem g, bounds.1, bounds.2, _,
      (M.pair_mem_niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 g _).2 rfl, entry⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
variable (hl : level ∈ M.sets)
variable (closed1 : ∀ g (w : Name s), w.val ∈ T1 → (a.act s g w).val ∈ T1)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T1 valid1).val ∈ M.sets)
variable (indexGround : M.niceRefinementIndices a s b d level T1 T2 valid1 ∈ M.sets)
include pairing unions powers separation collection carrier group nodes order maps nodeMaps hl closed1 closed2 familyGround indexGround

theorem niceRefinementIndexActionFamily_mem (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) :
    M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 ∈ M.sets := by
  let I := M.niceRefinementIndices a s b d level T1 T2 valid1
  let values := M.niceRefinementIndexActionGraph a s b d level T1 T2 valid1 valid2
  have graphGround (g : G) := M.niceRefinementIndexActionGraph_mem a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier maps nodeMaps hl hT1 hT2 indexGround g
  have graphBound (g : G) : values g ∈ M.groundRelations I I :=
    (M.mem_groundRelations I I _).2 ⟨graphGround g, fun _ h => (ZFSet.mem_sep.1 h).1⟩
  let params : Fin 5 → ZFSet.{u} := ![t.carrier, I, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t]
  have paramsGround : ∀ j, params j ∈ M.sets := Fin.cases group (Fin.cases indexGround
    (Fin.cases carrier (Fin.cases maps (Fin.cases nodeMaps (fun j => Fin.elim0 j)))))
  have args (z raw F : ZFSet.{u}) :
      (fun j : Fin 6 => (extend F (extend raw (extend z params))) (![0, 1, 4, 5, 6, 7] j)) =
      ![F, raw, I, s.carrier, a.conditionMapFamily s t, d.conditionMapFamily b t] := by
    funext j
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))))) j
  have meaning (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets refinementIndexActionFamilyEntryFormula (extend z params) ↔
      z ∈ M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 := by
    simp only [refinementIndexActionFamilyEntryFormula, realize_ex]
    constructor
    · rintro ⟨raw, hr, F, hF, actor, paired, coded⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier raw).1 actor
      have pairEq := (M.realize_orderedPairFormula pairing 2 1 0 _ hz hr hF).1 paired
      change z = ZFSet.pair (t.encode g) F at pairEq
      rw [realize_reindex, args] at coded
      have equal := (M.realize_refinementIndexActionSetFormula a s t b d pairing unions powers separation
        collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2 closed1 closed2
        familyGround indexGround hT1 hT2 g F hF).1 coded
      exact (mem_familyCodeGraph _ _ z).2 ⟨g, by simpa only [equal] using pairEq.symm⟩
    · intro member
      obtain ⟨g, rfl⟩ := (mem_familyCodeGraph _ _ z).1 member
      have hg := M.transitive group (t.encode_mem g)
      refine ⟨t.encode g, hg, values g, graphGround g, t.encode_mem g,
        (M.realize_orderedPairFormula pairing 2 1 0 _ hz hg (graphGround g)).2 rfl, ?_⟩
      rw [realize_reindex, args]
      exact (M.realize_refinementIndexActionSetFormula a s t b d pairing unions powers separation
        collection carrier group nodes order maps nodeMaps level T1 T2 hl valid1 valid2 closed1 closed2
        familyGround indexGround hT1 hT2 g (values g) (graphGround g)).2 rfl
  let B := ZFSet.prod t.carrier (M.groundRelations I I)
  have hB := M.prod_mem pairing unions powers separation group
    (M.groundRelations_mem pairing unions powers separation indexGround indexGround)
  have subset : M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 ⊆ B := by
    intro z hz
    obtain ⟨g, rfl⟩ := (mem_familyCodeGraph _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨t.encode_mem g, graphBound g⟩
  have equal : ZFSet.sep (fun z => Realize M.sets refinementIndexActionFamilyEntryFormula
      (extend z params)) B = M.niceRefinementIndexActionFamily a s t b d level T1 T2 valid1 valid2 := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (meaning z (M.transitive hB h.1)).1 h.2,
      fun h => ⟨subset h, (meaning z (M.transitive hB (subset h))).2 h⟩⟩
  exact equal ▸ M.separation_mem separation refinementIndexActionFamilyEntryFormula params paramsGround hB

theorem niceRefinementIndexFullActionGraph_mem (hT1 : T1 ∈ M.sets) (hT2 : T2 ∈ M.sets) :
    M.niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2 ∈ M.sets :=
  M.mapFamilyApplicationGraph_mem pairing unions powers separation group indexGround indexGround
    (M.niceRefinementIndexActionFamily_mem a s t b d level T1 T2 valid1 valid2 pairing unions powers
      separation collection carrier group nodes order maps nodeMaps hl closed1 closed2 familyGround indexGround hT1 hT2)

omit group nodes nodeMaps hl indexGround in
theorem niceRefinementIndexFullActionGraph_function :
    ZFSet.IsFunc (ZFSet.prod t.carrier (M.niceRefinementIndices a s b d level T1 T2 valid1))
      (M.niceRefinementIndices a s b d level T1 T2 valid1)
      (M.niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2) := by
  refine ⟨?_, ?_⟩
  · intro z h
    unfold niceRefinementIndexFullActionGraph mapFamilyApplicationGraph at h
    exact (ZFSet.mem_sep.1 h).1
  intro raw member
  obtain ⟨actor, ha, x, hx, rfl⟩ := ZFSet.mem_prod.1 member
  obtain ⟨g, rfl⟩ := (t.mem_carrier actor).1 ha
  have fiber :=  M.niceRefinementIndexActionGraph_function a s b d level T1 T2 valid1 valid2 t
    pairing unions powers separation collection carrier order maps closed1 closed2 familyGround g
  obtain ⟨y, entry, unique⟩ := fiber.2 x hx
  have meaning := M.pair_mem_niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2 g x
  exact ⟨y, (meaning y).2 entry, fun z hz => unique z ((meaning z).1 hz)⟩

omit group nodes nodeMaps hl indexGround in
theorem niceRefinementIndexFullActionGraph_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names)
    (source : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d level T1 T2 valid1) (y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g)
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val)) y ∈
      M.niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2 ↔
      y = refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
        (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val :=
  (M.pair_mem_niceRefinementIndexFullActionGraph a s t b d level T1 T2 valid1 valid2 g _ y).trans
    (M.niceRefinementIndexActionGraph_entry a s b d level T1 T2 valid1 valid2 t
      pairing unions powers separation collection carrier order maps closed1 closed2 familyGround
      g C E U Rf Rc source y)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "J" => stageOneAssignments I T
local notation "indexGraph" => M.niceRefinementIndexActionGraph a s b d level T T2 valid valid2
local notation "termGraph" => Name.renameFamilyGraph s (a.iso ·) T valid

noncomputable def refinementAssignmentActionGraph (g : G) : ZFSet.{u} :=
  relationProduct I (ZFSet.prod T T) I (ZFSet.prod T T) (indexGraph g)
    (relationProduct T T T T (Name.renameFamilyGraph s (a.iso g) T valid)
      (Name.renameFamilyGraph s (a.iso g) T valid))

theorem pair_mem_refinementAssignmentActionGraph (g : G) (i u w i' u' w' : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment i u w) (stageOneAssignment i' u' w') ∈
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g ↔
    i ∈ I ∧ u ∈ T ∧ w ∈ T ∧ i' ∈ I ∧ u' ∈ T ∧ w' ∈ T ∧
      ZFSet.pair i i' ∈ indexGraph g ∧
      ZFSet.pair u u' ∈ Name.renameFamilyGraph s (a.iso g) T valid ∧
      ZFSet.pair w w' ∈ Name.renameFamilyGraph s (a.iso g) T valid := by
  simp only [refinementAssignmentActionGraph, stageOneAssignment,
    pair_mem_relationProduct, ZFSet.pair_mem_prod]
  tauto

theorem refinementAssignmentActionGraph_zero (g : G) :
    M.refinementAssignmentActionGraph a s b d ∅ T T2 valid valid2 g =
      M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g := rfl

variable (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)

variable (t : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
variable (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets)

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem refinementAssignmentActionGraph_function (g : G) :
    ZFSet.IsFunc J J (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g) :=
  relationProduct_function
    (M.niceRefinementIndexActionGraph_function a s b d level T T2 valid valid2 t
      pairing unions powers separation collection carrier order maps closed closed2 familyGround g)
    (relationProduct_function (stageOneTermAction_function a s T valid closed g)
      (stageOneTermAction_function a s T valid closed g))

include pairing unions powers separation collection carrier maps in
theorem refinementAssignmentActionGraph_mem
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hLevel : level ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (hI : I ∈ M.sets) (g : G) :
    M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g ∈ M.sets := by
  have hi := M.niceRefinementIndexActionGraph_mem a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier maps nodeMaps hLevel hT hT2 hI g
  have ht := M.renameFamilyGraph_mem s s pairing unions powers separation collection carrier carrier
    (a.iso g) (M.conditionMap_graph_mem a s t maps g) T hT valid
  have htt := M.prod_mem pairing unions powers separation hT hT
  exact M.relationProduct_mem pairing unions powers separation hI htt hI htt hi
    (M.relationProduct_mem pairing unions powers separation hT hT hT hT ht ht)

include closed closed2 familyGround pairing unions powers separation collection carrier order maps in
theorem refinementAssignmentActionGraph_entry (g : G) (C E : L)
    (U Rf Rc : (M.nameDomain s).names) (u w : Name s)
    (index : refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈ I)
    (hu : u.val ∈ T) (hw : w.val ∈ T) (y : ZFSet.{u}) :
    ZFSet.pair (stageOneAssignment
      (refinementIndexCode level (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val) u.val w.val) y ∈
      M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g ↔
    y = stageOneAssignment (refinementIndexCode level (b.encode (d.iso g C)) (b.encode (d.iso g E))
      (a.act s g U.val).val (a.act s g Rf.val).val (a.act s g Rc.val).val)
      (a.act s g u).val (a.act s g w).val := by
  have idx := M.niceRefinementIndexActionGraph_entry a s b d level T T2 valid valid2 t
    pairing unions powers separation collection carrier order maps closed closed2 familyGround g C E U Rf Rc index
  constructor
  · intro entry
    have func := M.refinementAssignmentActionGraph_function a s b d level T T2 valid valid2 closed t
      pairing unions powers separation collection carrier order maps closed2 familyGround g
    obtain ⟨i', _, u', _, w', _, rfl⟩ := (mem_stageOneAssignments I T y).1
      (ZFSet.pair_mem_prod.1 (func.1 entry)).2
    obtain ⟨_, _, _, _, _, _, ei, eu, ew⟩ :=
      (M.pair_mem_refinementAssignmentActionGraph a s b d level T T2 valid valid2 g _ _ _ _ _ _).1 entry
    rw [(idx i').1 ei, ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u u').1 eu).2,
      ((Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w w').1 ew).2]
    rfl
  · rintro rfl
    apply (M.pair_mem_refinementAssignmentActionGraph a s b d level T T2 valid valid2 g _ _ _ _ _ _).2
    refine ⟨index, hu, hw, ?_, closed g u hu, closed g w hw, (idx _).2 rfl, ?_, ?_⟩
    · exact (M.niceRefinementIndex_act_iff a s t b d pairing unions powers separation collection
        carrier order maps level T T2 valid closed closed2 familyGround g C E U Rf Rc).2 index
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid u _).2 ⟨hu, rfl⟩
    · exact (Name.pair_mem_renameFamilyGraph s (a.iso g) T valid w _).2 ⟨hw, rfl⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d ∅ T T2 valid
local notation "indexGraph" => M.niceRefinementIndexActionGraph a s b d ∅ T T2 valid valid2
local notation "termGraph" => fun g => Name.renameFamilyGraph s (a.iso g) T valid

noncomputable def stageOneAssignmentActionFamily : ZFSet.{u} :=
  familyCodeGraph t.encode (M.stageOneAssignmentActionGraph a s b d T T2 valid valid2)

theorem pair_mem_stageOneAssignmentActionFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ M.stageOneAssignmentActionFamily a s t b d T T2 valid valid2 ↔
      F = M.stageOneAssignmentActionGraph a s b d T T2 valid valid2 g :=
  pair_mem_familyCodeGraph _ _ t.injective g F

theorem stageOneAssignmentActionFamily_function :
    FunctionGraphOn t.carrier (M.stageOneAssignmentActionFamily a s t b d T T2 valid valid2) := by
  have equal : ZFSet.range t.encode = t.carrier := by
    apply ZFSet.ext
    intro x
    exact ZFSet.mem_range.trans (t.mem_carrier x).symm
  simpa only [stageOneAssignmentActionFamily, equal] using familyCodeGraph_function t.encode
    (M.stageOneAssignmentActionGraph a s b d T T2 valid valid2) t.injective

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem stageOneAssignmentActionFamily_mem
    (group : t.carrier ∈ M.sets) (hT : T ∈ M.sets) (indexGround : I ∈ M.sets)
    (indexFamily : M.niceRefinementIndexActionFamily a s t b d ∅ T T2 valid valid2 ∈ M.sets)
    (termFamily : a.termActionFamily s t T valid ∈ M.sets) :
    M.stageOneAssignmentActionFamily a s t b d T T2 valid valid2 ∈ M.sets := by
  have pairs := M.familyCodeGraph_relationProducts_mem t T T T T (termGraph) (termGraph)
    pairing unions powers separation group hT hT hT hT termFamily termFamily
  have hTT := M.prod_mem pairing unions powers separation hT hT
  exact M.familyCodeGraph_relationProducts_mem t I (ZFSet.prod T T) I (ZFSet.prod T T)
    (indexGraph) (fun g => relationProduct T T T T ((termGraph) g) ((termGraph) g))
    pairing unions powers separation group indexGround hTT indexGround hTT indexFamily pairs

theorem stageOneAssignmentActionFamily_mem_of_inputs
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (indexGround : I ∈ M.sets)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets) :
    M.stageOneAssignmentActionFamily a s t b d T T2 valid valid2 ∈ M.sets := by
  have indices := M.niceRefinementIndexActionFamily_mem a s t b d ∅ T T2 valid valid2
    pairing unions powers separation collection carrier group nodes order maps nodeMaps
    (M.empty_mem ⟨T,hT⟩) closed closed2 familyGround indexGround hT hT2
  have terms := M.termActionFamily_mem a s t T valid pairing unions powers separation
    collection carrier group maps hT closed
  exact M.stageOneAssignmentActionFamily_mem a s t b d T T2 valid valid2
    pairing unions powers separation group hT indexGround indices terms

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P L : Type u}
variable [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (level T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) (valid2 : ∀ z ∈ T2, IsName s z)
local notation "I" => M.niceRefinementIndices a s b d level T T2 valid
local notation "indexGraph" => M.niceRefinementIndexActionGraph a s b d level T T2 valid valid2
local notation "termGraph" => fun g => Name.renameFamilyGraph s (a.iso g) T valid

noncomputable def refinementAssignmentActionFamily : ZFSet.{u} :=
  familyCodeGraph t.encode (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2)

theorem pair_mem_refinementAssignmentActionFamily (g : G) (F : ZFSet.{u}) :
    ZFSet.pair (t.encode g) F ∈ M.refinementAssignmentActionFamily a s t b d level T T2 valid valid2 ↔
      F = M.refinementAssignmentActionGraph a s b d level T T2 valid valid2 g :=
  pair_mem_familyCodeGraph _ _ t.injective g F

theorem refinementAssignmentActionFamily_function :
    FunctionGraphOn t.carrier (M.refinementAssignmentActionFamily a s t b d level T T2 valid valid2) := by
  have equal : ZFSet.range t.encode = t.carrier := by
    apply ZFSet.ext
    intro x
    exact ZFSet.mem_range.trans (t.mem_carrier x).symm
  simpa only [refinementAssignmentActionFamily, equal] using familyCodeGraph_function t.encode
    (M.refinementAssignmentActionGraph a s b d level T T2 valid valid2) t.injective

theorem refinementAssignmentActionFamily_zero :
    M.refinementAssignmentActionFamily a s t b d ∅ T T2 valid valid2 =
      M.stageOneAssignmentActionFamily a s t b d T T2 valid valid2 := rfl

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem refinementAssignmentActionFamily_mem
    (group : t.carrier ∈ M.sets) (hT : T ∈ M.sets) (indexGround : I ∈ M.sets)
    (indexFamily : M.niceRefinementIndexActionFamily a s t b d level T T2 valid valid2 ∈ M.sets)
    (termFamily : a.termActionFamily s t T valid ∈ M.sets) :
    M.refinementAssignmentActionFamily a s t b d level T T2 valid valid2 ∈ M.sets := by
  have pairs := M.familyCodeGraph_relationProducts_mem t T T T T (termGraph) (termGraph)
    pairing unions powers separation group hT hT hT hT termFamily termFamily
  have hTT := M.prod_mem pairing unions powers separation hT hT
  exact M.familyCodeGraph_relationProducts_mem t I (ZFSet.prod T T) I (ZFSet.prod T T)
    (indexGraph) (fun g => relationProduct T T T T ((termGraph) g) ((termGraph) g))
    pairing unions powers separation group indexGround hTT indexGround hTT indexFamily pairs

theorem refinementAssignmentActionFamily_mem_of_inputs
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets)
    (maps : a.conditionMapFamily s t ∈ M.sets) (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hLevel : level ∈ M.sets) (hT : T ∈ M.sets) (hT2 : T2 ∈ M.sets) (indexGround : I ∈ M.sets)
    (closed : ∀ g (w : Name s), w.val ∈ T → (a.act s g w).val ∈ T)
    (closed2 : ∀ g (w : Name s), w.val ∈ T2 → (a.act s g w).val ∈ T2)
    (familyGround : (Name.familySet ⊤ T valid).val ∈ M.sets) :
    M.refinementAssignmentActionFamily a s t b d level T T2 valid valid2 ∈ M.sets := by
  have indices := M.niceRefinementIndexActionFamily_mem a s t b d level T T2 valid valid2
    pairing unions powers separation collection carrier group nodes order maps nodeMaps
    hLevel closed closed2 familyGround indexGround hT hT2
  have terms := M.termActionFamily_mem a s t T valid pairing unions powers separation
    collection carrier group maps hT closed
  exact M.refinementAssignmentActionFamily_mem a s t b d level T T2 valid valid2
    pairing unions powers separation group hT indexGround indices terms

end PartitionPilot.Forcing.TransitiveGround

end OAI
