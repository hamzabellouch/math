import OAI.SetTheory.PartitionPrinciple.Definability.TaskRepresentativeCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowAssignmentActions
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundFlatSuccessorAssignmentGraphs

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_actionSectionEntry (g : G) (z : ZFSet.{u})
    (hg : t.encode g ∈ M.sets) (hz : z ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) (carrier : s.carrier ∈ M.sets) :
    Realize M.sets (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula
      (extend z (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z ∈ s.graph s (a.iso g) :=
  (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hz (Fin.cases hg (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.actionSectionEntry_correct a s t g z)

theorem realize_actionSection (g : G) (F : ZFSet.{u})
    (hg : t.encode g ∈ M.sets) (hF : F ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) (carrier : s.carrier ∈ M.sets) :
    Realize M.sets (BoundedFormula.actionSectionFormula 0 1 2 3).toFormula
      (extend F (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        F = s.graph s (a.iso g) :=
  (BoundedFormula.realize_toFormula M _ _
    (Fin.cases hF (Fin.cases hg (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j)))))).trans
      (BoundedFormula.actionSection_correct a s t g F)

theorem actionGraph_section_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (graph : a.actionGraph s t ∈ M.sets)
    (g : G) (hg : t.encode g ∈ M.sets) : s.graph s (a.iso g) ∈ M.sets := by
  obtain ⟨B, hB, bounds⟩ := M.exists_pair_bound pairing unions powers carrier carrier
  let params := extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))
  have selected := M.separation_mem separation (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula
    params (Fin.cases hg (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j)))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.actionSectionEntryFormula 0 1 2 3).toFormula (extend z params)) B =
        s.graph s (a.iso g) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_actionSectionEntry a s t g z hg (M.transitive hB hz) graph carrier).1 rel
    · intro hz
      have hzB : z ∈ B := by
        obtain ⟨p, eq⟩ := (s.mem_graph s (a.iso g) z).1 hz
        exact eq ▸ bounds _ (s.encode_mem p) _ (s.encode_mem (a.iso g p))
      exact ⟨hzB, (M.realize_actionSectionEntry a s t g z hg (M.transitive hB hzB) graph carrier).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y G : Type u} [Group G] [PartialOrder X]
variable (a : PosetAction G X) (s : Presentation X) (t : Presentation Y) (b : Presentation G)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {N : ZFSet.{u}} (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets)
variable (hG : b.carrier ∈ M.sets) (hN : N ∈ M.sets) (graph : a.actionGraph s b ∈ M.sets)

noncomputable def smallFunctionAction :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    PosetAction G (SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) := by
  letI := M.smallFunctionOrder s.carrier t.carrier N
  have maps (g : G) : s.graph s (a.iso g).toEquiv ∈ M.sets :=
    M.actionGraph_section_mem a s b pairing unions powers separation hX graph g
      (M.transitive hG (b.encode_mem g))
  let iso (g : G) := M.renameSmallOrderIso s t pairing unions powers separation hX hY hN
    (a.iso g).toEquiv (maps g)
  have raw (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
      SetMembers.raw (iso g p) = graphRename s t (a.iso g).toEquiv (SetMembers.raw p) :=
    M.raw_renameSmallOrderIso s t pairing unions powers separation hX hY hN (a.iso g).toEquiv (maps g) p
  exact {
    iso := iso
    one := by
      intro p
      apply SetMembers.raw_injective
      rw [raw]
      have eq : (a.iso 1).toEquiv = Equiv.refl X := by
        apply Equiv.ext
        exact a.one
      rw [eq]
      exact graphRename_refl s t (M.smallFunction_raw_properties s.carrier t.carrier N p).2.1.shape
    mul := by
      intro g h p
      apply SetMembers.raw_injective
      rw [raw, raw, raw]
      have eq : (a.iso (g * h)).toEquiv = (a.iso h).toEquiv.trans (a.iso g).toEquiv := by
        apply Equiv.ext
        exact a.mul g h
      rw [eq]
      exact (graphRename_comp s t (a.iso h).toEquiv (a.iso g).toEquiv (SetMembers.raw p)).symm }

theorem raw_smallFunctionAction (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N)) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) =
      graphRename s t (a.iso g).toEquiv (SetMembers.raw p) := SetMembers.raw_ofMem _ _

theorem smallFunctionAction_entry (g : G) (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier N))
    (x : X) (y : Y) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    ZFSet.pair (s.encode (a.iso g x)) (t.encode y) ∈
      SetMembers.raw ((M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).iso g p) ↔
        ZFSet.pair (s.encode x) (t.encode y) ∈ SetMembers.raw p := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  rw [raw_smallFunctionAction, pair_mem_graphRename]
  change ZFSet.pair (s.encode ((a.iso g).toEquiv.symm ((a.iso g).toEquiv x))) (t.encode y) ∈ _ ↔ _
  rw [(a.iso g).toEquiv.symm_apply_apply]

end PartitionPilot.Forcing.TransitiveGround

section

namespace PartitionPilot.Forcing.SetFormula

def actionMapPairFormula : SetFormula 4 :=
  ex (.conj (BoundedFormula.orderedPairFormula 2 1 0).toFormula
    (BoundedFormula.actionSectionFormula 0 1 3 4).toFormula)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)

theorem realize_actionMapPairFormula (g : G) (z : ZFSet.{u})
    (hg : t.encode g ∈ M.sets) (hz : z ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) (carrier : s.carrier ∈ M.sets)
    (section_mem : s.graph s (a.iso g) ∈ M.sets) :
    Realize M.sets actionMapPairFormula
      (extend (t.encode g) (extend z (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) ↔
        z = ZFSet.pair (t.encode g) (s.graph s (a.iso g)) := by
  rw [actionMapPairFormula, realize_ex]
  constructor
  · rintro ⟨F, hF, pair, rel⟩
    have members : ∀ j, (extend F (extend (t.encode g) (extend z
        (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))))) j ∈ M.sets :=
      Fin.cases hF (Fin.cases hg (Fin.cases hz (Fin.cases graph
        (Fin.cases carrier (fun j => Fin.elim0 j)))))
    have shape := (BoundedFormula.truth_orderedPairFormula 2 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ members).1 pair)
    have raw := (BoundedFormula.realize_toFormula M _ _ members).1 rel
    change BoundedFormula.Truth (BoundedFormula.actionSectionFormula 0 1 2 3)
      (extend F (extend (t.encode g) (extend (a.actionGraph s t) (extend s.carrier Fin.elim0)))) at raw
    have eq := (BoundedFormula.actionSection_correct a s t g F).1 raw
    change z = ZFSet.pair (t.encode g) F at shape
    exact eq ▸ shape
  · intro eq
    refine ⟨s.graph s (a.iso g), section_mem, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases section_mem (Fin.cases hg
        (Fin.cases hz (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))))))).2
      exact (BoundedFormula.truth_orderedPairFormula 2 1 0 _).2 eq
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases section_mem (Fin.cases hg
        (Fin.cases hz (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))))))).2
      change BoundedFormula.Truth (BoundedFormula.actionSectionFormula 0 1 2 3)
        (extend (s.graph s (a.iso g)) (extend (t.encode g)
          (extend (a.actionGraph s t) (extend s.carrier Fin.elim0))))
      exact (BoundedFormula.actionSection_correct a s t g _).2 rfl

theorem conditionMapFamily_mem_of_actionGraph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (graph : a.actionGraph s t ∈ M.sets) : a.conditionMapFamily s t ∈ M.sets := by
  have hg (g : G) := M.transitive group (t.encode_mem g)
  have sections (g : G) := M.actionGraph_section_mem a s t pairing unions powers separation carrier graph g (hg g)
  let params := extend (a.actionGraph s t) (extend s.carrier Fin.elim0)
  apply M.definable_image_mem separation collection actionMapPairFormula params
    (Fin.cases graph (Fin.cases carrier (fun j => Fin.elim0 j))) group
  · intro z hz
    obtain ⟨g, eq⟩ := ZFSet.mem_range.1 hz
    exact eq ▸ M.orderedPair_mem pairing (hg g) (sections g)
  · intro z hz
    change z ∈ ZFSet.range (fun g : G => ZFSet.pair (t.encode g) (s.graph s (a.iso g))) ↔ _
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨g, eq⟩
      exact ⟨t.encode g, t.encode_mem g,
        (M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).2 eq.symm⟩
    · rintro ⟨x, hx, rel⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier x).1 hx
      exact ⟨g, ((M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).1 rel).symm⟩
  · intro x hx y hy z hz rely relz
    obtain ⟨g, rfl⟩ := (t.mem_carrier x).1 hx
    exact ((M.realize_actionMapPairFormula a s t g y (hg g) hy graph carrier (sections g)).1 rely).trans
      ((M.realize_actionMapPairFormula a s t g z (hg g) hz graph carrier (sections g)).1 relz).symm

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {G P L : Type u} [Group G] [PartialOrder P] [OrderTop P] [PartialOrder L]

structure StageOneActionParameters (M : TransitiveGround.{u}) (a : PosetAction G P)
    (s : Presentation P) (t : Presentation G) (b : Presentation L) (d : PosetAction G L)
    (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z) : Prop where
  condition_maps : a.conditionMapFamily s t ∈ M.sets
  node_maps : d.conditionMapFamily b t ∈ M.sets
  terms_closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T
  pairs_closed : ∀ g (tau : Name s), tau.val ∈ T2 → (a.act s g tau).val ∈ T2
  family_ground : (Name.familySet ⊤ T valid).val ∈ M.sets

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {L G : Type u} [PartialOrder L] [OrderBot L] [Group G]

noncomputable def rowPositionSequenceAction (a : PosetAction G L) (s : Presentation L)
    (g : G) (mu f : ZFSet.{u}) : ZFSet.{u} :=
  relationCompose mu s.nonbottom.carrier s.nonbottom.carrier f
    (s.nonbottom.graph s.nonbottom (a.nonbottom.iso g))

theorem pair_mem_rowPositionSequenceAction (a : PosetAction G L) (s : Presentation L)
    (g : G) (mu f i : ZFSet.{u}) (x : {x : L // x ≠ ⊥}) :
    ZFSet.pair i (s.encode (a.iso g x.val)) ∈ rowPositionSequenceAction a s g mu f ↔
      i ∈ mu ∧ ZFSet.pair i (s.encode x.val) ∈ f := by
  rw [rowPositionSequenceAction, pair_mem_relationCompose]
  constructor
  · rintro ⟨hi, _, y, hy, entry, moved⟩
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
    have equal := (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g)
      y (a.nonbottom.iso g x)).1 moved
    have same := (a.nonbottom.iso g).injective equal
    exact ⟨hi, same ▸ entry⟩
  · rintro ⟨hi, entry⟩
    exact ⟨hi, s.nonbottom.encode_mem (a.nonbottom.iso g x), s.encode x.val,
      s.nonbottom.encode_mem x, entry,
      (s.nonbottom.pair_mem_graph s.nonbottom (a.nonbottom.iso g) x _).2 rfl⟩

theorem rowPositionSequenceAction_function (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu delta f : ZFSet.{u}} (subset : delta ⊆ mu)
    (function : ZFSet.IsFunc delta s.nonbottom.carrier f) :
    ZFSet.IsFunc delta s.nonbottom.carrier (rowPositionSequenceAction a s g mu f) := by
  constructor
  · intro z hz
    obtain ⟨i, _, y, _, x, hx, rfl, entry, _⟩ := (mem_relationCompose _ _ _ _ _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨(ZFSet.pair_mem_prod.1 (function.1 entry)).1, hx⟩
  · intro i hi
    obtain ⟨x, entry, unique⟩ := function.2 i hi
    obtain ⟨x, rfl⟩ := (s.nonbottom.mem_carrier x).1
      (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    refine ⟨s.encode (a.iso g x.val),
      (pair_mem_rowPositionSequenceAction a s g mu f i x).2 ⟨subset hi, entry⟩, ?_⟩
    intro y hy
    have hyI := ((pair_mem_relationCompose _ _ _ _ _ i y).1 hy).2.1
    obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hyI
    let old := (a.nonbottom.iso g).symm y
    have target : a.nonbottom.iso g old = y := (a.nonbottom.iso g).apply_symm_apply y
    have original : ZFSet.pair i (s.encode old.val) ∈ f := by
      apply ((pair_mem_rowPositionSequenceAction a s g mu f i old).1 ?_).2
      simpa only [← PosetAction.nonbottom_iso_val, target, Presentation.nonbottom_encode] using hy
    have same : old = x := s.nonbottom.injective (unique _ original)
    exact congrArg s.nonbottom.encode ((congrArg (a.nonbottom.iso g) same).symm.trans target).symm

theorem rowPositionSequenceAction_code (a : PosetAction G L) (s : Presentation L)
    (g : G) {mu f : ZFSet.{u}} (ordinal : ordinalSetProperty mu)
    (code : RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu f) :
    RowPositionSequenceCode s.carrier s.conditionOrder s.nonbottom.carrier mu
      (rowPositionSequenceAction a s g mu f) := by
  obtain ⟨delta, length, function, d, hd, bounds⟩ := code
  have subset := (rowPositionSequence_length ordinal length).2
  obtain ⟨D, rfl⟩ := (s.mem_carrier d).1 hd
  have movedFunction := rowPositionSequenceAction_function a s g subset function
  refine ⟨delta, length, movedFunction, s.encode (a.iso g D), s.encode_mem _, ?_⟩
  intro i x entry
  obtain ⟨_, _, y, hy, original, moved⟩ := (pair_mem_relationCompose _ _ _ _ _ i x).1 entry
  obtain ⟨y, rfl⟩ := (s.nonbottom.mem_carrier y).1 hy
  obtain ⟨v, hv⟩ := (s.nonbottom.mem_graph s.nonbottom (a.nonbottom.iso g) _).1 moved
  obtain ⟨same, value⟩ := ZFSet.pair_inj.1 hv
  have equal : v = y := s.nonbottom.injective same
  have lower := (s.pair_mem_conditionOrder y.val D).1 (bounds i _ original)
  have result := (s.pair_mem_conditionOrder (a.iso g y.val) (a.iso g D)).2 ((a.iso g).monotone lower)
  rw [equal] at value
  exact value ▸ result

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem rowPositionSequenceAction_mem (a : PosetAction G L) (s : Presentation L) (b : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) {mu f : ZFSet.{u}}
    (hmu : mu ∈ M.sets) (ordinal : ordinalSetProperty mu) (g : G)
    (member : f ∈ M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu) :
    rowPositionSequenceAction a s g mu f ∈
      M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu := by
  obtain ⟨hf, code⟩ := (M.mem_rowPositionSequences ordinal).1 member
  have hI := M.nonbottom_carrier_mem s separation hL
  have ha := M.nonbottom_actionGraph_mem a s b separation hL hG graph
  have actionSection := M.actionGraph_section_mem a.nonbottom s.nonbottom b pairing unions powers
    separation hI ha g (M.transitive hG (b.encode_mem g))
  exact (M.mem_rowPositionSequences ordinal).2
    ⟨M.relationCompose_mem pairing unions powers separation hmu hI hI hf actionSection,
      rowPositionSequenceAction_code a s g ordinal code⟩

end TransitiveGround

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u})

theorem decoded_conditionMapFamily_mem {G P m i e R A : ZFSet.{u}}
    (group : GroupCode G m i e) (order : PartialOrderCode P R)
    (action : PosetActionCode G P m e R A)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    letI := group.toGroup
    letI := order.toPartialOrder
    (action.toPosetAction group order).conditionMapFamily
      (SetMembers.presentation P) (SetMembers.presentation G) ∈ M.sets := by
  let := group.toGroup
  let := order.toPartialOrder
  apply M.conditionMapFamily_mem_of_actionGraph (action.toPosetAction group order)
    (SetMembers.presentation P) (SetMembers.presentation G) pairing unions powers separation collection hP hG
  rw [action.actionGraph_eq group order]
  exact hA

variable {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem exists_ZF_interpretation_from_actionGraph (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (graph : a.actionGraph s t ∈ M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      M.sets ⊆ (a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization ((a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) :=
  M.exists_ZF_interpretation a s t b F K basis small pairing unions powers separation collection infinite
    carrier order group indices supports
    (M.conditionMapFamily_mem_of_actionGraph a s t pairing unions powers separation collection carrier group graph) p

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G R P : Type u}
variable [Group G] [PartialOrder R]
variable (c : Presentation R) (s : Presentation P)
variable (I T levels alpha : ZFSet.{u}) (tests : ZFSet.{u} → P → Prop)
variable (rowAction : PosetAction G R) (t : Presentation G) (assignmentGraph : G → ZFSet.{u})
local notation "Q" => M.flatSuccessorCarrier c s I T levels alpha tests
local notation "J" => stageOneAssignments I T
local notation "B" => M.groundSmallSubsets J ZFSet.omega
local notation "assignmentFamily" => familyCodeGraph t.encode assignmentGraph

noncomputable def flatSuccessorFullActionGraph : ZFSet.{u} :=
  rowAssignmentActionGraph t.carrier Q c.carrier B J
    (rowAction.conditionMapFamily c t) assignmentFamily

theorem flatSuccessorFullActionGraph_entry (g : G) (p q : R) (A D : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (t.encode g) (ZFSet.pair (c.encode p) A)) (ZFSet.pair (c.encode q) D) ∈
      M.flatSuccessorFullActionGraph c s I T levels alpha tests rowAction t assignmentGraph ↔
      ZFSet.pair (c.encode p) A ∈ Q ∧ ZFSet.pair (c.encode q) D ∈ Q ∧ rowAction.iso g p = q ∧
        D = relationImage A J (assignmentGraph g) := by
  rw [flatSuccessorFullActionGraph, pair_mem_rowAssignmentActionGraph]
  constructor
  · rintro ⟨_,source,target,_,_,_,_,rf,af,indexed,row,indexedA,image⟩
    have rowEq := (rowAction.pair_mem_conditionMapFamily c t g rf).1 indexed
    have assignmentEq := (pair_mem_familyCodeGraph t.encode assignmentGraph t.injective g af).1 indexedA
    rw [assignmentEq] at image
    exact ⟨source,target,(c.pair_mem_graph c (rowAction.iso g) p q).1 (rowEq ▸ row),image⟩
  · rintro ⟨source,target,moved,image⟩
    have sourceBound := ZFSet.pair_mem_prod.1
      (M.flatSuccessorCarrier_subset c s I T levels alpha tests source)
    have targetBound := ZFSet.pair_mem_prod.1
      (M.flatSuccessorCarrier_subset c s I T levels alpha tests target)
    exact ⟨t.encode_mem g,source,target,sourceBound.1,sourceBound.2,targetBound.1,targetBound.2,
      _,_,(rowAction.pair_mem_conditionMapFamily c t g _).2 rfl,
      (c.pair_mem_graph c (rowAction.iso g) p q).2 moved,
      (pair_mem_familyCodeGraph t.encode assignmentGraph t.injective g _).2 rfl,image⟩

theorem flatSuccessorFullActionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (rows : c.carrier ∈ M.sets) (conditions : M.flatSuccessorCarrier c s I T levels alpha tests ∈ M.sets)
    (assignments : stageOneAssignments I T ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (group : t.carrier ∈ M.sets) (rowMaps : rowAction.conditionMapFamily c t ∈ M.sets)
    (assignmentMaps : familyCodeGraph t.encode assignmentGraph ∈ M.sets) :
    M.flatSuccessorFullActionGraph c s I T levels alpha tests rowAction t assignmentGraph ∈ M.sets :=
  M.rowAssignmentActionGraph_mem pairing unions powers separation group conditions rows
    (M.groundSmallSubsets_mem powers separation assignments omega) assignments rowMaps assignmentMaps

end PartitionPilot.Forcing.TransitiveGround

end OAI
