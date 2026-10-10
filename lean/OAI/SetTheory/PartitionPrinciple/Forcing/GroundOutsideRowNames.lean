import OAI.SetTheory.PartitionPrinciple.Definability.GroundBinaryRowSets
import OAI.SetTheory.PartitionPrinciple.Definability.SmallFunctionActionFormulas

namespace OAI


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

theorem smallFunctionActionGraph_mem :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    (M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).actionGraph
      (SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)) b ∈ M.sets := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  let act := M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph
  let c := SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)
  have carrier := M.smallPartialFunctions_mem pairing unions powers separation hX hY hN
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hG carrier) carrier
  let params := extend b.carrier (extend c.carrier (extend s.carrier (extend t.carrier
    (extend (a.actionGraph s b) Fin.elim0))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hG (Fin.cases carrier (Fin.cases hX (Fin.cases hY (Fin.cases graph (fun i => Fin.elim0 i)))))
  have correct (z : ZFSet.{u}) :
      BoundedFormula.Truth (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5) (extend z params) ↔
        z ∈ act.actionGraph c b := by
    rw [BoundedFormula.truth_smallActionEntryFormula]
    change (∃ g ∈ b.carrier, ∃ p ∈ c.carrier, ∃ q ∈ c.carrier,
      z = ZFSet.pair (ZFSet.pair g p) q ∧
        RenameActionRelation s.carrier t.carrier (a.actionGraph s b) g p q) ↔ _
    constructor
    · rintro ⟨g, hg, p, hp, q, hq, eq, relation⟩
      obtain ⟨g', rfl⟩ := (b.mem_carrier g).1 hg
      obtain ⟨p', rfl⟩ := (c.mem_carrier p).1 hp
      obtain ⟨q', rfl⟩ := (c.mem_carrier q).1 hq
      rw [eq]
      apply (act.triple_mem_actionGraph c b g' p' q').2
      apply SetMembers.raw_injective
      rw [M.raw_smallFunctionAction]
      exact (renameActionRelation_iff a s t b g'
        (M.smallFunction_raw_properties s.carrier t.carrier N q').2.1.shape).1 relation
    · intro hz
      obtain ⟨⟨g, p⟩, eq⟩ := ((b.product c).mem_graph c (fun x => act.iso x.1 x.2) z).1 hz
      refine ⟨b.encode g, b.encode_mem g, c.encode p, c.encode_mem p,
        c.encode (act.iso g p), c.encode_mem (act.iso g p), eq.symm, ?_⟩
      apply (renameActionRelation_iff a s t b g
        (M.smallFunction_raw_properties s.carrier t.carrier N (act.iso g p)).2.1.shape).2
      exact (M.raw_smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph g p).symm
  have selected := M.bounded_separation_mem separation (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5)
    params members bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.smallActionEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod (ZFSet.prod b.carrier c.carrier) c.carrier) = act.actionGraph c b := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun h => (correct z).1 h.2,
      fun hz => ⟨((b.product c).graph_isFunc c (fun x => act.iso x.1 x.2)).1 hz, (correct z).2 hz⟩⟩
  exact eq ▸ selected

theorem smallFunction_conditionMapFamily_mem (collection : CollectionSchema M.sets) :
    letI := M.smallFunctionOrder s.carrier t.carrier N
    (M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph).conditionMapFamily
      (SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)) b ∈ M.sets := by
  let := M.smallFunctionOrder s.carrier t.carrier N
  exact M.conditionMapFamily_mem_of_actionGraph
    (M.smallFunctionAction a s t b pairing unions powers separation hX hY hG hN graph)
    (SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier N)) b
    pairing unions powers separation collection
    (M.smallPartialFunctions_mem pairing unions powers separation hX hY hN) hG
    (M.smallFunctionActionGraph_mem a s t b pairing unions powers separation hX hY hG hN graph)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

noncomputable def rowUsedRows (I C Y p : ZFSet.{u}) : ZFSet.{u} :=
  relationImage (rowCoordinateDomain I C Y p) I (productFirst I C)

theorem mem_rowUsedRows (I C Y p i : ZFSet.{u}) :
    i ∈ rowUsedRows I C Y p ↔
      i ∈ I ∧ ∃ c ∈ C, ∃ y ∈ Y, ZFSet.pair (ZFSet.pair i c) y ∈ p := by
  rw [rowUsedRows, mem_relationImage]
  constructor
  · rintro ⟨hi, x, hx, rel⟩
    obtain ⟨j, _, c, hc, eq⟩ := (mem_productFirst I C _).1 rel
    have entries := ZFSet.pair_inj.1 eq
    obtain ⟨_, y, hy, entry⟩ := (mem_rowCoordinateDomain I C Y p x).1 hx
    rw [entries.1, ← entries.2] at entry
    exact ⟨hi, c, hc, y, hy, entry⟩
  · rintro ⟨hi, c, hc, y, hy, entry⟩
    exact ⟨hi, ZFSet.pair i c,
      (mem_rowCoordinateDomain I C Y p _).2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hc⟩, y, hy, entry⟩,
      (mem_productFirst I C _).2 ⟨i, hi, c, hc, rfl⟩⟩

theorem rowUsedRows_subset (I C Y p : ZFSet.{u}) : rowUsedRows I C Y p ⊆ I :=
  fun i hi => ((mem_rowUsedRows I C Y p i).1 hi).1

theorem row_mem_rowUsedRows {I C Y p i c y : ZFSet.{u}}
    (code : PartialFunctionCode (ZFSet.prod I C) Y p)
    (entry : ZFSet.pair (ZFSet.pair i c) y ∈ p) : i ∈ rowUsedRows I C Y p := by
  have bound := ZFSet.pair_mem_prod.1 (code.shape entry)
  have coordinates := ZFSet.pair_mem_prod.1 bound.1
  exact (mem_rowUsedRows I C Y p i).2 ⟨coordinates.1, c, coordinates.2, y, bound.2, entry⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowUsedRows_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) : rowUsedRows I C Y p ∈ M.sets :=
  M.relationImage_mem separation
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI
    (M.productFirst_mem pairing unions powers separation hI hC)

theorem rowUsedRows_groundEmbeddable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p N : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hY : Y ∈ M.sets) (hp : p ∈ M.sets) (hN : N ∈ M.sets)
    (small : M.groundEmbeddable p N) : M.groundEmbeddable (rowUsedRows I C Y p) N :=
  M.groundEmbeddable_function_image pairing unions powers separation choice
    (M.rowCoordinateDomain_mem pairing unions powers separation hI hC hY hp) hI hN
    (M.productFirst_mem pairing unions powers separation hI hC) (productFirst_function I C)
    (M.rowCoordinateDomain_groundEmbeddable pairing unions powers separation choice hI hC hY hp hN small)

theorem countablePartialFunctions_rowSupport
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C Y p : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hY : Y ∈ M.sets)
    (hp : p ∈ M.smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega) :
    rowUsedRows I C Y p ∈ M.sets ∧ M.groundEmbeddable (rowUsedRows I C Y p) ZFSet.omega := by
  obtain ⟨ground, _, small⟩ := (M.mem_smallPartialFunctions (ZFSet.prod I C) Y ZFSet.omega p).1 hp
  exact ⟨M.rowUsedRows_mem pairing unions powers separation hI hC hY ground,
    M.rowUsedRows_groundEmbeddable pairing unions powers separation choice
      hI hC hY ground (M.omega_mem separation infinite) small⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

open SetRealization
universe u

@[instance_reducible]
def columnOrder (C : ZFSet.{u}) : PartialOrder (SetMembers C) where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

noncomputable def rowCoordinatePresentation {L : Type u} [Bot L]
    (s : Presentation L) (C : ZFSet.{u}) :
    Presentation ({i : L // i ≠ ⊥} × SetMembers C) :=
  s.nonbottom.product (SetMembers.presentation C)

namespace PosetAction

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]

noncomputable def rowCoordinates (a : PosetAction G L) (C : ZFSet.{u}) :
    letI := columnOrder C
    PosetAction G ({i : L // i ≠ ⊥} × SetMembers C) := by
  letI := columnOrder C
  exact a.nonbottom.productColumns (SetMembers C)

theorem rowCoordinates_apply (a : PosetAction G L) (C : ZFSet.{u}) :
    letI := columnOrder C
    ∀ (g : G) (i : {i : L // i ≠ ⊥}) (c : SetMembers C),
      (a.rowCoordinates C).iso g (i, c) = (a.nonbottom.iso g i, c) := by
  let := columnOrder C
  intro g i c
  rfl

end PosetAction

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem rowCoordinate_carrier_mem {L : Type u} [Bot L]
    (s : Presentation L) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) :
    (rowCoordinatePresentation s C).carrier ∈ M.sets :=
  M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC

theorem rowCoordinate_graph_mem {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
    (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
    (graph : a.actionGraph s b ∈ M.sets) :
    letI := columnOrder C
    (a.rowCoordinates C).actionGraph (rowCoordinatePresentation s C) b ∈ M.sets := by
  let := columnOrder C
  exact M.productColumns_actionGraph_mem a.nonbottom s.nonbottom (SetMembers.presentation C) b
    pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC hG
    (M.nonbottom_actionGraph_mem a s b separation hL hG graph)

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

noncomputable def internalRowAction :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    PosetAction G (SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := columnOrder C
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  exact M.smallFunctionAction (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)

theorem internalRowAction_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers
      (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c : SetMembers C) (k : Fin 2),
      ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) (SetMembers.raw c)) (natSetCode k.val) ∈
        SetMembers.raw p := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c k
  exact M.smallFunctionAction_entry (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)
    g p (i, c) (ULift.up k)

theorem internalRowActionGraph_mem :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    (M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph).actionGraph
      (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) b ∈
          M.sets := by
  let := columnOrder C
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  exact M.smallFunctionActionGraph_mem (a.rowCoordinates C) (rowCoordinatePresentation s C)
    (natInitialPresentation 2) b pairing unions powers separation
    (M.rowCoordinate_carrier_mem s C pairing unions powers separation hL hC)
    (M.natSetCode_mem separation infinite 2) hG (M.omega_mem separation infinite)
    (M.rowCoordinate_graph_mem a s b C pairing unions powers separation hL hC hG graph)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem internalRowCondition_entry_shape {L : Type u} [Bot L]
    (s : Presentation L) (C : ZFSet.{u})
    (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
    (z : ZFSet.{u}) (hz : z ∈ SetMembers.raw p) :
    ∃ i : {i : L // i ≠ ⊥}, ∃ c ∈ C, ∃ y ∈ natSetCode 2,
      z = ZFSet.pair (ZFSet.pair (s.encode i.val) c) y := by
  have shape := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega p).2.1.shape hz
  obtain ⟨ic, hic, y, hy, eq⟩ := ZFSet.mem_prod.1 shape
  obtain ⟨r, hr, c, hc, rfl⟩ := ZFSet.mem_prod.1 hic
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier r).1 hr
  exact ⟨i, c, hc, y, hy, eq⟩

variable {G L : Type u} [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowAction_raw_entry :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}) (c y : ZFSet.{u}), c ∈ C → y ∈ natSetCode 2 →
      (ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) c) y ∈
        SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p) ↔
      ZFSet.pair (ZFSet.pair (s.encode i.val) c) y ∈ SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i c y hc hy
  obtain ⟨k, eq⟩ := ((natInitialPresentation 2).mem_carrier y).1 hy
  change natSetCode k.down.val = y at eq
  have entry := M.internalRowAction_entry a s b C pairing unions powers separation infinite
    hL hC hG graph g p i (SetMembers.ofMem c hc) k.down
  simpa only [SetMembers.raw_ofMem, eq] using entry

theorem internalRowAction_usedRows :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))
      (i : {i : L // i ≠ ⊥}),
      s.encode (a.iso g i.val) ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
        (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
          hL hC hG graph).iso g p)) ↔
      s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p i
  rw [mem_rowUsedRows, mem_rowUsedRows]
  constructor
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem i, c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).1 entry⟩
  · rintro ⟨_, c, hc, y, hy, entry⟩
    exact ⟨s.nonbottom.encode_mem (a.nonbottom.iso g i), c, hc, y, hy,
      (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
        hL hC hG graph g p i c y hc hy).2 entry⟩

theorem internalRowAction_eq_of_fixes_usedRows :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      (∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) →
        a.iso g i.val = i.val) →
      (M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph).iso g p = p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p fixed
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  change act.iso g p = p
  apply SetMembers.raw_injective
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, c, hc, y, hy, eq⟩ := M.internalRowCondition_entry_shape s C (act.iso g p) z hz
    let j := (a.nonbottom.iso g).symm i
    have image : a.iso g j.val = i.val :=
      congrArg Subtype.val ((a.nonbottom.iso g).apply_symm_apply i)
    have moved : ZFSet.pair (ZFSet.pair (s.encode (a.iso g j.val)) c) y ∈
        SetMembers.raw (act.iso g p) := by
      rw [image, ← eq]
      exact hz
    have old := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p j c y hc hy).1 moved
    have used := row_mem_rowUsedRows (M.smallFunction_raw_properties
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega p).2.1 old
    have rowEq : j.val = i.val := (fixed j used).symm.trans image
    rw [rowEq] at old
    exact eq.symm ▸ old
  · intro hz
    obtain ⟨i, c, hc, y, hy, eq⟩ := M.internalRowCondition_entry_shape s C p z hz
    have old : ZFSet.pair (ZFSet.pair (s.encode i.val) c) y ∈ SetMembers.raw p := by
      rw [← eq]
      exact hz
    have used := row_mem_rowUsedRows (M.smallFunction_raw_properties
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega p).2.1 old
    have moved := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i c y hc hy).2 old
    rw [fixed i used] at moved
    exact eq.symm ▸ moved

theorem internalRowAction_eq_of_principalFix :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (D : L),
      (∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      g ∈ a.principalFix D →
      (M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph).iso g p = p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p D bound fixed
  exact M.internalRowAction_eq_of_fixes_usedRows a s b C pairing unions powers separation infinite
    hL hC hG graph g p (fun i used => fixed i.val (bound i used))

theorem internalRowAction_usedRows_bounded :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (g : G) (p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) (D : L),
      (∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      ∀ i : {i : L // i ≠ ⊥},
        s.encode i.val ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2)
          (SetMembers.raw ((M.internalRowAction a s b C pairing unions powers separation infinite
            hL hC hG graph).iso g p)) → i.val ≤ a.iso g D := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro g p D bound i used
  let j := (a.nonbottom.iso g).symm i
  have image : a.iso g j.val = i.val :=
    congrArg Subtype.val ((a.nonbottom.iso g).apply_symm_apply i)
  have old := (M.internalRowAction_usedRows a s b C pairing unions powers separation infinite
    hL hC hG graph g p j).1 (by rw [image]; exact used)
  have mapped := (a.iso g).monotone (bound j old)
  rw [image] at mapped
  exact mapped

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (i : {i : L // i ≠ ⊥}) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowName_action (g : G) (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowName s C hL i) =
      M.internalRowName s C hL (a.nonbottom.iso g i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) =
    M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode (a.iso g i.val))
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val))) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, hp⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
      (s.encode i.val) ν p).1 entry
    refine ⟨x, hx, (act.act_check c g x).symm.trans eq, ?_⟩
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    exact moved.2 hp
  · rintro ⟨x, hx, rfl, hq⟩
    let p := (act.iso g).symm q
    have pq : act.iso g p = q := (act.iso g).apply_symm_apply q
    have moved := M.internalRowAction_entry a s b C pairing unions powers separation infinite
      hL hC hG graph g p i (SetMembers.ofMem x hx) (1 : Fin 2)
    simp only [SetMembers.raw_ofMem] at moved
    have hp : ZFSet.pair (ZFSet.pair (s.encode i.val) x) (natSetCode 1) ∈
        SetMembers.raw p := by
      apply moved.1
      change ZFSet.pair (ZFSet.pair (s.encode (a.iso g i.val)) x) (natSetCode 1) ∈
        SetMembers.raw (act.iso g p)
      rw [pq]
      exact hq
    exact ⟨Name.check c ⊤ x, p,
      (M.entry_binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val) _ p).2
        ⟨x, hx, rfl, hp⟩, act.act_check c g x, pq⟩

theorem internalRowName_supported (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    a.principalFix i.val ≤ act.stabilizer c (M.internalRowName s C hL i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act c g fixed
  change act.act c g (M.internalRowName s C hL i) = M.internalRowName s C hL i
  rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
  apply congrArg (M.internalRowName s C hL)
  exact Subtype.ext (fixed i.val le_rfl)

theorem internalRowName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k)
    (i : {i : L // i ≠ ⊥}) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalRowName s C hL i) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  refine HereditarilySymmetric.mk ⟨i.val,
    M.internalRowName_supported a s b C pairing unions powers separation infinite hL hC hG graph i⟩ ?_
  intro σ p entry
  obtain ⟨x, _, rfl, _⟩ := (M.entry_binaryRowName s.nonbottom.carrier C ⊤
    (s.encode i.val) σ p).1 entry
  exact HereditarilySymmetric.check act c (a.principalSupportFamily ⊥ directed) x

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalRowSetName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSetName s.nonbottom.carrier C ⊤

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalRowSetName_action (g : G) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalRowSetName s C hL) = M.internalRowSetName s C hL := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  change act.act c g (M.binaryRowSetName s.nonbottom.carrier C ⊤) =
    M.binaryRowSetName s.nonbottom.carrier C ⊤
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g)
    (M.binaryRowSetName s.nonbottom.carrier C ⊤)) q ↔ _
  rw [Name.entry_rename, M.entry_binaryRowSetName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨x, hx, rfl, rfl⟩ := (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ ν p).1 entry
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    refine ⟨s.nonbottom.encode (a.nonbottom.iso g i), s.nonbottom.encode_mem _, ?_,
      (act.iso g).map_top.symm⟩
    have moved := M.internalRowName_action a s b C pairing unions powers separation infinite
      hL hC hG graph g i
    exact moved.symm.trans eq
  · rintro ⟨x, hx, rfl, rfl⟩
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    let j := (a.nonbottom.iso g).symm i
    refine ⟨M.internalRowName s C hL j, ⊤,
      (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ _ ⊤).2
        ⟨s.nonbottom.encode j, s.nonbottom.encode_mem j, rfl, rfl⟩, ?_,
      (act.iso g).map_top⟩
    change act.act c g (M.internalRowName s C hL j) = M.internalRowName s C hL i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    exact congrArg (M.internalRowName s C hL) ((a.nonbottom.iso g).apply_symm_apply i)

theorem internalRowSetName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalRowSetName s C hL) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  refine HereditarilySymmetric.mk ⟨⊥, ?_⟩ ?_
  · intro g _
    exact M.internalRowSetName_action a s b C pairing unions powers separation infinite hL hC hG graph g
  · intro σ p entry
    obtain ⟨x, hx, rfl, _⟩ := (M.entry_binaryRowSetName s.nonbottom.carrier C ⊤ σ p).1 entry
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 hx
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def outsideRowIndices {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) : ZFSet.{u} :=
  ZFSet.sep (fun x => ZFSet.pair x (s.encode B) ∉ s.conditionOrder) s.nonbottom.carrier

theorem outsideRowIndices_subset {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) : outsideRowIndices s B ⊆ s.nonbottom.carrier :=
  fun _ hx => (ZFSet.mem_sep.1 hx).1

theorem encode_mem_outsideRowIndices {L : Type u} [PartialOrder L] [OrderBot L]
    (s : Presentation L) (B : L) (i : {i : L // i ≠ ⊥}) :
    s.encode i.val ∈ outsideRowIndices s B ↔ ¬ i.val ≤ B := by
  rw [outsideRowIndices, ZFSet.mem_sep, s.pair_mem_conditionOrder]
  exact ⟨And.right, fun hi => ⟨s.nonbottom.encode_mem i, hi⟩⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def binaryRowSubsetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u}) :
    Name (SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :=
  Name.assemble (fun i : SetMembers J => M.binaryRowName I C one (SetMembers.raw i)) (fun _ => one)

theorem entry_binaryRowSubsetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u})
    (σ : Name (SetMembers.presentation
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)))
    (p : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    Name.Entry σ (M.binaryRowSubsetName I C one J) p ↔
      ∃ i ∈ J, M.binaryRowName I C one i = σ ∧ one = p := by
  rw [binaryRowSubsetName, Name.entry_assemble]
  constructor
  · rintro ⟨i, eq, condition⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq, condition⟩
  · rintro ⟨i, hi, eq, condition⟩
    exact ⟨SetMembers.ofMem i hi, by simpa only [SetMembers.raw_ofMem] using eq, condition⟩

theorem mem_binaryRowSubsetName_code (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J z : ZFSet.{u}) :
    z ∈ (M.binaryRowSubsetName I C one J).val ↔ ∃ i ∈ J,
      z = ZFSet.pair (M.binaryRowName I C one i).val (SetMembers.raw one) := by
  change z ∈ ZFSet.range _ ↔ _
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, eq⟩
    exact ⟨SetMembers.raw i, SetMembers.raw_mem i, eq.symm⟩
  · rintro ⟨i, hi, eq⟩
    refine ⟨SetMembers.ofMem i hi, ?_⟩
    simpa only [SetMembers.presentation, SetMembers.raw_ofMem] using eq.symm

theorem eval_binaryRowSubsetName (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)), H.mem one →
      Name.eval {p | H.mem p} (M.binaryRowSubsetName I C one J) =
        ZFSet.range (fun i : SetMembers J => M.binaryGenericRow I C H (SetMembers.raw i)) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H hone
  apply ZFSet.ext
  intro x
  rw [binaryRowSubsetName, Name.mem_eval_assemble, ZFSet.mem_range]
  constructor
  · rintro ⟨i, _, eq⟩
    rw [M.eval_binaryRowName I C one H hone] at eq
    exact ⟨i, eq⟩
  · rintro ⟨i, eq⟩
    exact ⟨i, hone, (M.eval_binaryRowName I C one H hone (SetMembers.raw i)).trans eq⟩

theorem eval_binaryRowSubsetName_subset (I C : ZFSet.{u})
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))
    (J : ZFSet.{u}) (subset : J ⊆ I)
    (H : Set (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) :
    Name.eval H (M.binaryRowSubsetName I C one J) ⊆ Name.eval H (M.binaryRowSetName I C one) := by
  intro x hx
  obtain ⟨σ, p, entry, hp, eq⟩ := (Name.mem_eval H _ x).1 hx
  obtain ⟨i, hi, child, condition⟩ := (M.entry_binaryRowSubsetName I C one J σ p).1 entry
  exact (Name.mem_eval H _ x).2 ⟨σ, p,
    (M.entry_binaryRowSetName I C one σ p).2 ⟨i, subset hi, child, condition⟩, hp, eq⟩

variable {L G : Type u} [Group G] [PartialOrder L] [OrderBot L]

noncomputable def internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)) := by
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  exact M.binaryRowSubsetName s.nonbottom.carrier C ⊤ (outsideRowIndices s B)

theorem entry_internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    ∀ (σ : Name (SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)))
      (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.Entry σ (M.internalOutsideRowsName s C hL B) p ↔
        ∃ i : {i : L // i ≠ ⊥}, ¬ i.val ≤ B ∧ M.internalRowName s C hL i = σ ∧ ⊤ = p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro σ p
  rw [internalOutsideRowsName, M.entry_binaryRowSubsetName]
  constructor
  · rintro ⟨x, hx, child, condition⟩
    obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier x).1 (outsideRowIndices_subset s B hx)
    exact ⟨i, (encode_mem_outsideRowIndices s B i).1 hx, child, condition⟩
  · rintro ⟨i, hi, child, condition⟩
    exact ⟨s.encode i.val, (encode_mem_outsideRowIndices s B i).2 hi, child, condition⟩

theorem mem_eval_internalOutsideRowsName (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega))) (x : ZFSet.{u}),
      x ∈ Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B) ↔
        ∃ i : {i : L // i ≠ ⊥}, ¬ i.val ≤ B ∧
          M.binaryGenericRow s.nonbottom.carrier C H (s.encode i.val) = x := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H x
  rw [Name.mem_eval]
  constructor
  · rintro ⟨σ, p, entry, _, eq⟩
    obtain ⟨i, hi, rfl, _⟩ := (M.entry_internalOutsideRowsName s C hL B σ p).1 entry
    change Name.eval {p | H.mem p} (M.binaryRowName s.nonbottom.carrier C ⊤ (s.encode i.val)) = x at eq
    rw [M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem] at eq
    exact ⟨i, hi, eq⟩
  · rintro ⟨i, hi, eq⟩
    exact ⟨M.internalRowName s C hL i, ⊤,
      (M.entry_internalOutsideRowsName s C hL B _ ⊤).2 ⟨i, hi, rfl, rfl⟩, H.top_mem,
      (M.eval_binaryRowName s.nonbottom.carrier C ⊤ H H.top_mem (s.encode i.val)).trans eq⟩

theorem eval_internalOutsideRowsName_subset (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B) ⊆
        Name.eval {p | H.mem p} (M.internalRowSetName s C hL) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro H
  exact M.eval_binaryRowSubsetName_subset s.nonbottom.carrier C ⊤ (outsideRowIndices s B)
    (outsideRowIndices_subset s B) {p | H.mem p}

theorem eval_internalOutsideRowsName_nonempty (s : Presentation L) (C : ZFSet.{u})
    (hL : s.carrier ∈ M.sets) (B : L) (outside : ∃ i : L, ¬ i ≤ B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)),
      (Name.eval {p | H.mem p} (M.internalOutsideRowsName s C hL B)).Nonempty := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro H
  obtain ⟨i, hi⟩ := outside
  have nonbottom : i ≠ ⊥ := by
    intro eq
    exact hi (eq ▸ bot_le)
  exact ⟨M.binaryGenericRow s.nonbottom.carrier C H (s.encode i),
    (M.mem_eval_internalOutsideRowsName s C hL B H _).2 ⟨⟨i, nonbottom⟩, hi, rfl⟩⟩

variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem internalOutsideRowsName_action (B : L) (g : G) (fixed : g ∈ a.principalFix B) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    act.act c g (M.internalOutsideRowsName s C hL B) = M.internalOutsideRowsName s C hL B := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
  have preserves (i : {i : L // i ≠ ⊥}) :
      ¬ (a.nonbottom.iso g i).val ≤ B ↔ ¬ i.val ≤ B := by
    apply not_congr
    change a.iso g i.val ≤ B ↔ i.val ≤ B
    calc
      a.iso g i.val ≤ B ↔ a.iso g i.val ≤ a.iso g B := by rw [fixed B le_rfl]
      _ ↔ i.val ≤ B := (a.iso g).map_rel_iff
  apply Name.ext
  intro σ q
  change Name.Entry σ (Name.rename c (act.iso g) (M.internalOutsideRowsName s C hL B)) q ↔ _
  rw [Name.entry_rename, M.entry_internalOutsideRowsName]
  constructor
  · rintro ⟨ν, p, entry, eq, rfl⟩
    obtain ⟨i, hi, rfl, rfl⟩ := (M.entry_internalOutsideRowsName s C hL B ν p).1 entry
    refine ⟨a.nonbottom.iso g i, (preserves i).2 hi, ?_, (act.iso g).map_top.symm⟩
    have moved := M.internalRowName_action a s b C pairing unions powers separation infinite
      hL hC hG graph g i
    exact moved.symm.trans eq
  · rintro ⟨i, hi, rfl, rfl⟩
    let j := (a.nonbottom.iso g).symm i
    have image : a.nonbottom.iso g j = i := (a.nonbottom.iso g).apply_symm_apply i
    have outside : ¬ j.val ≤ B := (preserves j).1 (by rw [image]; exact hi)
    refine ⟨M.internalRowName s C hL j, ⊤,
      (M.entry_internalOutsideRowsName s C hL B _ ⊤).2 ⟨j, outside, rfl, rfl⟩, ?_,
      (act.iso g).map_top⟩
    change act.act c g (M.internalRowName s C hL j) = M.internalRowName s C hL i
    rw [M.internalRowName_action a s b C pairing unions powers separation infinite hL hC hG graph]
    exact congrArg (M.internalRowName s C hL) image

theorem internalOutsideRowsName_hs (directed : ∀ i j : L, ∃ k, i ≤ k ∧ j ≤ k) (B : L) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) (M.internalOutsideRowsName s C hL B) := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  refine HereditarilySymmetric.mk ⟨B, ?_⟩ ?_
  · intro g fixed
    exact M.internalOutsideRowsName_action a s b C pairing unions powers separation infinite
      hL hC hG graph B g fixed
  · intro σ p entry
    obtain ⟨i, _, rfl, _⟩ := (M.entry_internalOutsideRowsName s C hL B σ p).1 entry
    exact M.internalRowName_hs a s b C pairing unions powers separation infinite hL hC hG graph directed i

end TransitiveGround

end PartitionPilot.Forcing

end OAI
