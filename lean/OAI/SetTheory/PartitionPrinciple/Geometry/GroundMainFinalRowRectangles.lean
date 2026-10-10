import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticAlignedCopyUnions
import OAI.SetTheory.PartitionPrinciple.Definability.GroundSemanticStructuralOrderCoordinates
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundBinaryRowStructuralDataBoundActions

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [Group G] [PartialOrder L] [OrderBot L]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

local notation "Q" => SetMembers (M.smallPartialFunctions
  (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)

theorem internalRowAction_aligned_agrees :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V : L) (g h : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g p →
      (∀ i, i ≤ a.iso h D → i ≤ X → i ≤ a.iso h V) →
      (∀ i, i ≤ V → a.iso h i = a.iso g i) →
      ∀ x y z, ZFSet.pair x y ∈ SetMembers.raw r →
        ZFSet.pair x z ∈ SetMembers.raw (act.iso h p) → y = z := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V g h bp br reference overlap agree x y z left right
  have rc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega r).2.1
  have hc := (M.smallFunction_raw_properties (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega (act.iso h p)).2.1
  have coords := (ZFSet.pair_mem_prod.1 (rc.shape left)).1
  have hz := (ZFSet.pair_mem_prod.1 (hc.shape right)).2
  obtain ⟨row, hrow, c, hcol, rfl⟩ := ZFSet.mem_prod.1 coords
  obtain ⟨i, rfl⟩ := (s.nonbottom.mem_carrier row).1 hrow
  have ri := br i (row_mem_rowUsedRows rc left)
  have hi := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h p D bp i (row_mem_rowUsedRows hc right)
  have below := overlap i.val hi ri
  let j := (a.nonbottom.iso h).symm i
  have image : a.iso h j.val = i.val :=
    congrArg Subtype.val ((a.nonbottom.iso h).apply_symm_apply i)
  have oldV : j.val ≤ V := by
    have moved : a.iso h j.val ≤ a.iso h V := by rw [image]; exact below
    simpa only [OrderIso.symm_apply_apply] using (a.iso h).symm.monotone moved
  have same : a.iso g j.val = i.val := (agree j.val oldV).symm.trans image
  have old := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph h p j c z hcol hz).1 (by rw [image]; exact right)
  have copied := (M.internalRowAction_raw_entry a s b C pairing unions powers separation infinite
    hL hC hG graph g p j c z hcol hz).2 old
  rw [same] at copied
  have inherited := (M.smallFunction_le_iff (ZFSet.prod s.nonbottom.carrier C)
    (natSetCode 2) ZFSet.omega r (act.iso g p)).1 reference copied
  exact rc.unique _ y z left inherited

theorem internalRowAction_one_copy_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V : L) (g h : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g p →
      (∀ i, i ≤ a.iso h D → i ≤ X → i ≤ a.iso h V) →
      (∀ i, i ≤ V → a.iso h i = a.iso g i) →
      ∃ t : Q, SetMembers.raw t = SetMembers.raw r ∪ SetMembers.raw (act.iso h p) ∧
        t ≤ r ∧ t ≤ act.iso h p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V g h bp br reference overlap agree
  exact M.countableFunction_common_extension pairing unions powers separation infinite choice
    (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) r (act.iso h p)
    (M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
      hL hC hG graph p r D X V g h bp br reference overlap agree)

theorem internalRowAction_rectangle_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    ∀ (p r : Q) (D X V W : L) (g₁ g₂ h₁ h₂ : G),
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw p) → i.val ≤ D) →
      (∀ i : {i : L // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g₁ p → r ≤ act.iso g₂ p →
      (∀ i, i ≤ V → a.iso h₁ i = a.iso g₁ i) →
      (∀ i, i ≤ V → a.iso h₂ i = a.iso g₂ i) →
      (∀ i, i ≤ W → a.iso h₁ i = a.iso h₂ i) →
      (∀ i, i ≤ a.iso h₁ D → i ≤ X → i ≤ a.iso h₁ V) →
      (∀ i, i ≤ a.iso h₂ D → i ≤ X → i ≤ a.iso h₂ V) →
      (∀ i, i ≤ a.iso h₁ D → i ≤ a.iso h₂ D → i ≤ a.iso h₁ W) →
      ∃ t : Q, SetMembers.raw t =
          (SetMembers.raw r ∪ SetMembers.raw (act.iso h₁ p)) ∪ SetMembers.raw (act.iso h₂ p) ∧
        t ≤ r ∧ t ≤ act.iso h₁ p ∧ t ≤ act.iso h₂ p := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  intro act p r D X V W g₁ g₂ h₁ h₂ bp br ref₁ ref₂ agree₁ agree₂ agreeW overlap₁ overlap₂ overlapW
  have one := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p r D X V g₁ h₁ bp br ref₁ overlap₁ agree₁
  have two := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p r D X V g₂ h₂ bp br ref₂ overlap₂ agree₂
  have movedBound := M.internalRowAction_usedRows_bounded a s b C pairing unions powers separation
    infinite hL hC hG graph h₂ p D bp
  have pair := M.internalRowAction_aligned_agrees a s b C pairing unions powers separation infinite
    hL hC hG graph p (act.iso h₂ p) D (a.iso h₂ D) W h₂ h₁ bp movedBound
      le_rfl overlapW agreeW
  obtain ⟨q, rawq, qr, qh₁⟩ := M.countableFunction_common_extension pairing unions powers separation
    infinite choice (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) r (act.iso h₁ p) one
  have compatible : ∀ x y z, ZFSet.pair x y ∈ SetMembers.raw q →
      ZFSet.pair x z ∈ SetMembers.raw (act.iso h₂ p) → y = z := by
    intro x y z left right
    rw [rawq] at left
    rcases ZFSet.mem_union.1 left with left | left
    · exact two x y z left right
    · exact (pair x z y right left).symm
  obtain ⟨t, rawt, tq, th₂⟩ := M.countableFunction_common_extension pairing unions powers separation
    infinite choice (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) q (act.iso h₂ p) compatible
  refine ⟨t, ?_, le_trans tq qr, le_trans tq qh₁, th₂⟩
  exact rawt.trans (congrArg (fun z => z ∪ SetMembers.raw (act.iso h₂ p)) rawq)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem decoded_rectangle_request :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    ∀ (V W d : SetMembers geometry.carrier) (g h : SetMembers geometry.actors),
      V ≤ d → W ≤ d →
      g ∈ a.principalFix (geometry.meet.smallMeet V W) →
      h ∈ a.principalFix (geometry.meet.smallMeet V W) →
      geometry.meet.smallMeet (a.iso g d) (a.iso h d) = geometry.meet.smallMeet V W →
      ExternalRectangleCode geometry.carrier geometry.actors geometry.order
        geometry.meetGraph geometry.action (SetMembers.raw V) (SetMembers.raw W)
        (SetMembers.raw d) (SetMembers.raw g) (SetMembers.raw h) := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  intro a V W d g h vd wd fixesG fixesH separated
  let meet := geometry.meet.smallMeet V W
  refine ⟨SetMembers.raw_mem V, SetMembers.raw_mem W, SetMembers.raw_mem d,
    SetMembers.raw_mem g, SetMembers.raw_mem h, vd, wd,
    SetMembers.raw meet, SetMembers.raw_mem meet, geometry.meet.smallMeet_entry V W, ?_, ?_⟩
  · intro x hx y hy lower
    let z := SetMembers.ofMem x hx
    let value := SetMembers.ofMem y hy
    have below : z ≤ meet := by
      change ZFSet.pair (SetMembers.raw z) (SetMembers.raw meet) ∈ geometry.order
      simpa only [z, SetMembers.raw_ofMem] using lower
    have agree : a.iso g z = a.iso h z := (fixesG z below).trans (fixesH z below).symm
    change geometry.action_code.act g z = geometry.action_code.act h z at agree
    have iff : ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw z)) (SetMembers.raw value)
        ∈ geometry.action ↔
        ZFSet.pair (ZFSet.pair (SetMembers.raw h) (SetMembers.raw z)) (SetMembers.raw value)
        ∈ geometry.action := by
      rw [← geometry.action_code.act_eq_iff, ← geometry.action_code.act_eq_iff, agree]
    simpa only [z, value, SetMembers.raw_ofMem] using iff
  · intro y hy z hz v hv entries
    have first := (geometry.action_code.act_eq_iff g d (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.1)
    have second := (geometry.action_code.act_eq_iff h d (SetMembers.ofMem z hz)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.2.1)
    have last := (geometry.action_code.act_eq_iff g meet (SetMembers.ofMem v hv)).2
      (by simpa only [SetMembers.raw_ofMem] using entries.2.2)
    have same : geometry.meet.smallMeet (SetMembers.ofMem y hy) (SetMembers.ofMem z hz) =
        SetMembers.ofMem v hv := by
      rw [← first, ← second]
      exact separated.trans ((fixesG meet le_rfl).symm.trans last)
    simpa only [SetMembers.raw_ofMem] using (geometry.meet.smallMeet_eq_iff _ _ _).1 same

end PartitionPilot.Forcing.GroundMainFinalGeometry

namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)
include fulfilled

theorem decoded_separate_at :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    ∀ W d X : SetMembers geometry.carrier, W ≤ d → W ≤ X →
      ∃ h : SetMembers geometry.actors,
        h ∈ geometry.decodedAction.principalFix W ∧
        geometry.meet.smallMeet (geometry.decodedAction.iso h d) X = W := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  dsimp only
  intro W d X wd wx
  obtain ⟨k, hk, fixed, y, hy, action, meet⟩ := fulfilled.separates
    _ (SetMembers.raw_mem W) _ (SetMembers.raw_mem d) _ (SetMembers.raw_mem X) wd wx
  let h := SetMembers.ofMem k hk
  have acted : geometry.action_code.act h d = SetMembers.ofMem y hy :=
    (geometry.action_code.act_eq_iff _ _ _).2
      (by simpa only [h, SetMembers.raw_ofMem] using action)
  refine ⟨h, ?_, ?_⟩
  · intro z lower
    apply (geometry.action_code.act_eq_iff _ _ _).2
    simpa only [h, SetMembers.raw_ofMem] using fixed _ (SetMembers.raw_mem z) lower
  · apply (geometry.meet.smallMeet_eq_iff _ _ _).2
    change ZFSet.pair (ZFSet.pair (SetMembers.raw (geometry.action_code.act h d))
      (SetMembers.raw X)) (SetMembers.raw W) ∈ geometry.meetGraph
    simpa only [acted, SetMembers.raw_ofMem] using meet

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end


namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)
include fulfilled

theorem internalRow_rectangle_union
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    ∀ (p r : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (d X V W : SetMembers geometry.carrier) (g₁ g₂ : SetMembers geometry.actors),
      ExternalRectangleCode geometry.carrier geometry.actors geometry.order
        geometry.meetGraph geometry.action (SetMembers.raw V) (SetMembers.raw W)
        (SetMembers.raw d) (SetMembers.raw g₁) (SetMembers.raw g₂) →
      a.iso g₁ d ≤ X → a.iso g₂ d ≤ X →
      (∀ i : {i : SetMembers geometry.carrier // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → i.val ≤ d) →
      (∀ i : {i : SetMembers geometry.carrier // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw r) → i.val ≤ X) →
      r ≤ act.iso g₁ p → r ≤ act.iso g₂ p →
      ∃ h₁ h₂ : SetMembers geometry.actors,
        RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph geometry.action
          (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
          (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
          (SetMembers.raw h₁) (SetMembers.raw h₂) ∧
        ∃ t : SetMembers (M.smallPartialFunctions
          (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
          SetMembers.raw t = (SetMembers.raw r ∪ SetMembers.raw (act.iso h₁ p)) ∪
            SetMembers.raw (act.iso h₂ p) ∧
          t ≤ r ∧ t ≤ act.iso h₁ p ∧ t ≤ act.iso h₂ p := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  dsimp only
  intro p r d X V W g₁ g₂ request bound₁ bound₂ bp br reference₁ reference₂
  have upper (g : SetMembers geometry.actors) (bound : a.iso g d ≤ X) :
      ∀ y ∈ geometry.carrier,
        ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw d)) y ∈ geometry.action →
        ZFSet.pair y (SetMembers.raw X) ∈ geometry.order := by
    intro y hy entry
    have acted := (geometry.action_code.act_eq_iff g d (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    change ZFSet.pair (SetMembers.raw (geometry.action_code.act g d)) (SetMembers.raw X)
      ∈ geometry.order at bound
    simpa only [acted, SetMembers.raw_ofMem] using bound
  obtain ⟨k, hk, l, hl, rectangle⟩ := fulfilled.rectangles
    _ _ _ _ _ _ request (SetMembers.raw_mem X) (upper g₁ bound₁) (upper g₂ bound₂)
  let h₁ := SetMembers.ofMem k hk
  let h₂ := SetMembers.ofMem l hl
  have code : RectangleAtBoundCode geometry.carrier geometry.order geometry.meetGraph
      geometry.action (SetMembers.raw V) (SetMembers.raw W) (SetMembers.raw d)
      (SetMembers.raw g₁) (SetMembers.raw g₂) (SetMembers.raw X)
      (SetMembers.raw h₁) (SetMembers.raw h₂) := by
    simpa only [h₁, h₂, SetMembers.raw_ofMem] using rectangle
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  have agree₁ := agree h₁ g₁ V code.first_agreement
  have agree₂ := agree h₂ g₂ V code.second_agreement
  have agreeW := agree h₁ h₂ W code.common_agreement
  obtain ⟨v, hv, w, hw, y, hy, z, hz, t, ht,
    gv, hwv, ky, lz, kt, _, meet₁, meet₂, meetW⟩ := code.values
  have value (g : SetMembers geometry.actors) (x : SetMembers geometry.carrier)
      (y : ZFSet.{u}) (hy : y ∈ geometry.carrier)
      (entry : ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw x)) y ∈ geometry.action) :
      SetMembers.raw (a.iso g x) = y := by
    have acted := (geometry.action_code.act_eq_iff g x (SetMembers.ofMem y hy)).2
      (by simpa only [SetMembers.raw_ofMem] using entry)
    exact (congrArg SetMembers.raw acted).trans (SetMembers.raw_ofMem y hy)
  have eqv := value g₁ V v hv gv
  have eqw := value g₂ V w hw hwv
  have eqy := value h₁ d y hy ky
  have eqz := value h₂ d z hz lz
  have eqt := value h₁ W t ht kt
  have overlap₁ : ∀ i, i ≤ a.iso h₁ d → i ≤ X → i ≤ a.iso h₁ V := by
    intro i iy ix
    rw [agree₁ V le_rfl]
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso g₁ V)) ∈ geometry.order
    rw [eqv]
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso h₁ d)) ∈ geometry.order at iy
    rw [eqy] at iy
    exact geometry.meet.greatest y (SetMembers.raw X) v (SetMembers.raw i)
      (SetMembers.raw_mem i) meet₁ iy ix
  have overlap₂ : ∀ i, i ≤ a.iso h₂ d → i ≤ X → i ≤ a.iso h₂ V := by
    intro i iz ix
    rw [agree₂ V le_rfl]
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso g₂ V)) ∈ geometry.order
    rw [eqw]
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso h₂ d)) ∈ geometry.order at iz
    rw [eqz] at iz
    exact geometry.meet.greatest z (SetMembers.raw X) w (SetMembers.raw i)
      (SetMembers.raw_mem i) meet₂ iz ix
  have overlapW : ∀ i, i ≤ a.iso h₁ d → i ≤ a.iso h₂ d → i ≤ a.iso h₁ W := by
    intro i iy iz
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso h₁ W)) ∈ geometry.order
    rw [eqt]
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso h₁ d)) ∈ geometry.order at iy
    change ZFSet.pair (SetMembers.raw i) (SetMembers.raw (a.iso h₂ d)) ∈ geometry.order at iz
    rw [eqy] at iy
    rw [eqz] at iz
    exact geometry.meet.greatest y z t (SetMembers.raw i) (SetMembers.raw_mem i) meetW iy iz
  refine ⟨h₁, h₂, code, ?_⟩
  exact M.internalRowAction_rectangle_union a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground) choice p r d X V W
    g₁ g₂ h₁ h₂ bp br reference₁ reference₂ agree₁ agree₂ agreeW overlap₁ overlap₂ overlapW

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment




namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)
variable (nodeMaps : a.conditionMapFamily s b ∈ M.sets)
variable (supports : supportBasisCode s b a.principalFix ∈ M.sets)
variable (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

include collection order nodeMaps supports

theorem binaryRowStructural_aligned_copy_union
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (meet : L → L → L) {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (muOrdinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
    ∀ valid : ∀ z ∈ T, IsName c z,
    let lifted := Name.renamedFamily c.pairEmpty id T valid
    let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
    let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
    ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
      (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
      (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
      (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
      (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
      (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
        HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
      (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
      (stagesOrdinal : ordinalSetProperty stages)
      (trace : OrdinalRecursionTrace (fun level prior stage => stage =
        M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
          b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
          (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
    let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
    let two := M.natSetCode_mem separation infinite 2
    let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
    let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
    let forcingAction := M.internalRowActionGraph_mem a s b C pairing unions powers separation infinite hL hC hG graph
    let omega := M.omega_mem separation infinite
    let topMem := c.encode_mem ⊤
    let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
      fun r hr => by
        obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
        exact (c.pair_mem_conditionOrder r ⊤).2 le_top
    let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
      (supportBasisCode s b a.principalFix) lifted squared stages history
    let I := refinementDataHistoryIndices stages packed
    let anchors := refinementIndexFieldGraph I s.carrier 2
    let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
    letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
    let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
      pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
      nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
      topMem topRows hs hh stagesOrdinal trace
    ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
      (g h : G) (D X V : L),
      SetMembers.raw p = ZFSet.pair (c.encode r) A →
      SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
      StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
      q ≤ upperAct.iso g p →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw r) → i ≤ D) →
      (∀ i : L, s.encode i ∈ rowUsedRows s.nonbottom.carrier C (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
      (∀ z ∈ A, ZFSet.pair z (s.encode D) ∈
        stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
        stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
      g⁻¹ * h ∈ a.principalFix V →
      meet (a.iso h D) X = a.iso h V →
      meet (a.iso h D) X ≤ a.iso h D →
      meet (a.iso h D) X ≤ X →
      (∀ z : L, z ≤ a.iso h D → z ≤ X → z ≤ meet (a.iso h D) X) →
      (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
        let hAlpha := M.transitive hs member
        let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
        let subset := (And.left stagesOrdinal) alpha member
        let lowerPacked := graphRestriction alpha packed
        let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
        letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
        let lower := SetMembers.presentation Q
        let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
          pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
          nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
          topMem topRows hh trace hAlpha cutOrdinal subset
        ∀ (H : ConditionFilter (SetMembers Q)),
          H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
          ∀ (v w : L) (x y : (M.nameDomain lower).names),
            a.principalFix v ≤ localAct.stabilizer lower x.val →
            a.principalFix w ≤ localAct.stabilizer lower y.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
            Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
            ∃ tau : (M.nameDomain lower).names,
              HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
              a.principalFix (meet v w) ≤ localAct.stabilizer lower tau.val ∧
              Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
      let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A
      ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
        SetMembers.raw row = SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h r) ∧
        SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) ∧
        result ≤ upperAct.iso h p ∧ result ≤ q := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid lifted squared tuples hLifted hSquared valid1 valid2 closed1 closed2
    children1 children2 stages history hs hh stagesOrdinal trace coordinates two carrier forcingOrder
    forcingAction omega topMem topRows packed I anchors upperQ
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  intro upperAct p q r oldRow A oldA g h D X V pCode qCode prepared below usedD usedX dataD dataX
    relative overlap meetLeft meetRight meetGreatest descent movedA
  have source : ZFSet.pair (c.encode r) A ∈ upperQ := pCode ▸ SetMembers.raw_mem p
  have oldSource : ZFSet.pair (c.encode oldRow) oldA ∈ upperQ := qCode ▸ SetMembers.raw_mem q
  have reference := M.semanticStructuralOrder_action_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction
    hG hL order graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2
    children1 children2 topMem topRows hs hh stagesOrdinal trace g p q r oldRow A oldA pCode qCode below
  have agree (i : L) (hi : i ≤ V) : a.iso h i = a.iso g i := by
    have fixed := relative i hi
    have moved := congrArg (a.iso g) fixed
    simpa only [a.mul, a.point_inv_right] using moved
  obtain ⟨row, rowCode, rowBelowOld, rowBelowH⟩ :=
    M.internalRowAction_one_copy_union a s b C pairing unions powers separation infinite hL hC hG graph
      choice r oldRow D X V g h (fun i hi => usedD i.val hi) (fun i hi => usedX i.val hi)
      reference.1 (fun i hi hx => overlap ▸ meetGreatest i hi hx) agree
  have candidate := (M.mem_refinementHistoryForcing c.carrier lifted stages packed
    (ZFSet.pair (c.encode r) A)).1 source |>.1
  have hA : A ∈ M.sets := ((M.mem_groundSmallSubsets _ _ A).1 (ZFSet.pair_mem_prod.1 candidate).2).1
  have transported := M.binaryRowStructuralAssignmentImage_dataBound a s b C pairing unions powers
    separation collection infinite hL order hC hG graph nodeMaps supports directed hmu muOrdinal
    valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2 stages history hs hh
    stagesOrdinal trace h D A hA dataD
  have unionFacts := M.semanticStructuralTrace_aligned_copy_union c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace infinite choice small meet I S mu s.nonbottom.carrier tuples
    (fun f z entry => ((pair_mem_relationCompose S _ lifted _ _ f z).1 entry).2.1)
    (fun D f _ tau entry bound => M.liftedRowTuple_supported a s b C pairing unions powers separation
      infinite hL hC hG graph hmu muOrdinal valid f tau D entry bound.2)
    r oldRow row A oldA g h D X V source oldSource (pCode ▸ prepared)
    rowBelowOld reference.1 rowBelowH reference.2 relative overlap meetLeft meetRight meetGreatest
    transported.2.2 dataX descent
  let result : SetMembers upperQ := SetMembers.ofMem _ unionFacts.1
  have resultCode : SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) :=
    SetMembers.raw_ofMem _ _
  have movedCode := M.semanticStructuralAction_coordinates c act b s a ⊥ directed lifted squared
    (c.encode ⊤) pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order
    graph nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace h p r A pCode
  refine ⟨row, result, rowCode, resultCode, ?_, ?_⟩
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw (upperAct.iso h p)) ∈ _
    rw [resultCode, movedCode]
    exact unionFacts.2.1
  · change ZFSet.pair (SetMembers.raw result) (SetMembers.raw q) ∈ _
    rw [resultCode, qCode]
    exact unionFacts.2.2

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment
open SetFormula SetRealization
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable {run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I}
variable {level : GroundMainCandidateLevel M K} {i₀ : I}
variable (fulfilled : run.FinalFulfillment level i₀)

theorem structural_separating_copy_union
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (small : M.sets.Countable) (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets)
    {mu : ZFSet.{u}} (hmu : mu ∈ M.sets) (muOrdinal : ordinalSetProperty mu) :
  let geometry := run.finalGeometry i₀
  letI := geometry.group_code.toGroup
  letI := geometry.meet.order.toPartialOrder
  letI := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  ∀ valid : ∀ z ∈ T, IsName c z,
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
  ∀ (hLifted : lifted ∈ M.sets) (hSquared : squared ∈ M.sets)
    (valid1 : ∀ z ∈ lifted, IsName c.pairEmpty z)
    (valid2 : ∀ z ∈ squared, IsName c.pairEmpty z)
    (closed1 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ lifted → (act.act c.pairEmpty g tau).val ∈ lifted)
    (closed2 : ∀ g (tau : Name c.pairEmpty), tau.val ∈ squared → (act.act c.pairEmpty g tau).val ∈ squared)
    (children1 : ∀ tau : Name c.pairEmpty, tau.val ∈ lifted →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (children2 : ∀ tau : Name c.pairEmpty, tau.val ∈ squared →
      HereditarilySymmetric act c.pairEmpty (a.principalSupportFamily ⊥ directed) tau)
    (stages history : ZFSet.{u}) (hs : stages ∈ M.sets) (hh : history ∈ M.sets)
    (stagesOrdinal : ordinalSetProperty stages)
    (trace : OrdinalRecursionTrace (fun level prior stage => stage =
      M.structuralForcingStage c.carrier c.conditionOrder (c.encode ⊤) (act.actionGraph c b)
        b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
        (supportBasisCode s b a.principalFix) lifted squared level prior) stages history),
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  ∀ (p q : SetMembers upperQ) (r oldRow : SetMembers c.carrier) (A oldA : ZFSet.{u})
    (g1 g2 : SetMembers geometry.actors) (dBound X W : SetMembers geometry.carrier),
    SetMembers.raw p = ZFSet.pair (c.encode r) A →
    SetMembers.raw q = ZFSet.pair (c.encode oldRow) oldA →
    StoredPreparedConditionCode M c.carrier lifted stages packed s.carrier (SetMembers.raw p) →
    q ≤ upperAct.iso g1 p →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw r) → i ≤ dBound) →
    (∀ i : SetMembers geometry.carrier, s.encode i ∈ rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw oldRow) → i ≤ X) →
    (∀ z ∈ A, ZFSet.pair z (s.encode dBound) ∈
      stageOneDataBounds A I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    (∀ z ∈ oldA, ZFSet.pair z (s.encode X) ∈
      stageOneDataBounds oldA I lifted S s.carrier mu s.nonbottom.carrier s.conditionOrder anchors tuples) →
    W ≤ dBound → g1 ∈ a.principalFix W → g2 ∈ a.principalFix W →
    a.iso g1 dBound ≤ X → a.iso g2 dBound ≤ X →
    (∀ (alpha : ZFSet.{u}) (member : alpha ∈ stages),
      let hAlpha := M.transitive hs member
      let cutOrdinal := ordinalSetProperty_member stagesOrdinal member
      let subset := (And.left stagesOrdinal) alpha member
      let lowerPacked := graphRestriction alpha packed
      let Q := M.refinementHistoryForcing c.carrier lifted alpha lowerPacked
      letI := M.refinementHistoryPartialOrder c.conditionOrder_code lifted alpha lowerPacked
      let lower := SetMembers.presentation Q
      let localAct := M.semanticStructuralPrefixAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
        pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
        nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
        topMem topRows hh trace hAlpha cutOrdinal subset
      ∀ (H : ConditionFilter (SetMembers Q)),
        H.GenericFor (M.codedFamily lower) → H.GenericFor (formulaFamily (M.nameDomain lower)) →
        ∀ (v w : SetMembers geometry.carrier) (x y : (M.nameDomain lower).names),
          a.principalFix v ≤ localAct.stabilizer lower x.val →
          a.principalFix w ≤ localAct.stabilizer lower y.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) x.val →
          HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) y.val →
          Name.eval {p | H.mem p} x.val = Name.eval {p | H.mem p} y.val →
          ∃ tau : (M.nameDomain lower).names,
            HereditarilySymmetric localAct lower (a.principalSupportFamily ⊥ directed) tau.val ∧
            a.principalFix (geometry.meet.smallMeet v w) ≤ localAct.stabilizer lower tau.val ∧
            Name.eval {p | H.mem p} tau.val = Name.eval {p | H.mem p} x.val) →
    ∃ h : SetMembers geometry.actors,
      h ∈ a.principalFix W ∧
      geometry.meet.smallMeet (a.iso h dBound) X = W ∧
      geometry.meet.smallMeet (a.iso h dBound) (a.iso g1 dBound) = W ∧
      geometry.meet.smallMeet (a.iso h dBound) (a.iso g2 dBound) = W ∧
    (let movedA := M.structuralAssignmentImage b.carrier s.carrier s.conditionOrder (a.actionGraph s b)
      (supportBasisCode s b a.principalFix) lifted squared stages history (b.encode h) A;
    ∃ row : SetMembers c.carrier, ∃ result : SetMembers upperQ,
      SetMembers.raw row = SetMembers.raw oldRow ∪ SetMembers.raw (act.iso h r) ∧
      SetMembers.raw result = ZFSet.pair (c.encode row) (movedA ∪ oldA) ∧
      result ≤ q ∧ result ≤ upperAct.iso h p) := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let hL := geometry.carrier_ground
  let hG := geometry.actors_ground
  let hC := hColumns
  let order : s.conditionOrder ∈ M.sets := geometry.decoded_order_eq.symm ▸ geometry.order_ground
  let graph : a.actionGraph s b ∈ M.sets := geometry.decoded_action_eq.symm ▸ geometry.action_ground
  let nodeMaps := M.conditionMapFamily_mem_of_actionGraph a s b pairing unions powers separation
    collection hL hG graph
  let supports := geometry.decoded_supportBasis_ground pairing unions powers separation
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite hL hC hG graph
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  let rows := M.binaryRowNameGraph s.nonbottom.carrier columns ⊤
  let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
  let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S
  dsimp only
  intro valid
  let lifted := Name.renamedFamily c.pairEmpty id T valid
  let squared := orderedPairNameFamily (c.pairEmpty.encode ⊤) lifted lifted
  let tuples := liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier rows.sUnion.sUnion rows S valid
  intro hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
    stages history hs hh stagesOrdinal trace
  let coordinates := M.prod_mem pairing unions powers separation (M.nonbottom_carrier_mem s separation hL) hC
  let two := M.natSetCode_mem separation infinite 2
  let carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinates two
  let forcingOrder := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinates two
  let forcingAction := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite hL hC hG graph
  let omega := M.omega_mem separation infinite
  let topMem := c.encode_mem ⊤
  let topRows : ∀ r ∈ c.carrier, ZFSet.pair r (c.encode ⊤) ∈ c.conditionOrder :=
    fun r hr => by
      obtain ⟨r, rfl⟩ := (c.mem_carrier r).1 hr
      exact (c.pair_mem_conditionOrder r ⊤).2 le_top
  let packed := M.structuralRefinementHistory b.carrier s.carrier s.conditionOrder
    (supportBasisCode s b a.principalFix) lifted squared stages history
  let I := refinementDataHistoryIndices stages packed
  let anchors := refinementIndexFieldGraph I s.carrier 2
  let upperQ := M.refinementHistoryForcing c.carrier lifted stages packed
  let := M.refinementHistoryPartialOrder c.conditionOrder_code lifted stages packed
  let upperAct := M.semanticStructuralAction c act b s a ⊥ directed lifted squared (c.encode ⊤)
    pairing unions powers separation collection carrier forcingOrder forcingAction hG hL order graph
    nodeMaps supports hLifted hSquared omega valid1 valid2 closed1 closed2 children1 children2
    topMem topRows hs hh stagesOrdinal trace
  intro p q r oldRow A oldA g1 g2 dBound X W pCode qCode prepared below
    usedD usedX dataD dataX wd fixed1 fixed2 bound1 bound2 descent
  have fixedLower (g : SetMembers geometry.actors) (fixed : g ∈ a.principalFix W) :
      W ≤ a.iso g dBound := by
    have lower := (a.iso g).monotone wd
    rw [fixed W le_rfl] at lower
    exact lower
  obtain ⟨h, fixed, overlap⟩ := fulfilled.decoded_separate_at W dBound X wd
    ((fixedLower g1 fixed1).trans bound1)
  have relative : g1⁻¹ * h ∈ a.principalFix W :=
    (a.principalFix W).mul_mem ((a.principalFix W).inv_mem fixed1) fixed
  have overlapMoved : geometry.meet.smallMeet (a.iso h dBound) X = a.iso h W :=
    overlap.trans (fixed W le_rfl).symm
  obtain ⟨row, result, rowCode, resultCode, toH, toOld⟩ :=
    M.binaryRowStructural_aligned_copy_union a s b columns pairing unions powers separation
      collection infinite hL order hC hG graph nodeMaps supports directed choice small geometry.meet.smallMeet
      hmu muOrdinal valid hLifted hSquared valid1 valid2 closed1 closed2 children1 children2
      stages history hs hh stagesOrdinal trace p q r oldRow A oldA g1 h dBound X W
      pCode qCode prepared below usedD usedX dataD dataX relative overlapMoved
      (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
      (geometry.meet.toSmallMeetOrder.meet_le_right _ _)
      (fun _ left right => geometry.meet.toSmallMeetOrder.le_meet left right) descent
  have apart (Y : SetMembers geometry.carrier) (wy : W ≤ Y) (yx : Y ≤ X) :
      geometry.meet.smallMeet (a.iso h dBound) Y = W := by
    apply le_antisymm
    · rw [← overlap]
      exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
        (le_trans (geometry.meet.toSmallMeetOrder.meet_le_right _ _) yx)
    · exact geometry.meet.toSmallMeetOrder.le_meet (fixedLower h fixed) wy
  exact ⟨h, fixed, overlap, apart _ (fixedLower g1 fixed1) bound1,
    apart _ (fixedLower g2 fixed2) bound2, row, result, rowCode, resultCode, toOld, toH⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
