import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainFinalStructuralCommonSupportInduction

namespace OAI

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

theorem internalRow_rectangle_refinement
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
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    ∀ (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (V W d : SetMembers geometry.carrier) (x y : Name c),
      (∀ i : {i : SetMembers geometry.carrier // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → i.val ≤ d) →
      V ≤ d → W ≤ d →
      a.principalFix V ≤ act.stabilizer c x → a.principalFix W ≤ act.stabilizer c y →
      ∀ (g₁ g₂ : SetMembers geometry.actors),
        g₁ ∈ a.principalFix (geometry.meet.smallMeet V W) →
        g₂ ∈ a.principalFix (geometry.meet.smallMeet V W) →
        geometry.meet.smallMeet (a.iso g₁ d) (a.iso g₂ d) = geometry.meet.smallMeet V W →
        ∀ r, r ≤ act.iso g₁ p → r ≤ act.iso g₂ p →
          DenseBelow r (act.RectangleWitness c p x y g₁ g₂) := by
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
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  dsimp only
  intro p V W d x y bp vd wd sx sy g₁ g₂ fixed₁ fixed₂ separated r ref₁ ref₂ q qr
  obtain ⟨X, upper₁, upper₂, bq⟩ := fulfilled.internalRow_bounds_with infinite choice columns hColumns
    q (a.iso g₁ d) (a.iso g₂ d)
  have request := geometry.decoded_rectangle_request V W d g₁ g₂ vd wd fixed₁ fixed₂ separated
  obtain ⟨h₁, h₂, rectangle, t, _, tq, th₁, th₂⟩ := fulfilled.internalRow_rectangle_union
    infinite choice columns hColumns p q d X V W g₁ g₂ request upper₁ upper₂ bp bq
    (le_trans qr ref₁) (le_trans qr ref₂)
  have agree (g h : SetMembers geometry.actors) (v : SetMembers geometry.carrier)
      (rawAgree : ActionAgreementBelow geometry.carrier geometry.order geometry.action
        (SetMembers.raw g) (SetMembers.raw h) (SetMembers.raw v)) :
      ∀ i, i ≤ v → a.iso g i = a.iso h i := by
    intro i lower
    apply SetMembers.raw_injective
    exact rawAgree.entry_eq geometry.action_code (SetMembers.raw_mem h) (SetMembers.raw_mem i)
      lower (geometry.action_code.act_mem g i) (geometry.action_code.act_mem h i)
  let geom := geometry.action_code.toOrderAction geometry.group_code geometry.meet
  exact ⟨t, tq, h₁, h₂, th₁, th₂,
    act.act_eq_of_support_agreement geom c sx (agree h₁ g₁ V rectangle.first_agreement),
    act.act_eq_of_support_agreement geom c sx (agree h₂ g₂ V rectangle.second_agreement),
    act.act_eq_of_support_agreement geom c sy (agree h₁ h₂ W rectangle.common_agreement)⟩

theorem internalRow_separation_refinement
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
    ∀ (p : SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega))
      (W d : SetMembers geometry.carrier),
      (∀ i : {i : SetMembers geometry.carrier // i ≠ ⊥}, s.encode i.val ∈
        rowUsedRows s.nonbottom.carrier columns (natSetCode 2) (SetMembers.raw p) → i.val ≤ d) →
      W ≤ d → ∀ (g₁ g₂ : SetMembers geometry.actors),
        g₁ ∈ a.principalFix W → g₂ ∈ a.principalFix W →
        ∀ r, r ≤ act.iso g₁ p →
          DenseBelow r (act.SeparationWitness (a.principalFix W)
            (fun g h => geometry.meet.smallMeet (a.iso g d) (a.iso h d) = W) p g₁ g₂) := by
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
  intro p W d bp wd g₁ g₂ fixed₁ fixed₂ r ref₁ q qr
  obtain ⟨X, upper₁, upper₂, bq⟩ := fulfilled.internalRow_bounds_with infinite choice columns hColumns
    q (a.iso g₁ d) (a.iso g₂ d)
  have fixedLower (g : SetMembers geometry.actors) (fixed : g ∈ a.principalFix W) :
      W ≤ a.iso g d := by
    have lower := (a.iso g).monotone wd
    rw [fixed W le_rfl] at lower
    exact lower
  have lower₁ := fixedLower g₁ fixed₁
  have lower₂ := fixedLower g₂ fixed₂
  obtain ⟨h, fixed, overlap⟩ := fulfilled.decoded_separate_at W d X wd (le_trans lower₁ upper₁)
  have overlap' : ∀ i, i ≤ a.iso h d → i ≤ X → i ≤ a.iso h W := by
    intro i ih ix
    rw [fixed W le_rfl, ← overlap]
    exact geometry.meet.toSmallMeetOrder.le_meet ih ix
  obtain ⟨t, _, tq, th⟩ := M.internalRowAction_one_copy_union a s b columns
    pairing unions powers separation infinite geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground) choice p q d X W g₁ h
    bp bq (le_trans qr ref₁) overlap' (fun z hz => (fixed z hz).trans (fixed₁ z hz).symm)
  have sep (Y : SetMembers geometry.carrier) (wy : W ≤ Y) (yx : Y ≤ X) :
      geometry.meet.smallMeet (a.iso h d) Y = W := by
    apply le_antisymm
    · rw [← overlap]
      exact geometry.meet.toSmallMeetOrder.le_meet
        (geometry.meet.toSmallMeetOrder.meet_le_left _ _)
        (le_trans (geometry.meet.toSmallMeetOrder.meet_le_right _ _) yx)
    · exact geometry.meet.toSmallMeetOrder.le_meet (fixedLower h fixed) wy
  exact ⟨t, tq, h, fixed, th, sep _ lower₁ upper₁, sep _ lower₂ upper₂⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

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

theorem internalRow_common_support
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (columns : ZFSet.{u}) (hColumns : columns ∈ M.sets) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let directed := geometry.decoded_directed fulfilled.directed
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    ∀ (H : ConditionFilter (SetMembers (M.smallPartialFunctions
        (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)))
      (_genericCoded : H.GenericFor (M.codedFamily c))
      (_genericFormula : H.GenericFor (formulaFamily (M.nameDomain c)))
      (V W : SetMembers geometry.carrier) (x y : Name c)
      (_hx : x.val ∈ M.sets) (_hy : y.val ∈ M.sets)
      (_sx : a.principalFix V ≤ act.stabilizer c x)
      (_sy : a.principalFix W ≤ act.stabilizer c y)
      (_hs : HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) x)
      (_values : Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} y),
      ∃ z : Name c, z.val ∈ M.sets ∧
        HereditarilySymmetric act c (a.principalSupportFamily ⊥ directed) z ∧
        a.principalFix (geometry.meet.smallMeet V W) ≤ act.stabilizer c z ∧
        Name.nameRank z ≤ Name.nameRank x ∧
        Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let s := SetMembers.presentation geometry.carrier
  let b := SetMembers.presentation geometry.actors
  let a := geometry.decodedAction
  let directed := geometry.decoded_directed fulfilled.directed
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
  let act := M.internalRowAction a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  let c := SetMembers.presentation (M.smallPartialFunctions
    (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
  dsimp only
  intro H genericCoded genericFormula V W x y hx hy sx sy hs values
  have coordinateGround := M.rowCoordinate_carrier_mem s columns pairing unions powers separation
    geometry.carrier_ground hColumns
  have bits := M.natSetCode_mem separation infinite 2
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite coordinateGround bits
  have order := M.countableFunctionOrder_mem pairing unions powers separation infinite coordinateGround bits
  have actionGraph := M.internalRowActionGraph_mem a s b columns pairing unions powers separation infinite
    geometry.carrier_ground hColumns geometry.actors_ground
    (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
  have maps := M.conditionMapFamily_mem_of_actionGraph act c b pairing unions powers separation collection
    carrier geometry.actors_ground actionGraph
  have atoms : H.GenericFor (Name.atomicFamily (M.nameDomain c)) :=
    fun E hE dense => genericFormula E (Or.inl hE) dense
  obtain ⟨p, hp, forced⟩ := (Name.eval_eq_iff_forcesEq (M.nameDomain c) H atoms hx hy).1 values
  obtain ⟨d, vd, wd, bounds⟩ := fulfilled.internalRow_bounds_with infinite choice columns hColumns p V W
  let meet := geometry.meet.smallMeet V W
  let subgroup := a.principalFix meet
  let apart := fun g h => geometry.meet.smallMeet (a.iso g d) (a.iso h d) = meet
  have meetBelow : meet ≤ d :=
    le_trans (geometry.meet.toSmallMeetOrder.meet_le_left V W) vd
  have copies : H.GenericFor (act.copyWitnessFamily c subgroup apart p x y) := by
    exact geometry.internalRow_copyWitness_generic pairing unions powers separation collection
      infinite columns hColumns p x y hx hy meet d H genericCoded
  have translated : ∀ g, H.mem (act.iso g p) →
      Name.eval {q | H.mem q} (act.act c g x) = Name.eval {q | H.mem q} (act.act c g y) := by
    intro g active
    exact Name.forcesEq_sound (M.nameDomain c) H atoms _
      (M.act_mem c act b pairing unions powers separation collection carrier maps g x hx) _
      (M.act_mem c act b pairing unions powers separation collection carrier maps g y hy)
      _ active (act.forcesEq_act c g forced)
  have captured := act.mix_capture_from_refinements c subgroup apart p x y H copies hp translated
    (by
      intro g₁ hg₁ g₂ hg₂ separated r ref₁ ref₂
      exact fulfilled.internalRow_rectangle_refinement infinite choice columns hColumns p V W d x y
        bounds vd wd sx sy g₁ g₂ hg₁ hg₂ separated r ref₁ ref₂)
    (by
      intro g₁ hg₁ g₂ hg₂ r ref₁ _
      exact fulfilled.internalRow_separation_refinement infinite choice columns hColumns p meet d
        bounds meetBelow g₁ g₂ hg₁ hg₂ r ref₁)
  refine ⟨act.mix c subgroup p x,
    M.basis_mix_mem b s a.principalFix act c pairing unions powers separation collection carrier order
      geometry.actors_ground geometry.carrier_ground
      (geometry.decoded_supportBasis_ground pairing unions powers separation) maps meet p x hx,
    act.mix_hs c (a.principalSupportFamily ⊥ directed) subgroup ⟨meet, le_rfl⟩ p hs,
    ?_, act.nameRank_mix_le c subgroup p x, captured⟩
  intro g hg
  exact act.mix_fixed c subgroup p x hg

theorem exists_rowModel_with_descent
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (groundChoice : Realize M.sets SetFormula.choice Fin.elim0) (small : M.sets.Countable) :
    let geometry := run.finalGeometry i₀
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    letI := geometry.decodedBottom
    let s := SetMembers.presentation geometry.carrier
    let b := SetMembers.presentation geometry.actors
    let a := geometry.decodedAction
    let columns := M.groundOmegaOne pairing unions powers separation collection infinite
    let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega
    let act := M.internalRowAction a s b columns pairing unions powers separation infinite
      geometry.carrier_ground hColumns geometry.actors_ground
      (geometry.decoded_action_eq.symm ▸ geometry.action_ground)
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)
    let F := a.principalSupportFamily (⊥ : SetMembers geometry.carrier)
      (geometry.decoded_directed fulfilled.directed)
    ∀ p : SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega),
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier columns) (natSetCode 2) ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ¬ Realize ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q})
        SetFormula.choice Fin.elim0 ∧
      ∀ (V W : SetMembers geometry.carrier) (x y : (M.nameDomain c).names),
        a.principalFix V ≤ act.stabilizer c x.val →
        a.principalFix W ≤ act.stabilizer c y.val →
        HereditarilySymmetric act c F x.val →
        Name.eval {q | H.mem q} x.val = Name.eval {q | H.mem q} y.val →
        ∃ z : (M.nameDomain c).names, HereditarilySymmetric act c F z.val ∧
          a.principalFix (geometry.meet.smallMeet V W) ≤ act.stabilizer c z.val ∧
          Name.nameRank z.val ≤ Name.nameRank x.val ∧
          Name.eval {q | H.mem q} z.val = Name.eval {q | H.mem q} x.val := by
  let geometry := run.finalGeometry i₀
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let := geometry.decodedBottom
  let columns := M.groundOmegaOne pairing unions powers separation collection infinite
  let hColumns := (M.groundOmegaOne_spec pairing unions powers separation collection infinite).1
  dsimp only
  intro p
  obtain ⟨H, hp, coded, ordinary, symmetric, included, zf, notChoice⟩ :=
    fulfilled.exists_rowModel collection infinite groundChoice small p
  refine ⟨H, hp, coded, ordinary, symmetric, included, zf, notChoice, ?_⟩
  intro V W x y sx sy hs values
  obtain ⟨z, hz, symmetricZ, support, rank, equal⟩ := fulfilled.internalRow_common_support
    collection infinite groundChoice columns hColumns H coded ordinary V W x.val y.val
    x.property y.property sx sy hs values
  exact ⟨⟨z, hz⟩, symmetricZ, support, rank, equal⟩

end PartitionPilot.Forcing.GroundMainPrefix.FinalFulfillment

end OAI
