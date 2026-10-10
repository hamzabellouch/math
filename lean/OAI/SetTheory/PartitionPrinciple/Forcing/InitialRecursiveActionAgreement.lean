import OAI.SetTheory.PartitionPrinciple.Definability.RecursiveActionRealization
import OAI.SetTheory.PartitionPrinciple.Transfinite.InitialRecursiveTaskLaws

namespace OAI

namespace PartitionPilot.Forcing.CodedRecursiveTaskAction

universe u
variable {D rD μD J Qs rs μs As Es Fs Ss I Maps Sources Reps G m inv one A T : ZFSet.{u}}
variable {d : AttachmentBatchInputs D rD μD J Qs rs μs As Es Fs Ss}
variable {h : CodedRecursiveMapInputs d I Maps Sources Reps G m inv one A}
variable (s : CodedRecursiveTaskAction h T)
variable (M : TransitiveGround.{u}) (next : h.NextInputs M)

include s in
theorem nextAction_agreement
    (g k : {g : ZFSet.{u} // g ∈ G})
    (topPoint : {x : ZFSet.{u} // x ∈ D})
    (top : ∀ x ∈ D, ZFSet.pair x topPoint.val ∈ rD)
    (v : {x : ZFSet.{u} // x ∈ D}) (positive : ZFSet.{u} → Prop)
    (negative : ∀ i S a cap base w,
      ZFSet.pair i S ∈ Maps → ZFSet.pair i a ∈ Sources →
      ZFSet.pair topPoint.val cap ∈ S → ZFSet.pair a base ∈ S →
      ¬ positive i → ZFSet.pair (ZFSet.pair cap v.val) w ∈ d.batchMeetGraph →
      ZFSet.pair w base ∈ d.batchOrder)
    (currentAgree : ActionAgreementBelow d.batchCarrier d.batchOrder A g.val k.val v.val)
    (taskAgree : ∀ i i' i'', positive i →
      ZFSet.pair (ZFSet.pair g.val i) i' ∈ T →
      ZFSet.pair (ZFSet.pair k.val i) i'' ∈ T → i' = i'') :
    ActionAgreementBelow next.batchCarrier next.batchOrder
      (h.nextActionGraph T) g.val k.val v.val := by
  have typedNegative : ∀ i : {i : ZFSet.{u} // i ∈ I}, ¬ positive i.val →
      d.templates.extension.le
        (d.templates.extension.meet ((h.toInputs.previous i).toFun topPoint) (.inl v))
        ((h.toInputs.previous i).toFun (h.toInputs.source i)) := by
    intro i notPositive
    apply (d.coding.le_encode _ _).1
    exact negative i.val (h.maps.value i) (h.source i).val _ _ _
      (h.maps.value_entry i) (h.source_entry i)
      (h.toInputs_previous_entry i topPoint)
      (h.toInputs_previous_entry i (h.toInputs.source i)) notPositive
      (d.coding.encoded_meet_entry ((h.toInputs.previous i).toFun topPoint) (.inl v))
  have typedCurrent : ∀ x, d.templates.extension.le x (.inl v) →
      (s.toTaskSymmetry g).current.toFun x = (s.toTaskSymmetry k).current.toFun x := by
    intro x lower
    apply d.coding.encode_injective
    exact currentAgree.entry_eq h.action k.property (d.coding.encode_mem x)
      ((d.coding.le_encode x (.inl v)).2 lower)
      (s.toTaskSymmetry_current_entry g x) (s.toTaskSymmetry_current_entry k x)
  have typedTasks : ∀ i : {i : ZFSet.{u} // i ∈ I}, positive i.val →
      (s.toTaskSymmetry g).perm i = (s.toTaskSymmetry k).perm i := by
    intro i pos
    exact Subtype.ext (taskAgree i.val _ _ pos
      (s.toTaskSymmetry_perm_entry g i) (s.toTaskSymmetry_perm_entry k i))
  have outputs {x y z : ZFSet.{u}} (hx : x ∈ next.batchCarrier)
      (lower : ZFSet.pair x v.val ∈ next.batchOrder)
      (first : ZFSet.pair (ZFSet.pair g.val x) y ∈ h.nextActionGraph T)
      (second : ZFSet.pair (ZFSet.pair k.val x) z ∈ h.nextActionGraph T) : y = z := by
    obtain ⟨a, rfl⟩ := h.nextEncode_surjective M next x hx
    have below := (h.next_le_encode M next a (.inl (.inl v))).1 lower
    have same := (s.toTaskSymmetry g).agreement_persists (s.toTaskSymmetry k)
      topPoint (fun p => top p.val p.property) v (fun i => positive i.val)
      typedNegative typedCurrent typedTasks a below
    exact ((s.nextAction_entry_iff M next g a y).1 first).trans
      ((congrArg (h.nextEncode M next) same).trans
        ((s.nextAction_entry_iff M next k a z).1 second).symm)
  intro x hx y _ lower
  constructor
  · intro first
    obtain ⟨z, second, _⟩ := (s.nextAction_code M next).function.2
      (ZFSet.pair k.val x) (ZFSet.pair_mem_prod.2 ⟨k.property, hx⟩)
    exact (outputs hx lower first second).symm ▸ second
  · intro second
    obtain ⟨z, first, _⟩ := (s.nextAction_code M next).function.2
      (ZFSet.pair g.val x) (ZFSet.pair_mem_prod.2 ⟨g.property, hx⟩)
    exact outputs hx lower first second ▸ first

end PartitionPilot.Forcing.CodedRecursiveTaskAction

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem groundInitialTaskAction
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P)
      (constantFamilyGraph I r) As (literalTaskBaseGraph I P R U Labels)
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    ∀ Reps (h : CodedRecursiveMapInputs d I Maps As Reps G m inv one B),
      CodedRecursiveTaskAction h (M.groundTaskTransport P G r μ A Labels) := by
  dsimp only
  intro Reps h
  refine ⟨M.groundTaskTransport_setAction pairing unions powers separation hP hG hA
    group action meet, ?_, ?_⟩
  · intro g i j a b task first second
    exact M.groundInitialTask_source task first second
  · intro g i j S S' q x y task first second image image'
    exact M.groundInitialTask_intertwine pairing unions powers separation hP hG hr hμ hA hLabels
      group action meet task first second image image'

theorem groundInitialTask_positive_agreement
    {P G r μ A Labels m inv one g h v i i' i'' F : ZFSet.{u}}
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (agree : ActionAgreementBelow P r A g h v)
    (filter : ZFSet.pair i F ∈ literalTaskFilterGraph (M.groundEligibleTasks P G r μ A Labels)
      P (M.groundRelations P P) (M.groundMeetFilters P r μ) Labels)
    (positive : v ∈ F)
    (first : ZFSet.pair (ZFSet.pair g i) i' ∈ M.groundTaskTransport P G r μ A Labels)
    (second : ZFSet.pair (ZFSet.pair h i) i'' ∈ M.groundTaskTransport P G r μ A Labels) :
    i' = i'' := by
  have hi := ((triple_mem_taskTransportGraph G _ P _ _ Labels A g i i').1 first).2.1
  obtain ⟨a, ha, c, hc, base, hb, s, hs, F', hF, label, hl, equal, _⟩ :=
    (mem_eligibleTaskSet P G r μ A _ _ Labels i).1 hi
  have filterEq : F = F' :=
    ((literalTaskFieldGraph_entry_iff ha hc hb hs hF hl 4).1 (equal ▸ filter)).2
  exact M.groundTaskTransport_positive_agreement group action meet agree
    (filterEq ▸ positive) (equal ▸ first) (equal ▸ second)

theorem groundInitialRecursiveAction_agreement
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P G r μ A Labels m inv one T g h v : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets)
    (hA : A ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
    (meet : MeetOrderCode P r μ) (hT : T ∈ P)
    (top : ∀ x ∈ P, ZFSet.pair x T ∈ r)
    (hg : g ∈ G) (hh : h ∈ G) (hv : v ∈ P)
    (agree : ActionAgreementBelow P r A g h v) :
    let I := M.groundEligibleTasks P G r μ A Labels
    let R := M.groundRelations P P
    let U := M.groundMeetFilters P r μ
    let As := literalTaskSourceGraph I P R U Labels
    let Maps := M.batchEmbeddingFamily I P (constantFamilyGraph I P) (constantFamilyGraph I r)
      As (literalTaskBaseGraph I P R U Labels)
    let d := M.groundEligibleTaskBatchInputs (Labels := Labels) group action meet
    let B := M.groundEligibleBatchAction P G r μ A Labels
    ∀ Reps (inputs : CodedRecursiveMapInputs d I Maps As Reps G m inv one B)
      (next : inputs.NextInputs M),
      ActionAgreementBelow next.batchCarrier next.batchOrder
        (inputs.nextActionGraph (M.groundTaskTransport P G r μ A Labels)) g h v := by
  dsimp only
  intro Reps inputs next
  let I := M.groundEligibleTasks P G r μ A Labels
  let R := M.groundRelations P P
  let U := M.groundMeetFilters P r μ
  let positive : ZFSet.{u} → Prop := fun i =>
    ∃ F, ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels ∧ v ∈ F
  have symmetry := M.groundInitialTaskAction pairing unions powers separation
    hP hG hr hμ hA hLabels group action meet Reps inputs
  apply symmetry.nextAction_agreement M next ⟨g, hg⟩ ⟨h, hh⟩ ⟨T, hT⟩ top ⟨v, hv⟩ positive
  · intro i S a cap base w mapEntry source capEntry baseEntry negative entry
    have hi := inputs.maps.pair_source mapEntry
    obtain ⟨a', ha, c, hc, ell, hell, sep, hsep, F, hF, label, hl, equal, _⟩ :=
      (mem_eligibleTaskSet P G r μ A R U Labels i).1 hi
    have target : ZFSet.pair i c ∈ literalTaskTargetGraph I P R U Labels := by
      rw [equal]
      exact (literalTaskFieldGraph_entry_iff ha hc hell hsep hF hl 1).2 ⟨equal ▸ hi, rfl⟩
    have filter : ZFSet.pair i F ∈ literalTaskFilterGraph I P R U Labels := by
      rw [equal]
      exact (literalTaskFieldGraph_entry_iff ha hc hell hsep hF hl 4).2 ⟨equal ▸ hi, rfl⟩
    exact M.groundInitialMap_negative_cap pairing unions powers separation
      hP hG hr hμ hA hLabels group action meet hT top mapEntry source target filter
      capEntry baseEntry hv (fun hvF => negative ⟨F, filter, hvF⟩) entry
  · exact M.groundEligibleBatchAction_agreement pairing unions powers separation
      hP hG hA group action meet hg hh hv agree
  · intro i i' i'' hp first second
    obtain ⟨F, filter, hvF⟩ := hp
    exact M.groundInitialTask_positive_agreement group action meet agree filter hvF first second

end PartitionPilot.Forcing.TransitiveGround

end OAI
