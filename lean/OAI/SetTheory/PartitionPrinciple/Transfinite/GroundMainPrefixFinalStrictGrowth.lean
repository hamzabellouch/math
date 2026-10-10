import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMainPrefixRectangleBoundTransport
import OAI.SetTheory.PartitionPrinciple.Forcing.MainPrefixConditionalTraceLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTaskBearingSeparation
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTaskBearingStrictTop

namespace OAI

namespace PartitionPilot.Forcing.GroundMainPrefix
open SetFormula
universe u v
variable {M : TransitiveGround.{u}} {K Labels C D rD : ZFSet.{u}}
variable {pairing : Realize M.sets SetFormula.pairing Fin.elim0}
variable {unions : Realize M.sets SetFormula.union Fin.elim0}
variable {powers : Realize M.sets powerSet Fin.elim0} {separation : SeparationSchema M.sets}
variable {I : Type v} [Small.{u} I] [Preorder I]
variable (run : GroundMainPrefix M K Labels C D rD pairing unions powers separation I)

theorem selectedStep_terminal_entry {old next f : ZFSet.{u}} {i j : I}
    (before : i ≤ j) (adjacent : run.key j = insert (run.key i) (run.key i))
    (oldIndex : MainPrefixAtIndex (insert (run.key i) (run.key i)) old)
    (selected : MainPrefixSelectedStepCode f old next)
    (oldExtension : MainPrefixExtends old run.code)
    (nextExtension : MainPrefixExtends next run.code) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  obtain ⟨F, G, oldEqual⟩ := oldIndex
  obtain ⟨b, S, E, S', E', a, target, z, first, second, _, sourceEntry,
    selectedEntry, targetEntry, mapEntry⟩ := selected
  have same : b = run.key i := setSuccessor_injective
    (mainPrefixCode_inj.1 (first.symm.trans oldEqual)).1
  subst b
  rw [first] at oldExtension
  rw [second] at nextExtension
  have oldIncluded := (mainPrefixExtends_iff.1 oldExtension).2.1
  have nextIncluded := (mainPrefixExtends_iff.1 nextExtension).2
  have sourceEqual := (run.stageGraph_entry i a).1 (oldIncluded sourceEntry)
  have targetActual : ZFSet.pair (run.key j) target ∈ run.stageGraph := by
    rw [adjacent]
    exact nextIncluded.1 targetEntry
  have targetEqual := (run.stageGraph_entry j target).1 targetActual
  have mapActual : ZFSet.pair (ZFSet.pair (run.key j) (run.key i)) z ∈ run.transitionGraph := by
    rw [adjacent]
    exact nextIncluded.2 mapEntry
  have mapEqual := (run.transitionGraph_entry before z).1 mapActual
  rw [sourceEqual, targetEqual, mapEqual] at selectedEntry
  exact selectedEntry

theorem terminal_successor_entry {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    ZFSet.pair (run.linked i).code
      (ZFSet.pair (run.linked j).code (run.diagram.transition before).map.code) ∈ f := by
  have oldMember : run.key i ∈ A := domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have nextMember : insert (run.key i) (run.key i) ∈ A := by
    rw [← adjacent]
    exact domain ▸ ZFSet.mem_range.2 ⟨j, rfl⟩
  obtain ⟨old, oldEntry⟩ := trace.1.total oldMember
  obtain ⟨next, nextEntry⟩ := trace.1.total nextMember
  have selected := trace.mainPrefix_selected_successor chosen
    (domain ▸ run.indices_ordinal) nextMember oldEntry nextEntry
  exact run.selectedStep_terminal_entry before adjacent (trace.mainPrefix_values oldEntry).2
    selected (extension _ _ oldEntry) (extension _ _ nextEntry)

theorem terminal_successor_taskBearing {A B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g) A p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = A) (extension : MainPrefixHistoryExtends p run.code)
    {i j : I} (before : i ≤ j)
    (adjacent : run.key j = insert (run.key i) (run.key i)) :
    TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega
      (run.linked i).code (run.linked j).code (run.diagram.transition before).map.code :=
  tasks _ _ _ (run.terminal_successor_entry trace chosen domain extension before adjacent)

theorem final_rectangle_at_bound
    (edges : ∀ i, ∃ j, ∃ before : i ≤ j,
      RectangleFulfillmentCode (run.diagram.stage i).stage.carrier (run.diagram.stage i).stage.actors
        (run.diagram.stage i).stage.order (run.diagram.stage i).stage.meetGraph
        (run.diagram.stage i).stage.action (run.diagram.stage j).stage.carrier
        (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.order
        (run.diagram.stage j).stage.meetGraph (run.diagram.stage j).stage.action
        (run.diagram.transition before).map.points (run.diagram.transition before).map.actors)
    {c b d g h X : ZFSet.{u}}
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction c b d g h) (hX : X ∈ run.limitPoints)
    (firstUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair g d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder)
    (secondUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair h d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors, ∃ l ∈ run.limitActors,
      RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
        c b d g h X k l := by
  obtain ⟨i, c₀, b₀, d₀, X₀, g₀, h₀, hc, hb, hd, hXX, hg, hh,
    rfl, rfl, rfl, rfl, rfl, rfl⟩ := run.rectangle_data_coverage
      rectangle.1 rectangle.2.1 rectangle.2.2.1 hX rectangle.2.2.2.1 rectangle.2.2.2.2.1
  have localRectangle := run.limitRectangle_reflect i hc hb hd hg hh rectangle
  have firstLocal : ∀ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair (ZFSet.pair g₀ d₀) y ∈ (run.diagram.stage i).stage.action →
        ZFSet.pair y X₀ ∈ (run.diagram.stage i).stage.order := by
    intro y hy entry
    exact (run.limitLE_at i hy hXX).1 ((run.limitOrder_entry _ _).1
      (firstUpper _ (run.pointPresentation.limitPoint_mem hy) ((run.limitAction_at i hg hd hy).2 entry)))
  have secondLocal : ∀ y ∈ (run.diagram.stage i).stage.carrier,
      ZFSet.pair (ZFSet.pair h₀ d₀) y ∈ (run.diagram.stage i).stage.action →
        ZFSet.pair y X₀ ∈ (run.diagram.stage i).stage.order := by
    intro y hy entry
    exact (run.limitLE_at i hy hXX).1 ((run.limitOrder_entry _ _).1
      (secondUpper _ (run.pointPresentation.limitPoint_mem hy) ((run.limitAction_at i hh hd hy).2 entry)))
  obtain ⟨j, before, fulfills⟩ := edges i
  obtain ⟨c', imageC⟩ := run.pointSystem.map_entry_total before hc
  obtain ⟨b', imageB⟩ := run.pointSystem.map_entry_total before hb
  obtain ⟨d', imageD⟩ := run.pointSystem.map_entry_total before hd
  obtain ⟨X', imageX⟩ := run.pointSystem.map_entry_total before hXX
  obtain ⟨g', imageG⟩ := run.actorSystem.map_entry_total before hg
  obtain ⟨h', imageH⟩ := run.actorSystem.map_entry_total before hh
  obtain ⟨k, hk, l, hl, code⟩ := (run.diagram.transition before).map.rectangle_at_bound
    fulfills localRectangle hXX firstLocal secondLocal imageC imageB imageD imageX imageG imageH
  have finalCode := run.limitRectangleAtBound j
    (run.pointSystem.map_entry_bounds before imageC).2 (run.pointSystem.map_entry_bounds before imageB).2
    (run.pointSystem.map_entry_bounds before imageD).2 (run.pointSystem.map_entry_bounds before imageX).2
    (run.actorSystem.map_entry_bounds before imageG).2 (run.actorSystem.map_entry_bounds before imageH).2
    hk hl code
  rw [← run.pointPresentation.limitPoint_transition before imageC,
    ← run.pointPresentation.limitPoint_transition before imageB,
    ← run.pointPresentation.limitPoint_transition before imageD,
    ← run.pointPresentation.limitPoint_transition before imageX,
    ← run.actorPresentation.limitPoint_transition before imageG,
    ← run.actorPresentation.limitPoint_transition before imageH] at finalCode
  exact ⟨run.actorPresentation.limitPoint j k, run.actorPresentation.limitPoint_mem hk,
    run.actorPresentation.limitPoint j l, run.actorPresentation.limitPoint_mem hl, finalCode⟩

theorem final_rectangle_at_bound_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {c b d a a' X : ZFSet.{u}}
    (rectangle : ExternalRectangleCode run.limitPoints run.limitActors run.limitOrder
      run.limitMeetGraph run.limitAction c b d a a') (hX : X ∈ run.limitPoints)
    (firstUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair a d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder)
    (secondUpper : ∀ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair a' d) y ∈ run.limitAction →
      ZFSet.pair y X ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors, ∃ l ∈ run.limitActors,
      RectangleAtBoundCode run.limitPoints run.limitOrder run.limitMeetGraph run.limitAction
        c b d a a' X k l := by
  apply run.final_rectangle_at_bound _ rectangle hX firstUpper secondUpper
  intro i
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, run.rectangles_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_separation
    (edges : ∀ i, ∃ j, ∃ before : i ≤ j,
      SeparationFulfillmentCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage i).stage.order (run.diagram.stage j).stage.carrier
        (run.diagram.stage j).stage.order (run.diagram.stage j).stage.meetGraph
        (run.diagram.stage j).stage.actors (run.diagram.stage j).stage.action
        (run.diagram.transition before).map.points)
    {W d x : ZFSet.{u}} (hW : W ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hx : x ∈ run.limitPoints)
    (wd : ZFSet.pair W d ∈ run.limitOrder) (wx : ZFSet.pair W x ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors,
      (∀ z ∈ run.limitPoints, ZFSet.pair z W ∈ run.limitOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ run.limitAction) ∧
      ∃ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair k d) y ∈ run.limitAction ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ run.limitMeetGraph := by
  obtain ⟨i, w, d₀, x₀, hw₀, hd₀, hx₀, rfl, rfl, rfl⟩ :=
    run.pointPresentation.triple_coverage hW hd hx
  have wd' := (run.limitLE_at i hw₀ hd₀).1 ((run.limitOrder_entry _ _).1 wd)
  have wx' := (run.limitLE_at i hw₀ hx₀).1 ((run.limitOrder_entry _ _).1 wx)
  obtain ⟨j, before, fulfilled⟩ := edges i
  obtain ⟨w', ww⟩ := run.pointSystem.map_entry_total before hw₀
  obtain ⟨d', dd⟩ := run.pointSystem.map_entry_total before hd₀
  obtain ⟨x', xx⟩ := run.pointSystem.map_entry_total before hx₀
  have hw' := (run.pointSystem.map_entry_bounds before ww).2
  have hd' := (run.pointSystem.map_entry_bounds before dd).2
  have hx' := (run.pointSystem.map_entry_bounds before xx).2
  obtain ⟨k, hk, actor⟩ := fulfilled w hw₀
  obtain ⟨fixes, separates⟩ := actor w' hw' ww
  obtain ⟨y, acted, _⟩ := (run.diagram.stage j).stage.action_code.function.2
    (ZFSet.pair k d') (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
  have hy := (ZFSet.pair_mem_prod.1
    ((run.diagram.stage j).stage.action_code.function.1 acted)).2
  have meet := separates d₀ hd₀ x₀ hx₀ d' hd' x' hx' y hy wd' wx' dd xx acted
  have imageK := (run.actorPresentation.inclusion_entry j k _).2 ⟨hk, rfl⟩
  have imageW := (run.pointPresentation.inclusion_entry j w' _).2 ⟨hw', rfl⟩
  have identityAgreement :=
    ((run.diagram.stage j).stage.action_code.agreement_identity_iff_fixes).2 fixes
  have finalAgreement := run.limitMaps_agreement j k (run.diagram.stage j).stage.identity
    (run.actorPresentation.limitPoint j k) (run.limitIdentity j) w'
    (run.pointPresentation.limitPoint j w') imageK
    (run.limitActorMap_groupEmbedding j j).one imageW identityAgreement
  have finalFixes := ((run.limitAction_code j).agreement_identity_iff_fixes).1 finalAgreement
  rw [run.pointPresentation.limitPoint_transition before ww,
    run.pointPresentation.limitPoint_transition before dd,
    run.pointPresentation.limitPoint_transition before xx]
  refine ⟨run.actorPresentation.limitPoint j k, run.actorPresentation.limitPoint_mem hk,
    finalFixes, run.pointPresentation.limitPoint j y, run.pointPresentation.limitPoint_mem hy,
    (run.limitAction_at j hk hd' hy).2 acted, ?_⟩
  exact (run.limitMeetGraph_entry _ _ _).2 ((run.limitMeet_at j hy hx' hw').2 meet)

theorem limitPoints_separation_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {W d x : ZFSet.{u}} (hW : W ∈ run.limitPoints)
    (hd : d ∈ run.limitPoints) (hx : x ∈ run.limitPoints)
    (wd : ZFSet.pair W d ∈ run.limitOrder) (wx : ZFSet.pair W x ∈ run.limitOrder) :
    ∃ k ∈ run.limitActors,
      (∀ z ∈ run.limitPoints, ZFSet.pair z W ∈ run.limitOrder →
        ZFSet.pair (ZFSet.pair k z) z ∈ run.limitAction) ∧
      ∃ y ∈ run.limitPoints, ZFSet.pair (ZFSet.pair k d) y ∈ run.limitAction ∧
        ZFSet.pair (ZFSet.pair y x) W ∈ run.limitMeetGraph := by
  apply run.limitPoints_separation _ hW hd hx wd wx
  intro i
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, run.separation_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_strict_extension
    (growth : ∀ i, ∃ j, ∃ before : i ≤ j,
      StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
        (run.diagram.transition before).map.points (run.diagram.stage j).stage.top)
    {x : ZFSet.{u}} (member : x ∈ run.limitPoints) :
    ∃ y ∈ run.limitPoints, ZFSet.pair x y ∈ run.limitOrder ∧
      ZFSet.pair y x ∉ run.limitOrder := by
  obtain ⟨i, a, ha, rfl⟩ := run.pointPresentation.limitPoint_coverage member
  obtain ⟨j, before, strict⟩ := growth i
  obtain ⟨b, entry⟩ := run.pointSystem.map_entry_total before ha
  have hb := (run.pointSystem.map_entry_bounds before entry).2
  have ht := (run.diagram.stage j).stage.top_mem
  have bounds := strict a ha b hb entry
  refine ⟨run.pointPresentation.limitPoint j (run.diagram.stage j).stage.top,
    run.pointPresentation.limitPoint_mem ht, ?_⟩
  rw [run.pointPresentation.limitPoint_transition before entry]
  exact ⟨(run.limitOrder_entry _ _).2 ((run.limitLE_at j hb ht).2 bounds.1),
    fun lower => bounds.2 ((run.limitLE_at j ht hb).1 ((run.limitOrder_entry _ _).1 lower))⟩

theorem terminal_adjacent_strict_top
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code) (i : I) :
    ∃ j, ∃ before : i ≤ j, run.key j = insert (run.key i) (run.key i) ∧
      StrictSuccessorTopCode (run.diagram.stage i).stage.carrier
        (run.diagram.stage j).stage.carrier (run.diagram.stage j).stage.order
        (run.diagram.transition before).map.points (run.diagram.stage j).stage.top := by
  have member : run.key i ∈ M.groundOmegaOne pairing unions powers separation collection infinite :=
    domain ▸ ZFSet.mem_range.2 ⟨i, rfl⟩
  have next := M.groundOmegaOne_successor pairing unions powers separation collection infinite member
  obtain ⟨j, adjacent⟩ := ZFSet.mem_range.1 (domain.symm ▸ next)
  have before : i ≤ j := (run.key_order i j).2 (by
    rw [adjacent]
    exact Or.inr (ZFSet.mem_insert (run.key i) (run.key i)))
  exact ⟨j, before, adjacent, run.strict_top_of_taskBearing before
    (run.terminal_successor_taskBearing trace chosen tasks domain extension before adjacent)⟩

theorem limitPoints_strict_extension_of_trace
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B seed f g p : ZFSet.{u}}
    (trace : OrdinalRecursionTrace (MainPrefixTraceStepCode B seed g)
      (M.groundOmegaOne pairing unions powers separation collection infinite) p)
    (chosen : ∀ old next, ZFSet.pair old next ∈ g →
      MainPrefixConditionalStepCode M K Labels C D rD ZFSet.omega f old next)
    (tasks : ∀ source target z, ZFSet.pair source (ZFSet.pair target z) ∈ f →
      TaskBearingMainSuccessorCode M K Labels C D rD ZFSet.omega source target z)
    (domain : run.indices = M.groundOmegaOne pairing unions powers separation collection infinite)
    (extension : MainPrefixHistoryExtends p run.code)
    {x : ZFSet.{u}} (member : x ∈ run.limitPoints) :
    ∃ y ∈ run.limitPoints, ZFSet.pair x y ∈ run.limitOrder ∧
      ZFSet.pair y x ∉ run.limitOrder := by
  apply run.limitPoints_strict_extension _ member
  intro i
  obtain ⟨j, before, _, strict⟩ := run.terminal_adjacent_strict_top
    collection infinite trace chosen tasks domain extension i
  exact ⟨j, before, strict⟩

end PartitionPilot.Forcing.GroundMainPrefix

end OAI
