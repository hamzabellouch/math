import OAI.SetTheory.PartitionPrinciple.Geometry.GroundCompressionHeightSteps
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundFixedTopOrders
import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleFulfillmentAtBound
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundBatchBirths

namespace OAI

namespace PartitionPilot.Forcing

section

universe u

noncomputable def fixedTopAction (G P A : ZFSet.{u}) : ZFSet.{u} :=
  A ∪ ZFSet.sep (fun z => ∃ g ∈ G, z = ZFSet.pair (ZFSet.pair g P) P)
    (ZFSet.prod (ZFSet.prod G {P}) {P})

theorem pair_mem_fixedTopAction (G P A g p q : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g p) q ∈ fixedTopAction G P A ↔
      ZFSet.pair (ZFSet.pair g p) q ∈ A ∨ (g ∈ G ∧ p = P ∧ q = P) := by
  constructor
  · intro member
    rcases ZFSet.mem_union.1 member with old | fresh
    · exact Or.inl old
    · obtain ⟨h, hh, equal⟩ := (ZFSet.mem_sep.1 fresh).2
      obtain ⟨inner, rfl⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 inner
      exact Or.inr ⟨hh, rfl, rfl⟩
  · rintro (old | ⟨hg, rfl, rfl⟩)
    · exact ZFSet.mem_union.2 (Or.inl old)
    · exact ZFSet.mem_union.2 (Or.inr (ZFSet.mem_sep.2
        ⟨ZFSet.pair_mem_prod.2
          ⟨ZFSet.pair_mem_prod.2 ⟨hg, ZFSet.mem_singleton.2 rfl⟩, ZFSet.mem_singleton.2 rfl⟩,
          g, hg, rfl⟩))

theorem fixedTopAction_old_iff {G P A g p q : ZFSet.{u}} (hp : p ∈ P) :
    ZFSet.pair (ZFSet.pair g p) q ∈ fixedTopAction G P A ↔
      ZFSet.pair (ZFSet.pair g p) q ∈ A := by
  rw [pair_mem_fixedTopAction]
  exact ⟨fun h => h.elim id (fun h => False.elim (ZFSet.mem_irrefl P (h.2.1 ▸ hp))), Or.inl⟩

theorem fixedTopAction_at_top {G P A g q : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod G P) P A) :
    ZFSet.pair (ZFSet.pair g P) q ∈ fixedTopAction G P A ↔ g ∈ G ∧ q = P := by
  rw [pair_mem_fixedTopAction]
  constructor
  · rintro (old | ⟨hg, _, equal⟩)
    · exact False.elim (ZFSet.mem_irrefl P
        (ZFSet.pair_mem_prod.1 (ZFSet.pair_mem_prod.1 (function.1 old)).1).2)
    · exact ⟨hg, equal⟩
  · rintro ⟨hg, equal⟩
    exact Or.inr ⟨hg, rfl, equal⟩

theorem fixedTopAction_fixes_top {G P A g : ZFSet.{u}} (hg : g ∈ G) :
    ZFSet.pair (ZFSet.pair g P) P ∈ fixedTopAction G P A :=
  (pair_mem_fixedTopAction G P A g P P).2 (Or.inr ⟨hg, rfl, rfl⟩)

theorem fixedTopAction_function {G P A : ZFSet.{u}}
    (function : ZFSet.IsFunc (ZFSet.prod G P) P A) :
    ZFSet.IsFunc (ZFSet.prod G (fixedTopCarrier P)) (fixedTopCarrier P) (fixedTopAction G P A) := by
  refine ⟨?_, ?_⟩
  · intro z member
    rcases ZFSet.mem_union.1 member with old | fresh
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 old)
      obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hx
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
        ⟨hg, (mem_fixedTopCarrier P p).2 (Or.inr hp)⟩,
          (mem_fixedTopCarrier P y).2 (Or.inr hy)⟩
    · obtain ⟨g, hg, rfl⟩ := (ZFSet.mem_sep.1 fresh).2
      have top : P ∈ fixedTopCarrier P := (mem_fixedTopCarrier P P).2 (Or.inl rfl)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, top⟩, top⟩
  · intro x hx
    obtain ⟨g, hg, p, hp, rfl⟩ := ZFSet.mem_prod.1 hx
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · exact ⟨_, fixedTopAction_fixes_top hg,
        fun q entry => ((fixedTopAction_at_top function).1 entry).2⟩
    · obtain ⟨q, entry, unique⟩ := function.2 (ZFSet.pair g p) (ZFSet.pair_mem_prod.2 ⟨hg, old⟩)
      exact ⟨q, (fixedTopAction_old_iff old).2 entry,
        fun y hy => unique y ((fixedTopAction_old_iff old).1 hy)⟩

theorem PosetActionCode.fixedTop {G P m e r A : ZFSet.{u}}
    (action : PosetActionCode G P m e r A) (order : PartialOrderCode P r) (one_mem : e ∈ G) :
    PosetActionCode G (fixedTopCarrier P) m e (fixedTopOrder P r) (fixedTopAction G P A) := by
  refine ⟨fixedTopAction_function action.function, ?_, ?_, ?_⟩
  · intro p hp
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · exact fixedTopAction_fixes_top one_mem
    · exact (fixedTopAction_old_iff old).2 (action.one p old)
  · intro g hg h hh k hk p hp q _ s _ product first second
    rcases (mem_fixedTopCarrier P p).1 hp with rfl | old
    · have eqQ := ((fixedTopAction_at_top action.function).1 first).2
      subst q
      have eqS := ((fixedTopAction_at_top action.function).1 second).2
      subst s
      exact fixedTopAction_fixes_top hk
    · have firstOld := (fixedTopAction_old_iff old).1 first
      have qOld := (ZFSet.pair_mem_prod.1 (action.function.1 firstOld)).2
      have secondOld := (fixedTopAction_old_iff qOld).1 second
      have sOld := (ZFSet.pair_mem_prod.1 (action.function.1 secondOld)).2
      exact (fixedTopAction_old_iff old).2
        (action.mul g hg h hh k hk p old q qOld s sOld product firstOld secondOld)
  · intro g hg p _ q hq s hs v _ first second below
    rcases (mem_fixedTopCarrier P q).1 hq with rfl | qOld
    · have equal := ((fixedTopAction_at_top action.function).1 second).2
      subst v
      exact fixedTopOrder_greatest hs
    · have belowOld := (fixedTopOrder_old_iff qOld).1 below
      have pOld := (ZFSet.pair_mem_prod.1 (order.relation belowOld)).1
      have firstOld := (fixedTopAction_old_iff pOld).1 first
      have secondOld := (fixedTopAction_old_iff qOld).1 second
      have sOld := (ZFSet.pair_mem_prod.1 (action.function.1 firstOld)).2
      have vOld := (ZFSet.pair_mem_prod.1 (action.function.1 secondOld)).2
      exact ZFSet.mem_union.2 (Or.inl
        (action.monotone g hg p pOld q qOld s sOld v vOld firstOld secondOld belowOld))

namespace BoundedFormula

open SetFormula

def fixedTopActionEntryFormula {n} (z G P : Fin n) : BoundedFormula n :=
  exMem G (orderedTripleFormula z.succ 0 P.succ P.succ)

theorem truth_fixedTopActionEntryFormula {n} (z G P : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (fixedTopActionEntryFormula z G P) env ↔
      ∃ g ∈ env G, env z = ZFSet.pair (ZFSet.pair g (env P)) (env P) := by
  simp only [fixedTopActionEntryFormula, truth_exMem, truth_orderedTripleFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem fixedTopAction_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G P A : ZFSet.{u}} (hG : G ∈ M.sets) (hP : P ∈ M.sets) (hA : A ∈ M.sets) :
    fixedTopAction G P A ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  let params := extend G (extend P Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.fixedTopActionEntryFormula 0 1 2) params
    (Fin.cases hG (Fin.cases hP (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hG singleton) singleton)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.fixedTopActionEntryFormula 0 1 2) (extend z params))
      (ZFSet.prod (ZFSet.prod G {P}) {P}) =
      ZFSet.sep (fun z => ∃ g ∈ G, z = ZFSet.pair (ZFSet.pair g P) P)
        (ZFSet.prod (ZFSet.prod G {P}) {P}) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_fixedTopActionEntryFormula 0 1 2 _)
  exact M.binary_union_mem pairing unions hA (equal ▸ selected)

end TransitiveGround

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem exists_fixedTopExtension
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {P r μ G m e A D rD old : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets)
    (meet : MeetOrderCode P r μ) (action : PosetActionCode G P m e r A)
    (one_mem : e ∈ G) (nonempty : D.Nonempty)
    (height : StrictLexHeightCode P
      (M.groundOmegaOne pairing unions powers separation collection infinite) D r old rD)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod
      (M.groundOmegaOne pairing unions powers separation collection infinite) D) old) ZFSet.omega) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ b ∈ C, ∃ q ∈ D,
      fixedTopCarrier P ∈ M.sets ∧ fixedTopOrder P r ∈ M.sets ∧ fixedTopMeet P r ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧ fixedTopAction G P A ∈ M.sets ∧
      fixedTopHeightGraph P old b q ∈ M.sets ∧
      MeetOrderCode (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) ∧
      MeetEmbeddingCode P (fixedTopCarrier P) r (fixedTopOrder P r) μ (fixedTopMeet P r)
        (attachmentOldEmbeddingGraph P) ∧
      PosetActionCode G (fixedTopCarrier P) m e (fixedTopOrder P r) (fixedTopAction G P A) ∧
      StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r)
        (fixedTopHeightGraph P old b q) rD ∧
      (∀ x ∈ fixedTopCarrier P, ZFSet.pair x P ∈ fixedTopOrder P r) ∧
      (∀ x ∈ P, ZFSet.pair P x ∉ fixedTopOrder P r) ∧
      (∀ x y, y ∈ P → (ZFSet.pair x y ∈ fixedTopOrder P r ↔ ZFSet.pair x y ∈ r)) ∧
      (∀ x y, y ∈ P → ZFSet.pair x y ∈ fixedTopOrder P r → x ∈ P) ∧
      (∀ g ∈ G, ZFSet.pair (ZFSet.pair g P) P ∈ fixedTopAction G P A) ∧
      (∀ g x y, x ∈ P → (ZFSet.pair (ZFSet.pair g x) y ∈ fixedTopAction G P A ↔
        ZFSet.pair (ZFSet.pair g x) y ∈ A)) ∧
      (∀ x ∈ P, ∀ y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔ ZFSet.pair x y ∈ old) ∧
      (∀ c ∈ heightColumns P C D old, c ∈ b) ∧ b ∉ heightColumns P C D old ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) =
        insert (ZFSet.pair b q) (relationImage P (ZFSet.prod C D) old) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) ∈ M.sets ∧
      M.groundEmbeddable
        (relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q)) ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ old →
        ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) ∧
      (∀ x y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q →
        y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) := by
  obtain ⟨b, hb, q, hq, newHeight, hNewHeight, equal, above, fresh, strict,
    oldEntries, _, rangeEq, hRange, smallRange, oldBound, bound⟩ :=
    M.exists_fixedTopHeight pairing unions powers separation collection infinite choice
      hP hD hOld meet.order nonempty height small
  subst newHeight
  obtain ⟨hL, hR, hMeet, hEmbedding⟩ := M.fixedTop_ground_codes pairing unions powers separation hP hr
  exact ⟨b, hb, q, hq, hL, hR, hMeet, hEmbedding,
    M.fixedTopAction_mem pairing unions powers separation hG hP hA, hNewHeight,
    fixedTopMeet_code meet, fixedTopOldEmbedding_code meet, action.fixedTop meet.order one_mem,
    strict, fun _ hx => fixedTopOrder_greatest hx,
    fun _ hx => (fixedTopOrder_strict_top meet.order hx).2,
    fun _ _ hy => fixedTopOrder_old_iff hy,
    fun _ _ hy entry => fixedTopOrder_no_new_below meet.order hy entry,
    fun _ hg => fixedTopAction_fixes_top hg, fun _ _ _ hx => fixedTopAction_old_iff hx,
    oldEntries, above, fresh, rangeEq, hRange, smallRange, oldBound, bound⟩

theorem exists_fixedTopStep
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Space sourceOrder sourceMeet : ZFSet.{u} → ZFSet.{u}}
    {P r μ G m e A D rD old T birth s : ZFSet.{u}}
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets)
    (hD : D ∈ M.sets) (hOld : old ∈ M.sets) (hT : T ∈ M.sets) (hBirth : birth ∈ M.sets)
    (meet : MeetOrderCode P r μ) (action : PosetActionCode G P m e r A)
    (one_mem : e ∈ G) (nonempty : D.Nonempty)
    (height : StrictLexHeightCode P
      (M.groundOmegaOne pairing unions powers separation collection infinite) D r old rD)
    (small : M.groundEmbeddable (relationImage P (ZFSet.prod
      (M.groundOmegaOne pairing unions powers separation collection infinite) D) old) ZFSet.omega)
    (born : ZFSet.IsFunc P T birth) (hs : s ∈ T)
    (earlier : ∀ x t, ZFSet.pair x t ∈ birth → t ∈ s)
    (oldMeet : OldMeetCode r μ birth)
    (layers : ∀ t ∈ s, CodedGrowthLayer M Space sourceOrder sourceMeet P r μ birth t) :
    let C := M.groundOmegaOne pairing unions powers separation collection infinite
    ∃ b ∈ C, ∃ q ∈ D,
      fixedTopCarrier P ∈ M.sets ∧ fixedTopOrder P r ∈ M.sets ∧ fixedTopMeet P r ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧ fixedTopAction G P A ∈ M.sets ∧
      fixedTopBirth P birth s ∈ M.sets ∧ fixedTopHeightGraph P old b q ∈ M.sets ∧
      MeetOrderCode (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) ∧
      MeetEmbeddingCode P (fixedTopCarrier P) r (fixedTopOrder P r) μ (fixedTopMeet P r)
        (attachmentOldEmbeddingGraph P) ∧
      PosetActionCode G (fixedTopCarrier P) m e (fixedTopOrder P r) (fixedTopAction G P A) ∧
      ZFSet.IsFunc (fixedTopCarrier P) T (fixedTopBirth P birth s) ∧
      (∀ x t, ZFSet.pair x t ∈ fixedTopBirth P birth s → t = s ∨ t ∈ s) ∧
      OldMeetCode (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) ∧
      (∀ t, t = s ∨ t ∈ s → Nonempty (CodedGrowthLayer M Space sourceOrder sourceMeet
        (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopMeet P r) (fixedTopBirth P birth s) t)) ∧
      StrictLexHeightCode (fixedTopCarrier P) C D (fixedTopOrder P r)
        (fixedTopHeightGraph P old b q) rD ∧
      (∀ x ∈ P, ∀ y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q ↔ ZFSet.pair x y ∈ old) ∧
      (∀ x ∈ P, ∀ t, ZFSet.pair x t ∈ fixedTopBirth P birth s ↔ ZFSet.pair x t ∈ birth) ∧
      (∀ x ∈ fixedTopCarrier P, ZFSet.pair x P ∈ fixedTopOrder P r) ∧
      (∀ x ∈ P, ZFSet.pair P x ∉ fixedTopOrder P r) ∧
      (∀ g ∈ G, ZFSet.pair (ZFSet.pair g P) P ∈ fixedTopAction G P A) ∧
      relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q) ∈ M.sets ∧
      M.groundEmbeddable
        (relationImage (fixedTopCarrier P) (ZFSet.prod C D) (fixedTopHeightGraph P old b q)) ZFSet.omega ∧
      (∀ x y, ZFSet.pair x y ∈ fixedTopHeightGraph P old b q →
        y = ZFSet.pair b q ∨ ZFSet.pair y (ZFSet.pair b q) ∈ lexHeightOrder C D rD) := by
  obtain ⟨b, hb, q, hq, hL, hR, hMeet, hEmbedding, hAction, hHeight,
    newMeet, embedding, newAction, newHeight, greatest, strictTop, _, _, fixes,
    _, oldHeights, _, _, _, hRange, smallRange, _, bound⟩ :=
    M.exists_fixedTopExtension pairing unions powers separation collection infinite choice
      hP hr hG hA hD hOld meet action one_mem nonempty height small
  exact ⟨b, hb, q, hq, hL, hR, hMeet, hEmbedding, hAction,
    M.fixedTopBirth_mem pairing unions hP hBirth (M.transitive hT hs), hHeight,
    newMeet, embedding, newAction, fixedTopBirth_function born hs,
    fixedTopBirth_bound earlier, fixedTopBirth_oldMeet meet born earlier oldMeet,
    fun t ht => ⟨M.fixedTopBirth_layers pairing separation hP meet born earlier layers t ht⟩,
    newHeight, oldHeights, fun _ hx _ => fixedTopBirth_old_iff hx,
    greatest, strictTop, fixes, hRange, smallRange, bound⟩

end TransitiveGround

section
universe u

namespace IdealEmbeddingCode
variable {P Q rP rQ μP μQ e : ZFSet.{u}}
variable (code : IdealEmbeddingCode P Q rP rQ μP μQ e)
include code

theorem preserves_bottom (target : MeetOrderCode Q rQ μQ) {b b' : ZFSet.{u}}
    (least : ∀ x ∈ P, ZFSet.pair b x ∈ rP) (image : ZFSet.pair b b' ∈ e) :
    ∀ y ∈ Q, ZFSet.pair b' y ∈ rQ := by
  intro y hy
  have hb' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2
  obtain ⟨z, meet, _⟩ := target.operation.2 (ZFSet.pair b' y) (ZFSet.pair_mem_prod.2 ⟨hb', hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 (target.operation.1 meet)).2
  obtain ⟨x, hx, _, xx'⟩ := code.ideal b b' z image hz (target.lower_left b' y z meet)
  exact target.order.trans b' hb' z hz y hy
    (code.monotone b x b' z (least x hx) image xx') (target.lower_right b' y z meet)

theorem fixedTop (target : MeetOrderCode Q rQ μQ) :
    IdealEmbeddingCode P (fixedTopCarrier Q) rP (fixedTopOrder Q rQ) μP (fixedTopMeet Q rQ) e := by
  refine ⟨⟨⟨⟨?_, code.injection.function.2⟩, code.injection.injective⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro z entry
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.injection.function.1 entry)
    exact ZFSet.pair_mem_prod.2 ⟨hx, fixedTopCarrier_old hy⟩
  · intro x y x' y' lower first second
    exact fixedTopOrder_subset Q rQ (code.monotone x y x' y' lower first second)
  · intro x y z x' y' z' meet first second third
    exact fixedTopMeet_subset target (code.map_meet x y z x' y' z' meet first second third)
  · intro x y x' y' first second lower
    have hy' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 second)).2
    exact code.reflect x y x' y' first second ((fixedTopOrder_old_iff hy').1 lower)
  · intro v v' z image _ lower
    have hv' := (ZFSet.pair_mem_prod.1 (code.injection.function.1 image)).2
    exact code.ideal v v' z image (fixedTopOrder_no_new_below target.order hv' lower)
      ((fixedTopOrder_old_iff hv').1 lower)

end IdealEmbeddingCode

namespace ActionAgreementBelow
variable {G P m one r A g h v : ZFSet.{u}}
variable (agree : ActionAgreementBelow P r A g h v)
include agree

theorem fixedTop (order : PartialOrderCode P r) (action : PosetActionCode G P m one r A)
    (hv : v ∈ P) :
    ActionAgreementBelow (fixedTopCarrier P) (fixedTopOrder P r) (fixedTopAction G P A) g h v := by
  intro x _ y _ lower
  have hx := fixedTopOrder_no_new_below order hv lower
  rw [fixedTopAction_old_iff hx, fixedTopAction_old_iff hx]
  by_cases hy : y ∈ P
  · exact agree x hx y hy ((fixedTopOrder_old_iff hv).1 lower)
  · exact ⟨fun entry => False.elim (hy (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2),
      fun entry => False.elim (hy (ZFSet.pair_mem_prod.1 (action.function.1 entry)).2)⟩

end ActionAgreementBelow

end

open SetRealization
universe u

namespace ActionAgreementBelow
variable {Q H R ν B g h v : ZFSet.{u}}

theorem fixedTop_rectangleAgreement (meet : MeetOrderCode Q R ν) (function : ZFSet.IsFunc (ZFSet.prod H Q) Q B) (hv : v ∈ Q)
    (agreement : ActionAgreementBelow Q R B g h v) :
    ActionAgreementBelow (fixedTopCarrier Q) (fixedTopOrder Q R) (fixedTopAction H Q B) g h v := by
  intro x _ y _ lower
  have hx := fixedTopOrder_no_new_below meet.order hv lower
  rw [fixedTopAction_old_iff hx, fixedTopAction_old_iff hx]
  by_cases hy : y ∈ Q
  · exact agreement x hx y hy ((fixedTopOrder_old_iff hv).1 lower)
  · exact ⟨fun entry => (hy (ZFSet.pair_mem_prod.1 (function.1 entry)).2).elim,
      fun entry => (hy (ZFSet.pair_mem_prod.1 (function.1 entry)).2).elim⟩

end ActionAgreementBelow

namespace RectangleActorPairCode
variable {P μ A Q H R ν B e a c b d g h k l : ZFSet.{u}}

theorem fixedTop (code : RectangleActorPairCode P μ A Q H R ν B e a c b d g h k l)
    (meet : MeetOrderCode Q R ν) (function : ZFSet.IsFunc (ZFSet.prod H Q) Q B)
    (images : ∀ x y, ZFSet.pair x y ∈ e → y ∈ Q) :
    RectangleActorPairCode P μ A (fixedTopCarrier Q) H (fixedTopOrder Q R)
      (fixedTopMeet Q R) (fixedTopAction H Q B) e a c b d g h k l := by
  have root {g k} (old : RectangleRootMeetCode P μ A Q ν B e c d g k) :
      RectangleRootMeetCode P μ A (fixedTopCarrier Q) (fixedTopMeet Q R)
        (fixedTopAction H Q B) e c d g k := by
    intro x hx v hv w hw d' _ x' _ w' _ y _ acted met ed ex ew entry
    have hd' := images _ _ ed
    have hx' := images _ _ ex
    have hw' := images _ _ ew
    have entry := (fixedTopAction_old_iff hd').1 entry
    have hy := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    exact (fixedTopMeet_old_iff meet hy hx').2
      (old x hx v hv w hw d' hd' x' hx' w' hw' y hy acted met ed ex ew entry)
  refine ⟨⟨?_, ?_⟩, root code.2.1, root code.2.2.1, ?_⟩
  · intro c' _ g' hg' h' hh' ec ag ah
    have hc' := images _ _ ec
    have agrees := code.1.1 c' hc' g' hg' h' hh' ec ag ah
    exact ⟨ActionAgreementBelow.fixedTop_rectangleAgreement meet function hc' agrees.1,
      ActionAgreementBelow.fixedTop_rectangleAgreement meet function hc' agrees.2⟩
  · intro b' _ eb
    have hb' := images _ _ eb
    exact ActionAgreementBelow.fixedTop_rectangleAgreement meet function hb' (code.1.2 b' hb' eb)
  · intro b' _ d' _ y _ v _ z _ eb ed act1 act2 actB
    have hb' := images _ _ eb
    have hd' := images _ _ ed
    have act1 := (fixedTopAction_old_iff hd').1 act1
    have act2 := (fixedTopAction_old_iff hd').1 act2
    have actB := (fixedTopAction_old_iff hb').1 actB
    have hy := (ZFSet.pair_mem_prod.1 (function.1 act1)).2
    have hv := (ZFSet.pair_mem_prod.1 (function.1 act2)).2
    have hz := (ZFSet.pair_mem_prod.1 (function.1 actB)).2
    have cross := code.2.2.2 b' hb' d' hd' y hy v hv z hz eb ed act1 act2 actB
    exact ⟨(fixedTopMeet_old_iff meet hy hv).2 cross.1,
      (fixedTopAction_old_iff hb').2 cross.2⟩

end RectangleActorPairCode

end PartitionPilot.Forcing

end OAI
