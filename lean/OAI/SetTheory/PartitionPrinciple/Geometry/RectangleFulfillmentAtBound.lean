import OAI.SetTheory.PartitionPrinciple.Definability.GroundMainTransitionCodes

namespace OAI


namespace PartitionPilot.Forcing
universe u

noncomputable def externalRectangleCode (c b d g h : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.pair c (ZFSet.pair b (ZFSet.pair d (ZFSet.pair g h)))

noncomputable def externalRectangleBound (P G : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod P (ZFSet.prod P (ZFSet.prod P (ZFSet.prod G G)))

def ExternalRectangleCode (P G r μ A c b d g h : ZFSet.{u}) : Prop :=
  c ∈ P ∧ b ∈ P ∧ d ∈ P ∧ g ∈ G ∧ h ∈ G ∧
    ZFSet.pair c d ∈ r ∧ ZFSet.pair b d ∈ r ∧
    ∃ w ∈ P, ZFSet.pair (ZFSet.pair c b) w ∈ μ ∧ ActionAgreementBelow P r A g h w ∧
      ∀ y ∈ P, ∀ z ∈ P, ∀ v ∈ P,
        (ZFSet.pair (ZFSet.pair g d) y ∈ A ∧ ZFSet.pair (ZFSet.pair h d) z ∈ A ∧
          ZFSet.pair (ZFSet.pair g w) v ∈ A) → ZFSet.pair (ZFSet.pair y z) v ∈ μ

noncomputable def externalRectangles (P G r μ A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun t => ∃ c ∈ P, ∃ b ∈ P, ∃ d ∈ P, ∃ g ∈ G, ∃ h ∈ G,
    t = externalRectangleCode c b d g h ∧ ExternalRectangleCode P G r μ A c b d g h)
    (externalRectangleBound P G)

theorem externalRectangleCode_inj {c b d g h c' b' d' g' h' : ZFSet.{u}} :
    externalRectangleCode c b d g h = externalRectangleCode c' b' d' g' h' ↔
      c = c' ∧ b = b' ∧ d = d' ∧ g = g' ∧ h = h' := by
  simp only [externalRectangleCode, ZFSet.pair_inj]

theorem externalRectangleCode_mem_bound (P G c b d g h : ZFSet.{u}) :
    externalRectangleCode c b d g h ∈ externalRectangleBound P G ↔
      c ∈ P ∧ b ∈ P ∧ d ∈ P ∧ g ∈ G ∧ h ∈ G := by
  simp only [externalRectangleCode, externalRectangleBound, ZFSet.pair_mem_prod]

theorem mem_externalRectangles (P G r μ A t : ZFSet.{u}) :
    t ∈ externalRectangles P G r μ A ↔ ∃ c b d g h,
      t = externalRectangleCode c b d g h ∧ ExternalRectangleCode P G r μ A c b d g h := by
  rw [externalRectangles, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, c, _, b, _, d, _, g, _, h, _, eq, code⟩
    exact ⟨c, b, d, g, h, eq, code⟩
  · rintro ⟨c, b, d, g, h, rfl, code⟩
    exact ⟨(externalRectangleCode_mem_bound P G c b d g h).2
      ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1, code.2.2.2.2.1⟩,
      c, code.1, b, code.2.1, d, code.2.2.1, g, code.2.2.2.1, h, code.2.2.2.2.1, rfl, code⟩

theorem externalRectangleCode_mem (P G r μ A c b d g h : ZFSet.{u}) :
    externalRectangleCode c b d g h ∈ externalRectangles P G r μ A ↔
      ExternalRectangleCode P G r μ A c b d g h := by
  rw [mem_externalRectangles]
  constructor
  · rintro ⟨c', b', d', g', h', equal, code⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := externalRectangleCode_inj.1 equal
    exact code
  · intro code
    exact ⟨c, b, d, g, h, rfl, code⟩

namespace BoundedFormula
open SetFormula

def actionAgreementBelowFormula {n} (P r A g h w : Fin n) : BoundedFormula n :=
  .allMem P (.allMem P.succ (imp (pairMembershipFormula 1 w.succ.succ r.succ.succ)
    (.conj (imp (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)
      (tripleMembershipFormula h.succ.succ 1 0 A.succ.succ))
      (imp (tripleMembershipFormula h.succ.succ 1 0 A.succ.succ)
        (tripleMembershipFormula g.succ.succ 1 0 A.succ.succ)))))

theorem truth_actionAgreementBelowFormula {n} (P r A g h w : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (actionAgreementBelowFormula P r A g h w) env ↔
      ActionAgreementBelow (env P) (env r) (env A) (env g) (env h) (env w) := by
  simp only [actionAgreementBelowFormula, ActionAgreementBelow, Truth, truth_imp, iff_def,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  constructor <;> exact fun h => h

def rectangleSeparatedFormula {n} (P μ A d w g h : Fin n) : BoundedFormula n :=
  .allMem P (.allMem P.succ (.allMem P.succ.succ
    (imp (.conj (tripleMembershipFormula g.succ.succ.succ d.succ.succ.succ 2 A.succ.succ.succ)
      (.conj (tripleMembershipFormula h.succ.succ.succ d.succ.succ.succ 1 A.succ.succ.succ)
        (tripleMembershipFormula g.succ.succ.succ w.succ.succ.succ 0 A.succ.succ.succ)))
      (tripleMembershipFormula 2 1 0 μ.succ.succ.succ))))

def externalRectangleFormula {n} (P G r μ A c b d g h : Fin n) : BoundedFormula n :=
  .conj (.mem c P) (.conj (.mem b P) (.conj (.mem d P) (.conj (.mem g G) (.conj (.mem h G)
    (.conj (pairMembershipFormula c d r) (.conj (pairMembershipFormula b d r)
      (exMem P (.conj (tripleMembershipFormula c.succ b.succ 0 μ.succ)
        (.conj (actionAgreementBelowFormula P.succ r.succ A.succ g.succ h.succ 0)
          (rectangleSeparatedFormula P.succ μ.succ A.succ d.succ 0 g.succ h.succ))))))))))

theorem truth_externalRectangleFormula {n} (P G r μ A c b d g h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectangleFormula P G r μ A c b d g h) env ↔
      ExternalRectangleCode (env P) (env G) (env r) (env μ) (env A)
        (env c) (env b) (env d) (env g) (env h) := by
  simp only [externalRectangleFormula, ExternalRectangleCode, rectangleSeparatedFormula,
    Truth, truth_exMem, truth_imp, truth_actionAgreementBelowFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def externalRectangleTupleFormula {n} (t c b d g h : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 4 t
    (Fin.cases c (Fin.cases b (Fin.cases d (Fin.cases g (Fin.cases h Fin.elim0)))))

theorem truth_externalRectangleTupleFormula {n} (t c b d g h : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectangleTupleFormula t c b d g h) env ↔
      env t = externalRectangleCode (env c) (env b) (env d) (env g) (env h) := by
  rw [externalRectangleTupleFormula, truth_nonemptyTupleFormula]
  rfl

def externalRectanglesEntryFormula {n} (t P G r μ A : Fin n) : BoundedFormula n :=
  exMem P (exMem P.succ (exMem P.succ.succ (exMem G.succ.succ.succ
    (exMem G.succ.succ.succ.succ
      (.conj (externalRectangleTupleFormula t.succ.succ.succ.succ.succ 4 3 2 1 0)
        (externalRectangleFormula P.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ
          r.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ
          4 3 2 1 0))))))

theorem truth_externalRectanglesEntryFormula {n} (t P G r μ A : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalRectanglesEntryFormula t P G r μ A) env ↔
      ∃ c ∈ env P, ∃ b ∈ env P, ∃ d ∈ env P, ∃ g ∈ env G, ∃ h ∈ env G,
        env t = externalRectangleCode c b d g h ∧
          ExternalRectangleCode (env P) (env G) (env r) (env μ) (env A) c b d g h := by
  simp only [externalRectanglesEntryFormula, truth_exMem, Truth,
    truth_externalRectangleTupleFormula, truth_externalRectangleFormula]
  rfl

end BoundedFormula





def CompressionActorCode
    (P G Q H R B e a Sources Reps top Caps i k : ZFSet.{u}) : Prop :=
  (∀ s ∈ P, ∀ g ∈ G, ∀ g' ∈ H, ∀ s' ∈ Q,
    ZFSet.pair i s ∈ Sources → ZFSet.pair i g ∈ Reps →
      ZFSet.pair g g' ∈ a → ZFSet.pair s s' ∈ e →
        ActionAgreementBelow Q R B k g' s') ∧
  ∀ top' ∈ Q, ∀ v ∈ Q, ZFSet.pair top top' ∈ e →
    (ZFSet.pair (ZFSet.pair k top') v ∈ B ↔ ZFSet.pair i v ∈ Caps)

def CompressionActorFulfillmentCode
    (I P G Q H R B e a Sources Reps top Caps : ZFSet.{u}) : Prop :=
  ∀ i ∈ I, ∃ k ∈ H, CompressionActorCode P G Q H R B e a Sources Reps top Caps i k

namespace BoundedFormula

def compressionActorFormula {n}
    (P G Q H R B e a Sources Reps top Caps i k : Fin n) : BoundedFormula n :=
  let lift (j : Fin n) := j.succ.succ.succ.succ
  .conj
    (.allMem P (.allMem G.succ (.allMem H.succ.succ (.allMem Q.succ.succ.succ
      (imp (pairMembershipFormula (lift i) 3 (lift Sources))
        (imp (pairMembershipFormula (lift i) 2 (lift Reps))
          (imp (pairMembershipFormula 2 1 (lift a))
            (imp (pairMembershipFormula 3 0 (lift e))
              (actionAgreementBelowFormula (lift Q) (lift R) (lift B) (lift k) 1 0)))))))))
    (.allMem Q (.allMem Q.succ
      (imp (pairMembershipFormula top.succ.succ 1 e.succ.succ)
        (.conj
          (imp (tripleMembershipFormula k.succ.succ 1 0 B.succ.succ)
            (pairMembershipFormula i.succ.succ 0 Caps.succ.succ))
          (imp (pairMembershipFormula i.succ.succ 0 Caps.succ.succ)
            (tripleMembershipFormula k.succ.succ 1 0 B.succ.succ))))))

theorem truth_compressionActorFormula {n}
    (P G Q H R B e a Sources Reps top Caps i k : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorFormula P G Q H R B e a Sources Reps top Caps i k) env ↔
      CompressionActorCode (env P) (env G) (env Q) (env H) (env R) (env B)
        (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) (env i) (env k) := by
  simp only [compressionActorFormula, CompressionActorCode, Truth, truth_imp,
    truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_actionAgreementBelowFormula, iff_def]
  constructor <;> exact fun h => h

def compressionActorFulfillmentFormula {n}
    (I P G Q H R B e a Sources Reps top Caps : Fin n) : BoundedFormula n :=
  .allMem I (.exMem H.succ
    (compressionActorFormula P.succ.succ G.succ.succ Q.succ.succ H.succ.succ
      R.succ.succ B.succ.succ e.succ.succ a.succ.succ Sources.succ.succ
      Reps.succ.succ top.succ.succ Caps.succ.succ 1 0))

theorem truth_compressionActorFulfillmentFormula {n}
    (I P G Q H R B e a Sources Reps top Caps : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (compressionActorFulfillmentFormula I P G Q H R B e a Sources Reps top Caps) env ↔
      CompressionActorFulfillmentCode (env I) (env P) (env G) (env Q) (env H) (env R)
        (env B) (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) := by
  simp only [compressionActorFulfillmentFormula, Truth, truth_exMem, truth_compressionActorFormula]
  rfl

theorem realize_compressionActorFulfillmentFormula (M : TransitiveGround.{u}) {n}
    (I P G Q H R B e a Sources Reps top Caps : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) :
    SetFormula.Realize M.sets
      (compressionActorFulfillmentFormula I P G Q H R B e a Sources Reps top Caps).toFormula env ↔
      CompressionActorFulfillmentCode (env I) (env P) (env G) (env Q) (env H) (env R)
        (env B) (env e) (env a) (env Sources) (env Reps) (env top) (env Caps) :=
  (realize_toFormula M _ env members).trans
    (truth_compressionActorFulfillmentFormula I P G Q H R B e a Sources Reps top Caps env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {P G r μ A m inv one c b d g h : ZFSet.{u}}
variable (group : GroupCode G m inv one) (action : PosetActionCode G P m one r A)
variable (meet : MeetOrderCode P r μ)

noncomputable def ExternalRectangleCode.toActionRectangle
    (code : ExternalRectangleCode P G r μ A c b d g h) :
    Compression.RecursiveMaps.ActionRectangle meet.toMeetOrder (action.toMeetIso group meet) := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  let w := Classical.choose witness
  have mw := (Classical.choose_spec witness).2.1
  have agree := (Classical.choose_spec witness).2.2.1
  have separated := (Classical.choose_spec witness).2.2.2
  let C := (⟨c, hc⟩ : {x : ZFSet.{u} // x ∈ P})
  let B := (⟨b, hb⟩ : {x : ZFSet.{u} // x ∈ P})
  let D := (⟨d, hd⟩ : {x : ZFSet.{u} // x ∈ P})
  let first := (⟨g, hg⟩ : {x : ZFSet.{u} // x ∈ G})
  let second := (⟨h, hh⟩ : {x : ZFSet.{u} // x ∈ G})
  have meetValue : (meet.toMeetOrder.meet C B).val = w :=
    (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.toMeetOrder_meet_entry C B) mw
  refine {
    C := C
    B := B
    D := D
    first := first
    second := second
    C_le_D := cd
    B_le_D := bd
    agree := ?_
    separated := ?_ }
  · intro x lower
    apply Subtype.ext
    have lowerW : ZFSet.pair x.val w ∈ r := meetValue ▸ lower
    exact agree.entry_eq action hh x.property lowerW
      (action.toMeetIso_entry group meet first x)
      (action.toMeetIso_entry group meet second x)
  · apply Subtype.ext
    let y := (action.toMeetIso group meet first).toFun D
    let z := (action.toMeetIso group meet second).toFun D
    let v := (action.toMeetIso group meet first).toFun (meet.toMeetOrder.meet C B)
    have actMeet : ZFSet.pair (ZFSet.pair g w) v.val ∈ A := by
      rw [← meetValue]
      exact action.toMeetIso_entry group meet first (meet.toMeetOrder.meet C B)
    have value := separated y.val y.property z.val z.property v.val v.property
      ⟨action.toMeetIso_entry group meet first D, action.toMeetIso_entry group meet second D, actMeet⟩
    exact (show FunctionGraphOn (ZFSet.prod P P) μ from ⟨P, meet.operation⟩).unique
      (meet.toMeetOrder_meet_entry y z) value

theorem ExternalRectangleCode.toActionRectangle_fields
    (code : ExternalRectangleCode P G r μ A c b d g h) :
    let request := code.toActionRectangle group action meet
    request.C.val = c ∧ request.B.val = b ∧ request.D.val = d ∧
      request.first.val = g ∧ request.second.val = h := by
  obtain ⟨hc, hb, hd, hg, hh, cd, bd, witness⟩ := code
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem externalRectangleCode_of_actionRectangle
    (request : Compression.RecursiveMaps.ActionRectangle meet.toMeetOrder (action.toMeetIso group meet)) :
    ExternalRectangleCode P G r μ A request.C.val request.B.val request.D.val
      request.first.val request.second.val := by
  refine ⟨request.C.property, request.B.property, request.D.property,
    request.first.property, request.second.property, request.C_le_D, request.B_le_D,
    (meet.toMeetOrder.meet request.C request.B).val,
    (meet.toMeetOrder.meet request.C request.B).property,
    meet.toMeetOrder_meet_entry request.C request.B, ?_, ?_⟩
  · intro x hx y hy lower
    have same := request.agree ⟨x, hx⟩ lower
    rw [← action.toMeetIso_eq_iff group meet request.first ⟨x, hx⟩ ⟨y, hy⟩,
      ← action.toMeetIso_eq_iff group meet request.second ⟨x, hx⟩ ⟨y, hy⟩]
    exact ⟨fun entry => same.symm.trans entry, fun entry => same.trans entry⟩
  · intro y hy z hz v hv entries
    have first := (action.toMeetIso_eq_iff group meet request.first request.D ⟨y, hy⟩).2 entries.1
    have second := (action.toMeetIso_eq_iff group meet request.second request.D ⟨z, hz⟩).2 entries.2.1
    have meetImage := (action.toMeetIso_eq_iff group meet request.first
      (meet.toMeetOrder.meet request.C request.B) ⟨v, hv⟩).2 entries.2.2
    have same : meet.toMeetOrder.meet ⟨y, hy⟩ ⟨z, hz⟩ = ⟨v, hv⟩ := by
      rw [← first, ← second, request.separated]
      exact meetImage
    have entry := meet.toMeetOrder_meet_entry ⟨y, hy⟩ ⟨z, hz⟩
    rw [same] at entry
    exact entry

theorem actionRectangle_mem_externalRectangles
    (request : Compression.RecursiveMaps.ActionRectangle meet.toMeetOrder (action.toMeetIso group meet)) :
    externalRectangleCode request.C.val request.B.val request.D.val request.first.val request.second.val ∈
      externalRectangles P G r μ A :=
  (externalRectangleCode_mem _ _ _ _ _ _ _ _ _ _).2
    (externalRectangleCode_of_actionRectangle group action meet request)

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

def RectangleIdealCode (Q H R B e a c b g h k l : ZFSet.{u}) : Prop :=
  (∀ c' ∈ Q, ∀ g' ∈ H, ∀ h' ∈ H,
    ZFSet.pair c c' ∈ e → ZFSet.pair g g' ∈ a → ZFSet.pair h h' ∈ a →
      ActionAgreementBelow Q R B k g' c' ∧ ActionAgreementBelow Q R B l h' c') ∧
  ∀ b' ∈ Q, ZFSet.pair b b' ∈ e → ActionAgreementBelow Q R B k l b'

def RectangleRootMeetCode (P μ A Q ν B e c d g k : ZFSet.{u}) : Prop :=
  ∀ x ∈ P, ∀ v ∈ P, ∀ w ∈ P, ∀ d' ∈ Q, ∀ x' ∈ Q, ∀ w' ∈ Q, ∀ y ∈ Q,
    ZFSet.pair (ZFSet.pair g c) v ∈ A → ZFSet.pair (ZFSet.pair v x) w ∈ μ →
    ZFSet.pair d d' ∈ e → ZFSet.pair x x' ∈ e → ZFSet.pair w w' ∈ e →
    ZFSet.pair (ZFSet.pair k d') y ∈ B → ZFSet.pair (ZFSet.pair y x') w' ∈ ν

def RectangleCrossMeetCode (Q ν B e b d k l : ZFSet.{u}) : Prop :=
  ∀ b' ∈ Q, ∀ d' ∈ Q, ∀ y ∈ Q, ∀ v ∈ Q, ∀ z ∈ Q,
    ZFSet.pair b b' ∈ e → ZFSet.pair d d' ∈ e →
    ZFSet.pair (ZFSet.pair k d') y ∈ B → ZFSet.pair (ZFSet.pair l d') v ∈ B →
    ZFSet.pair (ZFSet.pair k b') z ∈ B →
      ZFSet.pair (ZFSet.pair y v) z ∈ ν ∧ ZFSet.pair (ZFSet.pair l b') z ∈ B

def RectangleActorPairCode (P μ A Q H R ν B e a c b d g h k l : ZFSet.{u}) : Prop :=
  RectangleIdealCode Q H R B e a c b g h k l ∧
  RectangleRootMeetCode P μ A Q ν B e c d g k ∧
  RectangleRootMeetCode P μ A Q ν B e c d h l ∧
  RectangleCrossMeetCode Q ν B e b d k l

def RectangleFulfillmentCode (P G r μ A Q H R ν B e a : ZFSet.{u}) : Prop :=
  ∀ c ∈ P, ∀ b ∈ P, ∀ d ∈ P, ∀ g ∈ G, ∀ h ∈ G,
    ExternalRectangleCode P G r μ A c b d g h →
      ∃ k ∈ H, ∃ l ∈ H, RectangleActorPairCode P μ A Q H R ν B e a c b d g h k l

namespace BoundedFormula

def rectangleIdealFormula {n} (Q H R B e a c b g h k l : Fin n) : BoundedFormula n :=
  (.conj (.allMem Q (.allMem H.succ (.allMem H.succ.succ (imp (pairMembershipFormula c.succ.succ.succ 2 e.succ.succ.succ) (imp (pairMembershipFormula g.succ.succ.succ 1 a.succ.succ.succ) (imp (pairMembershipFormula h.succ.succ.succ 0 a.succ.succ.succ) (.conj (actionAgreementBelowFormula Q.succ.succ.succ R.succ.succ.succ B.succ.succ.succ k.succ.succ.succ 1 2) (actionAgreementBelowFormula Q.succ.succ.succ R.succ.succ.succ B.succ.succ.succ l.succ.succ.succ 0 2)))))))) (.allMem Q (imp (pairMembershipFormula b.succ 0 e.succ) (actionAgreementBelowFormula Q.succ R.succ B.succ k.succ l.succ 0))))

theorem truth_rectangleIdealFormula {n} (Q H R B e a c b g h k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleIdealFormula Q H R B e a c b g h k l) env ↔ RectangleIdealCode (env Q) (env H) (env R) (env B) (env e) (env a) (env c) (env b) (env g) (env h) (env k) (env l) := by
  simp only [rectangleIdealFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_actionAgreementBelowFormula]
  rfl

def rectangleRootMeetFormula {n} (P μ A Q ν B e c d g k : Fin n) : BoundedFormula n :=
  (.allMem P (.allMem P.succ (.allMem P.succ.succ (.allMem Q.succ.succ.succ (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ.succ (imp (tripleMembershipFormula g.succ.succ.succ.succ.succ.succ.succ c.succ.succ.succ.succ.succ.succ.succ 5 A.succ.succ.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula 5 6 4 μ.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula d.succ.succ.succ.succ.succ.succ.succ 3 e.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula 6 2 e.succ.succ.succ.succ.succ.succ.succ) (imp (pairMembershipFormula 4 1 e.succ.succ.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ.succ.succ 3 0 B.succ.succ.succ.succ.succ.succ.succ) (tripleMembershipFormula 0 2 1 ν.succ.succ.succ.succ.succ.succ.succ))))))))))))))

theorem truth_rectangleRootMeetFormula {n} (P μ A Q ν B e c d g k : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleRootMeetFormula P μ A Q ν B e c d g k) env ↔ RectangleRootMeetCode (env P) (env μ) (env A) (env Q) (env ν) (env B) (env e) (env c) (env d) (env g) (env k) := by
  simp only [rectangleRootMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

def rectangleCrossMeetFormula {n} (Q ν B e b d k l : Fin n) : BoundedFormula n :=
  (.allMem Q (.allMem Q.succ (.allMem Q.succ.succ (.allMem Q.succ.succ.succ (.allMem Q.succ.succ.succ.succ (imp (pairMembershipFormula b.succ.succ.succ.succ.succ 4 e.succ.succ.succ.succ.succ) (imp (pairMembershipFormula d.succ.succ.succ.succ.succ 3 e.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ 3 2 B.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula l.succ.succ.succ.succ.succ 3 1 B.succ.succ.succ.succ.succ) (imp (tripleMembershipFormula k.succ.succ.succ.succ.succ 4 0 B.succ.succ.succ.succ.succ) (.conj (tripleMembershipFormula 2 1 0 ν.succ.succ.succ.succ.succ) (tripleMembershipFormula l.succ.succ.succ.succ.succ 4 0 B.succ.succ.succ.succ.succ))))))))))))

theorem truth_rectangleCrossMeetFormula {n} (Q ν B e b d k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleCrossMeetFormula Q ν B e b d k l) env ↔ RectangleCrossMeetCode (env Q) (env ν) (env B) (env e) (env b) (env d) (env k) (env l) := by
  simp only [rectangleCrossMeetFormula, Truth, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula]
  rfl

def rectangleActorPairFormula {n} (P μ A Q H R ν B e a c b d g h k l : Fin n) : BoundedFormula n :=
  (.conj (rectangleIdealFormula Q H R B e a c b g h k l) (.conj (rectangleRootMeetFormula P μ A Q ν B e c d g k) (.conj (rectangleRootMeetFormula P μ A Q ν B e c d h l) (rectangleCrossMeetFormula Q ν B e b d k l))))

theorem truth_rectangleActorPairFormula {n} (P μ A Q H R ν B e a c b d g h k l : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleActorPairFormula P μ A Q H R ν B e a c b d g h k l) env ↔ RectangleActorPairCode (env P) (env μ) (env A) (env Q) (env H) (env R) (env ν) (env B) (env e) (env a) (env c) (env b) (env d) (env g) (env h) (env k) (env l) := by
  simp only [rectangleActorPairFormula, Truth, truth_rectangleIdealFormula,
    truth_rectangleRootMeetFormula, truth_rectangleCrossMeetFormula]
  rfl

def rectangleFulfillmentFormula {n} (P G r μ A Q H R ν B e a : Fin n) : BoundedFormula n :=
  (.allMem P (.allMem P.succ (.allMem P.succ.succ (.allMem G.succ.succ.succ (.allMem G.succ.succ.succ.succ (imp (externalRectangleFormula P.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ r.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ 4 3 2 1 0) (.exMem H.succ.succ.succ.succ.succ (.exMem H.succ.succ.succ.succ.succ.succ (rectangleActorPairFormula P.succ.succ.succ.succ.succ.succ.succ μ.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ ν.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ a.succ.succ.succ.succ.succ.succ.succ 6 5 4 3 2 1 0)))))))))

theorem truth_rectangleFulfillmentFormula {n} (P G r μ A Q H R ν B e a : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rectangleFulfillmentFormula P G r μ A Q H R ν B e a) env ↔ RectangleFulfillmentCode (env P) (env G) (env r) (env μ) (env A) (env Q) (env H) (env R) (env ν) (env B) (env e) (env a) := by
  simp only [rectangleFulfillmentFormula, Truth, truth_imp, truth_exMem,
    truth_externalRectangleFormula, truth_rectangleActorPairFormula]
  rfl

theorem realize_rectangleFulfillmentFormula (M : TransitiveGround.{u}) {n}
    (P G r μ A Q H R ν B e a : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    SetFormula.Realize M.sets (rectangleFulfillmentFormula P G r μ A Q H R ν B e a).toFormula env ↔
      RectangleFulfillmentCode (env P) (env G) (env r) (env μ) (env A) (env Q) (env H)
        (env R) (env ν) (env B) (env e) (env a) :=
  (realize_toFormula M _ env members).trans (truth_rectangleFulfillmentFormula P G r μ A Q H R ν B e a env)

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem choose_compressionActorFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I P G Q H R B e a Sources Reps top Caps : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hQ : Q ∈ M.sets)
    (hH : H ∈ M.sets) (hR : R ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets)
    (ha : a ∈ M.sets) (hSources : Sources ∈ M.sets) (hReps : Reps ∈ M.sets)
    (hTop : top ∈ M.sets) (hCaps : Caps ∈ M.sets)
    (total : CompressionActorFulfillmentCode I P G Q H R B e a Sources Reps top Caps) :
    ∃ f ∈ M.sets, ZFSet.IsFunc I H f ∧
      ∀ i k, ZFSet.pair i k ∈ f → CompressionActorCode P G Q H R B e a Sources Reps top Caps i k := by
  let params : Fin 12 → ZFSet.{u} := extend P (extend G (extend Q (extend H (extend R (extend B
    (extend e (extend a (extend Sources (extend Reps (extend top (extend Caps Fin.elim0)))))))))))
  have members : ∀ j, params j ∈ M.sets := Fin.cases hP (Fin.cases hG (Fin.cases hQ (Fin.cases hH
    (Fin.cases hR (Fin.cases hB (Fin.cases he (Fin.cases ha (Fin.cases hSources
      (Fin.cases hReps (Fin.cases hTop (Fin.cases hCaps (fun j => Fin.elim0 j))))))))))))
  let φ : SetFormula 14 := (BoundedFormula.compressionActorFormula 2 3 4 5 6 7 8 9 10 11 12 13 0 1).toFormula
  let relation := M.definableRelation φ params I H
  have ground : relation ∈ M.sets := M.definableRelation_mem pairing unions powers separation φ params members hI hH
  have exactCode (i k : ZFSet.{u}) (hi : i ∈ I) (hk : k ∈ H) :
      Realize M.sets φ (extend i (extend k params)) ↔
        CompressionActorCode P G Q H R B e a Sources Reps top Caps i k :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive hI hi) (Fin.cases (M.transitive hH hk) members))).trans
      (BoundedFormula.truth_compressionActorFormula 2 3 4 5 6 7 8 9 10 11 12 13 0 1 _)
  obtain ⟨f, hf, function, included⟩ := M.uniformize_relation pairing unions powers separation choice hI hH ground (by
    intro i hi
    obtain ⟨k, hk, code⟩ := total i hi
    exact ⟨k, hk, (M.pair_mem_definableRelation φ params I H i k).2 ⟨hi, hk, (exactCode i k hi hk).2 code⟩⟩)
  refine ⟨f, hf, function, ?_⟩
  intro i k entry
  obtain ⟨hi, hk, realized⟩ := (M.pair_mem_definableRelation φ params I H i k).1 (included entry)
  exact (exactCode i k hi hk).1 realized

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
universe u

structure RectangleAtBoundCode (P r μ A c b d g h X k l : ZFSet.{u}) : Prop where
  first_agreement : ActionAgreementBelow P r A k g c
  second_agreement : ActionAgreementBelow P r A l h c
  common_agreement : ActionAgreementBelow P r A k l b
  values : ∃ v ∈ P, ∃ w ∈ P, ∃ y ∈ P, ∃ z ∈ P, ∃ t ∈ P,
    ZFSet.pair (ZFSet.pair g c) v ∈ A ∧ ZFSet.pair (ZFSet.pair h c) w ∈ A ∧
    ZFSet.pair (ZFSet.pair k d) y ∈ A ∧ ZFSet.pair (ZFSet.pair l d) z ∈ A ∧
    ZFSet.pair (ZFSet.pair k b) t ∈ A ∧ ZFSet.pair (ZFSet.pair l b) t ∈ A ∧
    ZFSet.pair (ZFSet.pair y X) v ∈ μ ∧ ZFSet.pair (ZFSet.pair z X) w ∈ μ ∧
    ZFSet.pair (ZFSet.pair y z) t ∈ μ

theorem MeetOrderCode.meet_entry_of_lower {P r μ x y : ZFSet.{u}}
    (meet : MeetOrderCode P r μ) (hx : x ∈ P) (hy : y ∈ P)
    (lower : ZFSet.pair x y ∈ r) : ZFSet.pair (ZFSet.pair x y) x ∈ μ := by
  obtain ⟨z, entry, _⟩ := meet.operation.2 (ZFSet.pair x y) (ZFSet.pair_mem_prod.2 ⟨hx, hy⟩)
  have hz := (ZFSet.pair_mem_prod.1 (meet.operation.1 entry)).2
  have equal : z = x := meet.order.antisymm z hz x hx (meet.lower_left x y z entry)
    (meet.greatest x y z x hx entry (meet.order.refl x hx) lower)
  exact equal ▸ entry

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.GroundMainTransition
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}
variable (transition : GroundMainTransition source target)

theorem rectangle_at_bound
    (fulfills : RectangleFulfillmentCode source.carrier source.actors source.order
      source.meetGraph source.action target.carrier target.actors target.order target.meetGraph
      target.action transition.points transition.actors)
    {c b d g h X c' b' d' g' h' X' : ZFSet.{u}}
    (rectangle : ExternalRectangleCode source.carrier source.actors source.order
      source.meetGraph source.action c b d g h) (hX : X ∈ source.carrier)
    (firstUpper : ∀ y ∈ source.carrier, ZFSet.pair (ZFSet.pair g d) y ∈ source.action →
      ZFSet.pair y X ∈ source.order)
    (secondUpper : ∀ y ∈ source.carrier, ZFSet.pair (ZFSet.pair h d) y ∈ source.action →
      ZFSet.pair y X ∈ source.order)
    (imageC : ZFSet.pair c c' ∈ transition.points)
    (imageB : ZFSet.pair b b' ∈ transition.points)
    (imageD : ZFSet.pair d d' ∈ transition.points)
    (imageX : ZFSet.pair X X' ∈ transition.points)
    (imageG : ZFSet.pair g g' ∈ transition.actors)
    (imageH : ZFSet.pair h h' ∈ transition.actors) :
    ∃ k ∈ target.actors, ∃ l ∈ target.actors,
      RectangleAtBoundCode target.carrier target.order target.meetGraph target.action
        c' b' d' g' h' X' k l := by
  have rectangleData := rectangle
  obtain ⟨hc, hb, hd, hg, hh, cd, _, _⟩ := rectangleData
  obtain ⟨k, hk, l, hl, ideals, rootG, rootH, cross⟩ := fulfills c hc b hb d hd g hg h hh rectangle
  have hc' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageC)).2
  have hb' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageB)).2
  have hd' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageD)).2
  have hX' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 imageX)).2
  have hg' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 imageG)).2
  have hh' := (ZFSet.pair_mem_prod.1 (transition.group_embedding.injection.function.1 imageH)).2
  obtain ⟨v, gv, _⟩ := source.action_code.function.2 (ZFSet.pair g c) (ZFSet.pair_mem_prod.2 ⟨hg, hc⟩)
  obtain ⟨w, hwAction, _⟩ := source.action_code.function.2 (ZFSet.pair h c) (ZFSet.pair_mem_prod.2 ⟨hh, hc⟩)
  obtain ⟨gd, gD, _⟩ := source.action_code.function.2 (ZFSet.pair g d) (ZFSet.pair_mem_prod.2 ⟨hg, hd⟩)
  obtain ⟨hdv, hD, _⟩ := source.action_code.function.2 (ZFSet.pair h d) (ZFSet.pair_mem_prod.2 ⟨hh, hd⟩)
  have hv := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 gv)).2
  have hw := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 hwAction)).2
  have hgd := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 gD)).2
  have hhd := (ZFSet.pair_mem_prod.1 (source.action_code.function.1 hD)).2
  have vX := source.meet.order.trans v hv gd hgd X hX
    (source.action_code.monotone g hg c hc d hd v hv gd hgd gv gD cd) (firstUpper gd hgd gD)
  have wX := source.meet.order.trans w hw hdv hhd X hX
    (source.action_code.monotone h hh c hc d hd w hw hdv hhd hwAction hD cd) (secondUpper hdv hhd hD)
  have meetV := source.meet.meet_entry_of_lower hv hX vX
  have meetW := source.meet.meet_entry_of_lower hw hX wX
  obtain ⟨v', vv', _⟩ := transition.point_embedding.injection.function.2 v hv
  obtain ⟨w', ww', _⟩ := transition.point_embedding.injection.function.2 w hw
  have hv' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 vv')).2
  have hw' := (ZFSet.pair_mem_prod.1 (transition.point_embedding.injection.function.1 ww')).2
  obtain ⟨y, ky, _⟩ := target.action_code.function.2 (ZFSet.pair k d') (ZFSet.pair_mem_prod.2 ⟨hk, hd'⟩)
  obtain ⟨z, lz, _⟩ := target.action_code.function.2 (ZFSet.pair l d') (ZFSet.pair_mem_prod.2 ⟨hl, hd'⟩)
  obtain ⟨t, kt, _⟩ := target.action_code.function.2 (ZFSet.pair k b') (ZFSet.pair_mem_prod.2 ⟨hk, hb'⟩)
  have hy := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 ky)).2
  have hz := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 lz)).2
  have ht := (ZFSet.pair_mem_prod.1 (target.action_code.function.1 kt)).2
  have agree := ideals.1 c' hc' g' hg' h' hh' imageC imageG imageH
  have meets := cross b' hb' d' hd' y hy z hz t ht imageB imageD ky lz kt
  refine ⟨k, hk, l, hl, agree.1, agree.2, ideals.2 b' hb' imageB,
    v', hv', w', hw', y, hy, z, hz, t, ht, ?_, ?_, ky, lz, kt, meets.2, ?_, ?_, meets.1⟩
  · exact transition.equivariant g g' c v c' v' imageG imageC vv' gv
  · exact transition.equivariant h h' c w c' w' imageH imageC ww' hwAction
  · exact rootG X hX v hv v hv d' hd' X' hX' v' hv' y hy gv meetV imageD imageX vv' ky
  · exact rootH X hX w hw w hw d' hd' X' hX' w' hw' z hz hwAction meetW imageD imageX ww' lz

end PartitionPilot.Forcing.GroundMainTransition

end OAI
