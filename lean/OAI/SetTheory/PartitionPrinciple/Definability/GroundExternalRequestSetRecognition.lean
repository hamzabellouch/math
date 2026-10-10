import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleFulfillmentAtBound

namespace OAI

namespace PartitionPilot.Forcing

section
universe u

noncomputable def externalRequestCarrier (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  (ZFSet.prod {natSetCode 0} I ∪ ZFSet.prod {natSetCode 1} P) ∪
    ZFSet.prod {natSetCode 2} Rectangles

noncomputable def externalChildLetters (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (externalRequestCarrier I P Rectangles) {natSetCode 0} ∪
    ZFSet.prod (ZFSet.prod {natSetCode 2} Rectangles) {natSetCode 1}

theorem pair_mem_externalRequestCarrier (I P Rectangles t x : ZFSet.{u}) :
    ZFSet.pair t x ∈ externalRequestCarrier I P Rectangles ↔
      (t = natSetCode 0 ∧ x ∈ I) ∨ (t = natSetCode 1 ∧ x ∈ P) ∨
        (t = natSetCode 2 ∧ x ∈ Rectangles) := by
  simp only [externalRequestCarrier, ZFSet.mem_union, ZFSet.pair_mem_prod,
    ZFSet.mem_singleton, or_assoc]

theorem compression_mem_externalRequestCarrier (I P Rectangles i : ZFSet.{u}) :
    ZFSet.pair (natSetCode 0) i ∈ externalRequestCarrier I P Rectangles ↔ i ∈ I := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem separation_mem_externalRequestCarrier (I P Rectangles x : ZFSet.{u}) :
    ZFSet.pair (natSetCode 1) x ∈ externalRequestCarrier I P Rectangles ↔ x ∈ P := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem rectangle_mem_externalRequestCarrier (I P Rectangles z : ZFSet.{u}) :
    ZFSet.pair (natSetCode 2) z ∈ externalRequestCarrier I P Rectangles ↔ z ∈ Rectangles := by
  rw [pair_mem_externalRequestCarrier]
  simp only [natSetCode_injective.eq_iff]
  simp

theorem pair_mem_externalChildLetters (I P Rectangles request child : ZFSet.{u}) :
    ZFSet.pair request child ∈ externalChildLetters I P Rectangles ↔
      (request ∈ externalRequestCarrier I P Rectangles ∧ child = natSetCode 0) ∨
        (request ∈ ZFSet.prod {natSetCode 2} Rectangles ∧ child = natSetCode 1) := by
  simp only [externalChildLetters, ZFSet.mem_union, ZFSet.pair_mem_prod, ZFSet.mem_singleton]

theorem compression_child_iff (I P Rectangles i child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 0) i) child ∈ externalChildLetters I P Rectangles ↔
      i ∈ I ∧ child = natSetCode 0 := by
  rw [pair_mem_externalChildLetters, compression_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, natSetCode_injective.eq_iff]
  simp

theorem separation_child_iff (I P Rectangles x child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 1) x) child ∈ externalChildLetters I P Rectangles ↔
      x ∈ P ∧ child = natSetCode 0 := by
  rw [pair_mem_externalChildLetters, separation_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, natSetCode_injective.eq_iff]
  simp

theorem rectangle_child_iff (I P Rectangles z child : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair (natSetCode 2) z) child ∈ externalChildLetters I P Rectangles ↔
      z ∈ Rectangles ∧ (child = natSetCode 0 ∨ child = natSetCode 1) := by
  rw [pair_mem_externalChildLetters, rectangle_mem_externalRequestCarrier]
  simp only [ZFSet.pair_mem_prod, ZFSet.mem_singleton, true_and]
  exact and_or_left.symm

noncomputable def externalRequestTags : ZFSet.{u} :=
  insert (natSetCode 0) (insert (natSetCode 1) {natSetCode 2})

noncomputable def externalRequestPayloadBound (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  (I ∪ P) ∪ Rectangles

theorem externalRequestCarrier_subset (I P Rectangles : ZFSet.{u}) :
    externalRequestCarrier I P Rectangles ⊆
      ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles) := by
  intro z hz
  rcases ZFSet.mem_union.1 hz with old | rectangle
  · rcases ZFSet.mem_union.1 old with compression | separation
    · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 compression
      rw [ZFSet.mem_singleton] at ht
      subst t
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert _ _,
        ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inl hx)))⟩
    · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 separation
      rw [ZFSet.mem_singleton] at ht
      subst t
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert _ _),
        ZFSet.mem_union.2 (Or.inl (ZFSet.mem_union.2 (Or.inr hx)))⟩
  · obtain ⟨t, ht, x, hx, rfl⟩ := ZFSet.mem_prod.1 rectangle
    rw [ZFSet.mem_singleton] at ht
    subst t
    exact ZFSet.pair_mem_prod.2
      ⟨ZFSet.mem_insert_of_mem _ (ZFSet.mem_insert_of_mem _ (ZFSet.mem_singleton.2 rfl)),
        ZFSet.mem_union.2 (Or.inr hx)⟩

noncomputable def externalRequestKinds (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction (externalRequestCarrier I P Rectangles)
    (productFirst externalRequestTags (externalRequestPayloadBound I P Rectangles))

noncomputable def externalRequestPayloads (I P Rectangles : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction (externalRequestCarrier I P Rectangles)
    (productSecond externalRequestTags (externalRequestPayloadBound I P Rectangles))

theorem externalRequestKinds_function (I P Rectangles : ZFSet.{u}) :
    FunctionGraphOn (externalRequestCarrier I P Rectangles) (externalRequestKinds I P Rectangles) :=
  (show FunctionGraphOn (ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles))
    (productFirst externalRequestTags (externalRequestPayloadBound I P Rectangles)) from
    ⟨_, productFirst_function _ _⟩).restrict (externalRequestCarrier_subset I P Rectangles)

theorem externalRequestPayloads_function (I P Rectangles : ZFSet.{u}) :
    FunctionGraphOn (externalRequestCarrier I P Rectangles) (externalRequestPayloads I P Rectangles) :=
  (show FunctionGraphOn (ZFSet.prod externalRequestTags (externalRequestPayloadBound I P Rectangles))
    (productSecond externalRequestTags (externalRequestPayloadBound I P Rectangles)) from
    ⟨_, productSecond_function _ _⟩).restrict (externalRequestCarrier_subset I P Rectangles)

theorem externalRequest_fields_entry {I P Rectangles t x : ZFSet.{u}}
    (member : ZFSet.pair t x ∈ externalRequestCarrier I P Rectangles) :
    ZFSet.pair (ZFSet.pair t x) t ∈ externalRequestKinds I P Rectangles ∧
      ZFSet.pair (ZFSet.pair t x) x ∈ externalRequestPayloads I P Rectangles := by
  have bounds := ZFSet.pair_mem_prod.1 (externalRequestCarrier_subset I P Rectangles member)
  constructor
  · exact pair_mem_graphRestriction.2
      ⟨(mem_productFirst _ _ _).2 ⟨t, bounds.1, x, bounds.2, rfl⟩, member⟩
  · exact pair_mem_graphRestriction.2
      ⟨(mem_productSecond _ _ _).2 ⟨t, bounds.1, x, bounds.2, rfl⟩, member⟩

def ExternalRequestOverlapForward
    (P G Rectangles Maps F r A zero first second q i x j y : ZFSet.{u}) : Prop :=
  (i = zero ∧ j = first ∧ ∃ f ∈ F, ZFSet.pair q f ∈ Maps ∧ ZFSet.pair y x ∈ f) ∨
  (i = zero ∧ j = first ∧ ∃ w ∈ P, q = ZFSet.pair first w ∧ x = y ∧ ZFSet.pair x w ∈ r) ∨
  (∃ t ∈ Rectangles, ∃ c ∈ P, ∃ b ∈ P, ∃ d ∈ P, ∃ g ∈ G, ∃ h ∈ G,
    q = ZFSet.pair second t ∧ t = externalRectangleCode c b d g h ∧
      ((i = zero ∧ j = first ∧ ZFSet.pair y c ∈ r ∧ ZFSet.pair (ZFSet.pair g y) x ∈ A) ∨
       (i = zero ∧ j = second ∧ ZFSet.pair y c ∈ r ∧ ZFSet.pair (ZFSet.pair h y) x ∈ A) ∨
       (i = first ∧ j = second ∧ x = y ∧ ZFSet.pair x b ∈ r)))

def ExternalRequestOverlapCode
    (P G Rectangles Maps F r A zero first second q i x j y : ZFSet.{u}) : Prop :=
  (i = j ∧ x = y) ∨
    ExternalRequestOverlapForward P G Rectangles Maps F r A zero first second q i x j y ∨
    ExternalRequestOverlapForward P G Rectangles Maps F r A zero first second q j y i x

theorem ExternalRequestOverlapCode.symm
    {P G Rectangles Maps F r A zero first second q i x j y : ZFSet.{u}}
    (overlap : ExternalRequestOverlapCode P G Rectangles Maps F r A zero first second q i x j y) :
    ExternalRequestOverlapCode P G Rectangles Maps F r A zero first second q j y i x := by
  rcases overlap with ⟨equal, same⟩ | forward | backward
  · exact Or.inl ⟨equal.symm, same.symm⟩
  · exact Or.inr (Or.inr forward)
  · exact Or.inr (Or.inl backward)

noncomputable def externalTileVertices (Requests Rectangles U : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod (ZFSet.prod Requests {natSetCode 0, natSetCode 1}) U ∪
    ZFSet.prod (ZFSet.prod (ZFSet.prod {natSetCode 2} Rectangles) {natSetCode 2}) U

theorem triple_mem_externalTileVertices (Requests Rectangles U q i x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair q i) x ∈ externalTileVertices Requests Rectangles U ↔
      ((q ∈ Requests ∧ (i = natSetCode 0 ∨ i = natSetCode 1)) ∨
        (q ∈ ZFSet.prod {natSetCode 2} Rectangles ∧ i = natSetCode 2)) ∧ x ∈ U := by
  simp only [externalTileVertices, ZFSet.mem_union, ZFSet.pair_mem_prod,
    ZFSet.mem_pair, ZFSet.mem_singleton]
  tauto

namespace BoundedFormula
open SetFormula

def compressionOverlapFormula {n} (Maps F zero first q i x j y : Fin n) : BoundedFormula n :=
  .conj (.equal i zero) (.conj (.equal j first)
    (exMem F (.conj (pairMembershipFormula q.succ 0 Maps.succ)
      (pairMembershipFormula y.succ x.succ 0))))

def separationOverlapFormula {n} (P r zero first q i x j y : Fin n) : BoundedFormula n :=
  .conj (.equal i zero) (.conj (.equal j first)
    (exMem P (.conj (orderedPairFormula q.succ first.succ 0)
      (.conj (.equal x.succ y.succ) (pairMembershipFormula x.succ 0 r.succ)))))

def requestRectangleOverlapFieldsFormula {n} (r A zero first second i x j y c b g h : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i zero) (.conj (.equal j first)
    (.conj (pairMembershipFormula y c r) (tripleMembershipFormula g y x A))))
    (disj (.conj (.equal i zero) (.conj (.equal j second)
      (.conj (pairMembershipFormula y c r) (tripleMembershipFormula h y x A))))
      (.conj (.equal i first) (.conj (.equal j second)
        (.conj (.equal x y) (pairMembershipFormula x b r)))))

def requestRectangleOverlapFormula {n}
    (P G Rectangles r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  exMem Rectangles (exMem P.succ (exMem P.succ.succ (exMem P.succ.succ.succ
    (exMem G.succ.succ.succ.succ (exMem G.succ.succ.succ.succ.succ
      (.conj (orderedPairFormula q.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ 5)
        (.conj (externalRectangleTupleFormula 5 4 3 2 1 0)
          (requestRectangleOverlapFieldsFormula r.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ
            zero.succ.succ.succ.succ.succ.succ first.succ.succ.succ.succ.succ.succ second.succ.succ.succ.succ.succ.succ
            i.succ.succ.succ.succ.succ.succ x.succ.succ.succ.succ.succ.succ
            j.succ.succ.succ.succ.succ.succ y.succ.succ.succ.succ.succ.succ 4 3 1 0))))))))

def externalRequestOverlapForwardFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  disj (compressionOverlapFormula Maps F zero first q i x j y)
    (disj (separationOverlapFormula P r zero first q i x j y)
      (requestRectangleOverlapFormula P G Rectangles r A zero first second q i x j y))

theorem truth_externalRequestOverlapForwardFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q i x j y) env ↔
      ExternalRequestOverlapForward (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
        (env zero) (env first) (env second) (env q) (env i) (env x) (env j) (env y) := by
  simp only [externalRequestOverlapForwardFormula, compressionOverlapFormula, separationOverlapFormula,
    requestRectangleOverlapFormula, requestRectangleOverlapFieldsFormula, Truth, truth_disj, truth_exMem,
    truth_orderedPairFormula, truth_pairMembershipFormula, truth_tripleMembershipFormula,
    truth_externalRectangleTupleFormula, ExternalRequestOverlapForward]
  rfl

def externalRequestOverlapFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) : BoundedFormula n :=
  disj (.conj (.equal i j) (.equal x y))
    (disj (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q i x j y)
      (externalRequestOverlapForwardFormula P G Rectangles Maps F r A zero first second q j y i x))

theorem truth_externalRequestOverlapFormula {n}
    (P G Rectangles Maps F r A zero first second q i x j y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalRequestOverlapFormula P G Rectangles Maps F r A zero first second q i x j y) env ↔
      ExternalRequestOverlapCode (env P) (env G) (env Rectangles) (env Maps) (env F) (env r) (env A)
        (env zero) (env first) (env second) (env q) (env i) (env x) (env j) (env y) := by
  simp only [externalRequestOverlapFormula, Truth, truth_disj,
    truth_externalRequestOverlapForwardFormula, ExternalRequestOverlapCode]

end BoundedFormula

end

section
open SetRealization
universe u

abbrev ExternalRequestIndex (I P R : ZFSet.{u}) :=
  SetMembers I ⊕ (SetMembers P ⊕ SetMembers R)

noncomputable def externalRequestIndexCode {I P R : ZFSet.{u}} :
    ExternalRequestIndex I P R → ZFSet.{u}
  | .inl i => ZFSet.pair (natSetCode 0) (SetMembers.raw i)
  | .inr (.inl x) => ZFSet.pair (natSetCode 1) (SetMembers.raw x)
  | .inr (.inr r) => ZFSet.pair (natSetCode 2) (SetMembers.raw r)

theorem externalRequestIndexCode_injective (I P R : ZFSet.{u}) :
    Function.Injective (@externalRequestIndexCode I P R) := by
  intro x y equal
  rcases x with i | (x | r) <;> rcases y with j | (y | s) <;>
    simp only [externalRequestIndexCode, ZFSet.pair_inj, natSetCode_injective.eq_iff] at equal
  all_goals simp_all
  all_goals exact SetMembers.raw_injective _ equal

noncomputable def externalRequestPresentation (I P R : ZFSet.{u}) :
    Presentation (ExternalRequestIndex I P R) where
  carrier := externalRequestCarrier I P R
  encode := externalRequestIndexCode
  injective := externalRequestIndexCode_injective I P R
  mem_carrier z := by
    constructor
    · intro hz
      obtain ⟨tag, _, value, _, equal⟩ := ZFSet.mem_prod.1 (externalRequestCarrier_subset I P R hz)
      rw [equal] at hz
      rcases (pair_mem_externalRequestCarrier I P R tag value).1 hz with
        ⟨rfl, hi⟩ | ⟨rfl, hx⟩ | ⟨rfl, hr⟩
      · exact ⟨.inl (SetMembers.ofMem value hi), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
      · exact ⟨.inr (.inl (SetMembers.ofMem value hx)), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
      · exact ⟨.inr (.inr (SetMembers.ofMem value hr)), by
          simpa only [externalRequestIndexCode, SetMembers.raw_ofMem] using equal.symm⟩
    · rintro ⟨index, rfl⟩
      rcases index with i | (x | r)
      · exact (compression_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem i)
      · exact (separation_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem x)
      · exact (rectangle_mem_externalRequestCarrier I P R _).2 (SetMembers.raw_mem r)

def ExternalRequestChild {I P R : ZFSet.{u}} : ExternalRequestIndex I P R → Type u
  | .inl _ => ULift.{u} Unit
  | .inr (.inl _) => ULift.{u} Unit
  | .inr (.inr _) => ULift.{u} Bool

noncomputable def externalRequestChildCode {I P R : ZFSet.{u}} :
    (r : ExternalRequestIndex I P R) → ExternalRequestChild r → ZFSet.{u}
  | .inl _, _ => natSetCode 0
  | .inr (.inl _), _ => natSetCode 0
  | .inr (.inr _), child => externalSignCode child.down

theorem externalRequestChildCode_injective {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) : Function.Injective (externalRequestChildCode r) := by
  rcases r with i | (x | r)
  · intro a b _
    exact ULift.ext _ _ (Subsingleton.elim a.down b.down)
  · intro a b _
    exact ULift.ext _ _ (Subsingleton.elim a.down b.down)
  · intro a b equal
    exact ULift.ext _ _ (externalSignCode_injective equal)

theorem externalRequestChildCode_range {I P R : ZFSet.{u}}
    (r : ExternalRequestIndex I P R) (c : ZFSet.{u}) :
    ZFSet.pair (externalRequestIndexCode r) c ∈ externalChildLetters I P R ↔
      ∃ child : ExternalRequestChild r, externalRequestChildCode r child = c := by
  rcases r with i | (x | r)
  · rw [externalRequestIndexCode, compression_child_iff]
    exact ⟨fun h => ⟨⟨()⟩, h.2.symm⟩,
      fun ⟨_, equal⟩ => ⟨SetMembers.raw_mem i, equal.symm⟩⟩
  · rw [externalRequestIndexCode, separation_child_iff]
    exact ⟨fun h => ⟨⟨()⟩, h.2.symm⟩,
      fun ⟨_, equal⟩ => ⟨SetMembers.raw_mem x, equal.symm⟩⟩
  · rw [externalRequestIndexCode, rectangle_child_iff]
    constructor
    · rintro ⟨_, equal | equal⟩
      · exact ⟨⟨false⟩, equal.symm⟩
      · exact ⟨⟨true⟩, equal.symm⟩
    · rintro ⟨⟨b⟩, equal⟩
      refine ⟨SetMembers.raw_mem r, ?_⟩
      cases b
      · exact Or.inl equal.symm
      · exact Or.inr equal.symm

noncomputable def externalRequestLetterCode {I P R : ZFSet.{u}}
    (letter : Sigma (@ExternalRequestChild I P R)) : ZFSet.{u} :=
  ZFSet.pair (externalRequestIndexCode letter.1) (externalRequestChildCode letter.1 letter.2)

theorem externalRequestLetterCode_injective (I P R : ZFSet.{u}) :
    Function.Injective (@externalRequestLetterCode I P R) := by
  rintro ⟨r, a⟩ ⟨s, b⟩ equal
  have parts := ZFSet.pair_inj.1 equal
  have same := externalRequestIndexCode_injective I P R parts.1
  cases same
  have child := externalRequestChildCode_injective r parts.2
  cases child
  rfl

noncomputable def externalRequestLetterPresentation (I P R : ZFSet.{u}) :
    Presentation (Sigma (@ExternalRequestChild I P R)) where
  carrier := externalChildLetters I P R
  encode := externalRequestLetterCode
  injective := externalRequestLetterCode_injective I P R
  mem_carrier z := by
    constructor
    · intro hz
      have shape : ∃ request ∈ externalRequestCarrier I P R, ∃ child,
          z = ZFSet.pair request child := by
        rcases ZFSet.mem_union.1 hz with zero | one
        · obtain ⟨request, member, child, _, equal⟩ := ZFSet.mem_prod.1 zero
          exact ⟨request, member, child, equal⟩
        · obtain ⟨request, member, child, _, equal⟩ := ZFSet.mem_prod.1 one
          exact ⟨request, ZFSet.mem_union.2 (Or.inr member), child, equal⟩
      obtain ⟨request, member, child, rfl⟩ := shape
      obtain ⟨r, rfl⟩ := ((externalRequestPresentation I P R).mem_carrier request).1 member
      obtain ⟨c, equal⟩ := (externalRequestChildCode_range r child).1 hz
      exact ⟨⟨r, c⟩, congrArg (ZFSet.pair (externalRequestIndexCode r)) equal⟩
    · rintro ⟨⟨r, c⟩, rfl⟩
      exact (externalRequestChildCode_range r _).2 ⟨c, rfl⟩

end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation

theorem externalRectangleBound_mem {P G : ZFSet.{u}} (hP : P ∈ M.sets) (hG : G ∈ M.sets) :
    externalRectangleBound P G ∈ M.sets :=
  M.prod_mem pairing unions powers separation hP
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hP (M.prod_mem pairing unions powers separation hG hG)))

theorem externalRectangles_mem {P G r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) : externalRectangles P G r μ A ∈ M.sets := by
  let params := extend P (extend G (extend r (extend μ (extend A Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalRectanglesEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hP (Fin.cases hG (Fin.cases hr (Fin.cases hμ (Fin.cases hA (fun i => Fin.elim0 i))))))
    (M.externalRectangleBound_mem pairing unions powers separation hP hG)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalRectanglesEntryFormula 0 1 2 3 4 5) (extend z params))
      (externalRectangleBound P G) = externalRectangles P G r μ A := by
    apply ZFSet.ext
    intro z
    rw [externalRectangles, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalRectanglesEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

omit powers separation in
private theorem tag_mem (inhabited : M.sets.Nonempty) (n : Nat) : natSetCode n ∈ M.sets := by
  induction n with
  | zero => exact M.empty_mem inhabited
  | succ n ih => exact M.insert_mem pairing unions ih ih

omit unions powers separation in
private theorem singleton_mem {x : ZFSet.{u}} (hx : x ∈ M.sets) : ({x} : ZFSet.{u}) ∈ M.sets := by
  simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx

theorem externalRequestCarrier_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestCarrier I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact M.binary_union_mem pairing unions
    (M.binary_union_mem pairing unions
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 0)) hI)
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 1)) hP))
    (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 2)) hRectangles)

theorem externalChildLetters_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalChildLetters I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation
      (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
      (M.singleton_mem pairing (tag 0)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation (M.singleton_mem pairing (tag 2)) hRectangles)
      (M.singleton_mem pairing (tag 1)))

omit powers separation in
private theorem fieldBounds_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestTags ∈ M.sets ∧ externalRequestPayloadBound I P Rectangles ∈ M.sets := by
  have tag := M.tag_mem pairing unions ⟨P, hP⟩
  exact ⟨M.insert_mem pairing unions (tag 0)
      (M.insert_mem pairing unions (tag 1) (M.singleton_mem pairing (tag 2))),
    M.binary_union_mem pairing unions (M.binary_union_mem pairing unions hI hP) hRectangles⟩

theorem externalRequestKinds_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestKinds I P Rectangles ∈ M.sets := by
  have bounds := M.fieldBounds_mem pairing unions hI hP hRectangles
  exact M.graphRestriction_mem unions separation
    (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
    (M.productFirst_mem pairing unions powers separation bounds.1 bounds.2)

theorem externalRequestPayloads_mem {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets) :
    externalRequestPayloads I P Rectangles ∈ M.sets := by
  have bounds := M.fieldBounds_mem pairing unions hI hP hRectangles
  exact M.graphRestriction_mem unions separation
    (M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles)
    (M.productSecond_mem pairing unions powers separation bounds.1 bounds.2)

theorem groundExternalRequestData {I P G r μ A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hA : A ∈ M.sets) :
    let Rectangles := externalRectangles P G r μ A
    let Requests := externalRequestCarrier I P Rectangles
    Rectangles ∈ M.sets ∧ Requests ∈ M.sets ∧ externalChildLetters I P Rectangles ∈ M.sets ∧
      externalRequestKinds I P Rectangles ∈ M.sets ∧
      externalRequestPayloads I P Rectangles ∈ M.sets ∧
      FunctionGraphOn Requests (externalRequestKinds I P Rectangles) ∧
      FunctionGraphOn Requests (externalRequestPayloads I P Rectangles) := by
  dsimp only
  have rectangles := M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA
  exact ⟨rectangles, M.externalRequestCarrier_mem pairing unions powers separation hI hP rectangles,
    M.externalChildLetters_mem pairing unions powers separation hI hP rectangles,
    M.externalRequestKinds_mem pairing unions powers separation hI hP rectangles,
    M.externalRequestPayloads_mem pairing unions powers separation hI hP rectangles,
    externalRequestKinds_function I P _, externalRequestPayloads_function I P _⟩

end TransitiveGround

open SetFormula
universe u

namespace BoundedFormula

def externalRequestSetEntryFormula {n} (z I P R zero one two : Fin n) : BoundedFormula n :=
  disj (exMem I (orderedPairFormula z.succ zero.succ 0))
    (disj (exMem P (orderedPairFormula z.succ one.succ 0))
      (exMem R (orderedPairFormula z.succ two.succ 0)))

theorem truth_externalRequestSetEntryFormula {n} (z I P R zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0)
    (ho : env one = natSetCode 1) (ht : env two = natSetCode 2) :
    Truth (externalRequestSetEntryFormula z I P R zero one two) env ↔
      env z ∈ externalRequestCarrier (env I) (env P) (env R) := by
  simp only [externalRequestSetEntryFormula, truth_disj, truth_exMem, truth_orderedPairFormula]
  simp [externalRequestCarrier, ZFSet.mem_prod, extend, hz, ho, ht, or_assoc]

def externalChildSetEntryFormula {n} (z Requests R zero one two : Fin n) : BoundedFormula n :=
  disj (exMem Requests (orderedPairFormula z.succ 0 zero.succ))
    (exMem R (orderedTripleFormula z.succ two.succ 0 one.succ))

theorem truth_externalChildSetEntryFormula {n} (z Requests R zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) {I P : ZFSet.{u}}
    (requests : env Requests = externalRequestCarrier I P (env R))
    (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) (ht : env two = natSetCode 2) :
    Truth (externalChildSetEntryFormula z Requests R zero one two) env ↔
      env z ∈ externalChildLetters I P (env R) := by
  simp only [externalChildSetEntryFormula, truth_disj, truth_exMem,
    truth_orderedPairFormula, truth_orderedTripleFormula]
  simp [externalChildLetters, ZFSet.mem_prod, extend, requests, hz, ho, ht]

end BoundedFormula

namespace SetFormula

def externalRectanglesSetFormula {n} (output P G r μ A : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.externalRectanglesEntryFormula 0 P.succ G.succ r.succ μ.succ A.succ).toFormula

def externalRequestSetFormula {n} (output I P R zero one two : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.externalRequestSetEntryFormula 0 I.succ P.succ R.succ
      zero.succ one.succ two.succ).toFormula

def externalChildSetFormula {n} (output Requests R zero one two : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.externalChildSetEntryFormula 0 Requests.succ R.succ
      zero.succ one.succ two.succ).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_externalRectanglesSetFormula {n} (output P G r μ A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (externalRectanglesSetFormula output P G r μ A) env ↔
      env output = externalRectangles (env P) (env G) (env r) (env μ) (env A) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.externalRectangles_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A)) hz)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_externalRectanglesEntryFormula, mem_externalRectangles]
  constructor
  · rintro ⟨c, _, b, _, d, _, g, _, h, _, equal, eligible⟩
    exact ⟨c, b, d, g, h, equal, eligible⟩
  · rintro ⟨c, b, d, g, h, equal, eligible⟩
    exact ⟨c, eligible.1, b, eligible.2.1, d, eligible.2.2.1,
      g, eligible.2.2.2.1, h, eligible.2.2.2.2.1, equal, eligible⟩

theorem realize_externalRequestSetFormula {n} (output I P R zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) (ht : env two = natSetCode 2) :
    Realize M.sets (externalRequestSetFormula output I P R zero one two) env ↔
      env output = externalRequestCarrier (env I) (env P) (env R) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z h => M.transitive (M.externalRequestCarrier_mem pairing unions powers separation
      (members I) (members P) (members R)) h)
  intro z h
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases h members)]
  exact BoundedFormula.truth_externalRequestSetEntryFormula 0 I.succ P.succ R.succ
    zero.succ one.succ two.succ (extend z env) hz ho ht

theorem realize_externalChildSetFormula {n} (output Requests I P R zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (requests : env Requests = externalRequestCarrier (env I) (env P) (env R))
    (hz : env zero = natSetCode 0) (ho : env one = natSetCode 1) (ht : env two = natSetCode 2) :
    Realize M.sets (externalChildSetFormula output Requests R zero one two) env ↔
      env output = externalChildLetters (env I) (env P) (env R) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z h => M.transitive (M.externalChildLetters_mem pairing unions powers separation
      (members I) (members P) (members R)) h)
  intro z h
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases h members)]
  exact BoundedFormula.truth_externalChildSetEntryFormula 0 Requests.succ R.succ
    zero.succ one.succ two.succ (extend z env) requests hz ho ht

end TransitiveGround

end PartitionPilot.Forcing

end OAI
