import OAI.SetTheory.PartitionPrinciple.Definability.GroundExternalRequestSetRecognition

namespace OAI

namespace PartitionPilot.Forcing
open SetFormula
universe u

def ExternalRequestDataCode (I P G r μ A Rectangles Requests Letters : ZFSet.{u}) : Prop :=
  Rectangles = externalRectangles P G r μ A ∧
    Requests = externalRequestCarrier I P Rectangles ∧
    Letters = externalChildLetters I P Rectangles

namespace SetFormula

def externalRequestDataFormula {n} (Rectangles Requests Letters I P G r μ A : Fin n) : SetFormula n :=
  let old (i : Fin n) := i.succ.succ.succ
  ex (ex (ex (.conj (BoundedFormula.emptyFormula 2).toFormula
    (.conj (BoundedFormula.successorFormula 1 2).toFormula
      (.conj (BoundedFormula.successorFormula 0 1).toFormula
        (.conj (externalRectanglesSetFormula (old Rectangles) (old P) (old G) (old r) (old μ) (old A))
          (.conj (externalRequestSetFormula (old Requests) (old I) (old P) (old Rectangles) 2 1 0)
            (externalChildSetFormula (old Letters) (old Requests) (old Rectangles) 2 1 0))))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_externalRequestDataFormula {n} (Rectangles Requests Letters I P G r μ A : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (externalRequestDataFormula Rectangles Requests Letters I P G r μ A) env ↔
      ExternalRequestDataCode (env I) (env P) (env G) (env r) (env μ) (env A)
        (env Rectangles) (env Requests) (env Letters) := by
  simp only [externalRequestDataFormula, realize_ex, Realize]
  constructor
  · rintro ⟨zero, hzero, first, hfirst, second, hsecond, empty, succ1, succ2, rectangles, requests, letters⟩
    have bounds : ∀ i, (extend second (extend first (extend zero env))) i ∈ M.sets :=
      Fin.cases hsecond (Fin.cases hfirst (Fin.cases hzero members))
    have eq0 : zero = natSetCode 0 := (BoundedFormula.truth_emptyFormula 2 _).1
      ((BoundedFormula.realize_toFormula M _ _ bounds).1 empty)
    have eq1 : first = natSetCode 1 := by
      have eq := (BoundedFormula.truth_successorFormula 1 2 _).1
        ((BoundedFormula.realize_toFormula M _ _ bounds).1 succ1)
      change first = insert zero zero at eq
      rw [eq0] at eq
      exact eq
    have eq2 : second = natSetCode 2 := by
      have eq := (BoundedFormula.truth_successorFormula 0 1 _).1
        ((BoundedFormula.realize_toFormula M _ _ bounds).1 succ2)
      change second = insert first first at eq
      rw [eq1] at eq
      exact eq
    have rect := (M.realize_externalRectanglesSetFormula pairing unions powers separation
      Rectangles.succ.succ.succ P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ
      μ.succ.succ.succ A.succ.succ.succ _ bounds).1 rectangles
    have req := (M.realize_externalRequestSetFormula pairing unions powers separation
      Requests.succ.succ.succ I.succ.succ.succ P.succ.succ.succ Rectangles.succ.succ.succ
      2 1 0 _ bounds eq0 eq1 eq2).1 requests
    have children := (M.realize_externalChildSetFormula pairing unions powers separation
      Letters.succ.succ.succ Requests.succ.succ.succ I.succ.succ.succ P.succ.succ.succ
      Rectangles.succ.succ.succ 2 1 0 _ bounds req eq0 eq1 eq2).1 letters
    exact ⟨rect, req, children⟩
  · rintro ⟨rect, req, children⟩
    have hzero : (natSetCode 0 : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨env I, members I⟩
    have hfirst : (natSetCode 1 : ZFSet.{u}) ∈ M.sets := M.insert_mem pairing unions hzero hzero
    have hsecond : (natSetCode 2 : ZFSet.{u}) ∈ M.sets := M.insert_mem pairing unions hfirst hfirst
    let values := extend (natSetCode 2) (extend (natSetCode 1) (extend (natSetCode 0) env))
    have bounds : ∀ i, values i ∈ M.sets :=
      Fin.cases hsecond (Fin.cases hfirst (Fin.cases hzero members))
    refine ⟨natSetCode 0, hzero, natSetCode 1, hfirst, natSetCode 2, hsecond, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (BoundedFormula.realize_toFormula M _ values bounds).2
        ((BoundedFormula.truth_emptyFormula 2 values).2 rfl)
    · exact (BoundedFormula.realize_toFormula M _ values bounds).2
        ((BoundedFormula.truth_successorFormula 1 2 values).2 rfl)
    · exact (BoundedFormula.realize_toFormula M _ values bounds).2
        ((BoundedFormula.truth_successorFormula 0 1 values).2 rfl)
    · exact (M.realize_externalRectanglesSetFormula pairing unions powers separation
        Rectangles.succ.succ.succ P.succ.succ.succ G.succ.succ.succ r.succ.succ.succ
        μ.succ.succ.succ A.succ.succ.succ values bounds).2 rect
    · exact (M.realize_externalRequestSetFormula pairing unions powers separation
        Requests.succ.succ.succ I.succ.succ.succ P.succ.succ.succ Rectangles.succ.succ.succ
        2 1 0 values bounds rfl rfl rfl).2 req
    · exact (M.realize_externalChildSetFormula pairing unions powers separation
        Letters.succ.succ.succ Requests.succ.succ.succ I.succ.succ.succ P.succ.succ.succ
        Rectangles.succ.succ.succ 2 1 0 values bounds req rfl rfl rfl).2 children

end TransitiveGround

theorem mem_externalRequestField (kind : Bool) (I P R z : ZFSet.{u}) :
    z ∈ (if kind then externalRequestKinds I P R else externalRequestPayloads I P R) ↔
      ∃ t x, ZFSet.pair t x ∈ externalRequestCarrier I P R ∧
        z = ZFSet.pair (ZFSet.pair t x) (if kind then t else x) := by
  cases kind
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [externalRequestPayloads, mem_graphRestriction]
    constructor
    · rintro ⟨q, hq, y, rfl, projection⟩
      obtain ⟨t, _, x, _, equal⟩ := (mem_productSecond _ _ _).1 projection
      have same := ZFSet.pair_inj.1 equal
      exact ⟨t, x, same.1 ▸ hq, equal⟩
    · rintro ⟨t, x, member, rfl⟩
      exact mem_graphRestriction.1 (externalRequest_fields_entry member).2
  · simp only [↓reduceIte]
    rw [externalRequestKinds, mem_graphRestriction]
    constructor
    · rintro ⟨q, hq, y, rfl, projection⟩
      obtain ⟨t, _, x, _, equal⟩ := (mem_productFirst _ _ _).1 projection
      have same := ZFSet.pair_inj.1 equal
      exact ⟨t, x, same.1 ▸ hq, equal⟩
    · rintro ⟨t, x, member, rfl⟩
      exact mem_graphRestriction.1 (externalRequest_fields_entry member).1

namespace BoundedFormula

def externalRequestFieldEntryFormula {n} (kind : Bool) (z I P R zero one two : Fin n) : BoundedFormula n :=
  disj (exMem I (orderedTripleFormula z.succ zero.succ 0 (if kind then zero.succ else 0)))
    (disj (exMem P (orderedTripleFormula z.succ one.succ 0 (if kind then one.succ else 0)))
      (exMem R (orderedTripleFormula z.succ two.succ 0 (if kind then two.succ else 0))))

theorem truth_externalRequestFieldEntryFormula {n} (kind : Bool) (z I P R zero one two : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env zero = natSetCode 0)
    (ho : env one = natSetCode 1) (ht : env two = natSetCode 2) :
    Truth (externalRequestFieldEntryFormula kind z I P R zero one two) env ↔
      env z ∈ (if kind then externalRequestKinds (env I) (env P) (env R)
        else externalRequestPayloads (env I) (env P) (env R)) := by
  simp only [externalRequestFieldEntryFormula, truth_disj, truth_exMem, truth_orderedTripleFormula]
  have chosen (tag : Fin n) (x : ZFSet.{u}) :
      extend x env (if kind then tag.succ else 0) = (if kind then env tag else x) := by
    cases kind <;> rfl
  simp only [chosen]
  change ((∃ x ∈ env I, env z = ZFSet.pair (ZFSet.pair (env zero) x) (if kind then env zero else x)) ∨
    (∃ x ∈ env P, env z = ZFSet.pair (ZFSet.pair (env one) x) (if kind then env one else x)) ∨
    (∃ x ∈ env R, env z = ZFSet.pair (ZFSet.pair (env two) x) (if kind then env two else x))) ↔ _
  rw [hz, ho, ht, mem_externalRequestField]
  constructor
  · intro member
    rcases member with ⟨x, hx, equal⟩ | ⟨x, hx, equal⟩ | ⟨x, hx, equal⟩
    · exact ⟨natSetCode 0, x, (compression_mem_externalRequestCarrier _ _ _ _).2 hx, equal⟩
    · exact ⟨natSetCode 1, x, (separation_mem_externalRequestCarrier _ _ _ _).2 hx, equal⟩
    · exact ⟨natSetCode 2, x, (rectangle_mem_externalRequestCarrier _ _ _ _).2 hx, equal⟩
  · rintro ⟨t, x, request, equal⟩
    rcases (pair_mem_externalRequestCarrier _ _ _ _ _).1 request with
      ⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨rfl, hx⟩
    · exact Or.inl ⟨x, hx, equal⟩
    · exact Or.inr (Or.inl ⟨x, hx, equal⟩)
    · exact Or.inr (Or.inr ⟨x, hx, equal⟩)

end BoundedFormula

namespace SetFormula

def externalRequestFieldFormula {n} (kind : Bool) (output I P R : Fin n) : SetFormula n :=
  let old (i : Fin n) := i.succ.succ.succ
  ex (ex (ex (.conj (BoundedFormula.emptyFormula 2).toFormula
    (.conj (BoundedFormula.successorFormula 1 2).toFormula
      (.conj (BoundedFormula.successorFormula 0 1).toFormula
        (exactSetFormula (old output)
          (BoundedFormula.externalRequestFieldEntryFormula kind 0
            (old I).succ (old P).succ (old R).succ 3 2 1).toFormula))))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_externalRequestFieldFormula {n} (kind : Bool) (output I P R : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (externalRequestFieldFormula kind output I P R) env ↔
      env output = (if kind then externalRequestKinds (env I) (env P) (env R)
        else externalRequestPayloads (env I) (env P) (env R)) := by
  have fieldGround : (if kind then externalRequestKinds (env I) (env P) (env R)
      else externalRequestPayloads (env I) (env P) (env R)) ∈ M.sets := by
    cases kind
    · exact M.externalRequestPayloads_mem pairing unions powers separation (members I) (members P) (members R)
    · exact M.externalRequestKinds_mem pairing unions powers separation (members I) (members P) (members R)
  have meaning (zero one two : ZFSet.{u})
      (bounds : ∀ j, extend two (extend one (extend zero env)) j ∈ M.sets)
      (hz : zero = natSetCode 0) (ho : one = natSetCode 1) (ht : two = natSetCode 2) :
      Realize M.sets (exactSetFormula output.succ.succ.succ
        (BoundedFormula.externalRequestFieldEntryFormula kind 0
          I.succ.succ.succ.succ P.succ.succ.succ.succ R.succ.succ.succ.succ 3 2 1).toFormula)
        (extend two (extend one (extend zero env))) ↔
      env output = (if kind then externalRequestKinds (env I) (env P) (env R)
        else externalRequestPayloads (env I) (env P) (env R)) := by
    apply M.realize_exactBoundedSetFormula output.succ.succ.succ _ _ bounds fieldGround
    intro z
    exact BoundedFormula.truth_externalRequestFieldEntryFormula kind _ _ _ _ _ _ _ _ hz ho ht
  simp only [externalRequestFieldFormula, realize_ex, Realize]
  constructor
  · rintro ⟨zero, hzero, one, hone, two, htwo, empty, succ1, succ2, field⟩
    have bounds : ∀ j, extend two (extend one (extend zero env)) j ∈ M.sets :=
      Fin.cases htwo (Fin.cases hone (Fin.cases hzero members))
    have hz : zero = natSetCode 0 := (BoundedFormula.truth_emptyFormula 2 _).1
      ((BoundedFormula.realize_toFormula M _ _ bounds).1 empty)
    have ho : one = natSetCode 1 := by
      have equal := (BoundedFormula.truth_successorFormula 1 2 _).1
        ((BoundedFormula.realize_toFormula M _ _ bounds).1 succ1)
      change one = insert zero zero at equal
      rw [hz] at equal
      exact equal
    have ht : two = natSetCode 2 := by
      have equal := (BoundedFormula.truth_successorFormula 0 1 _).1
        ((BoundedFormula.realize_toFormula M _ _ bounds).1 succ2)
      change two = insert one one at equal
      rw [ho] at equal
      exact equal
    exact (meaning zero one two bounds hz ho ht).1 field
  · intro equal
    have hz : (natSetCode 0 : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨env I, members I⟩
    have ho : (natSetCode 1 : ZFSet.{u}) ∈ M.sets := M.insert_mem pairing unions hz hz
    have ht : (natSetCode 2 : ZFSet.{u}) ∈ M.sets := M.insert_mem pairing unions ho ho
    have bounds : ∀ j, extend (natSetCode 2) (extend (natSetCode 1) (extend (natSetCode 0) env)) j ∈ M.sets :=
      Fin.cases ht (Fin.cases ho (Fin.cases hz members))
    refine ⟨natSetCode 0, hz, natSetCode 1, ho, natSetCode 2, ht, ?_, ?_, ?_,
      (meaning _ _ _ bounds rfl rfl rfl).2 equal⟩
    · exact (BoundedFormula.realize_toFormula M _ _ bounds).2
        ((BoundedFormula.truth_emptyFormula 2 _).2 rfl)
    · exact (BoundedFormula.realize_toFormula M _ _ bounds).2
        ((BoundedFormula.truth_successorFormula 1 2 _).2 rfl)
    · exact (BoundedFormula.realize_toFormula M _ _ bounds).2
        ((BoundedFormula.truth_successorFormula 0 1 _).2 rfl)

noncomputable def definable_externalRequestField (kind : Bool) : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => if kind then externalRequestKinds (env 0) (env 1) (env 2)
      else externalRequestPayloads (env 0) (env 1) (env 2)) where
  formula := externalRequestFieldFormula kind 0 1 2 3
  closed := by
    intro env members
    cases kind
    · exact M.externalRequestPayloads_mem pairing unions powers separation (members 0) (members 1) (members 2)
    · exact M.externalRequestKinds_mem pairing unions powers separation (members 0) (members 1) (members 2)
  correct := fun env members z hz => M.realize_externalRequestFieldFormula pairing unions powers separation
    kind 0 1 2 3 (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
