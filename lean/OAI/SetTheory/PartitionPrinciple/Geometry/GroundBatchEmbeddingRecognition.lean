import OAI.SetTheory.PartitionPrinciple.Definability.GroundLiftedCompressionFormulas
import OAI.SetTheory.PartitionPrinciple.Definability.RecursivePrimitiveFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundBatchAttachment

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundDefinableFunction
open SetFormula
universe u

def withAux {M : TransitiveGround.{u}} {n}
    {a f : (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (aux : GroundDefinableFunction M a) (body : SetFormula (n + 2))
    (closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets)
    (correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
      Realize M.sets body (extend (a env) (extend z env)) ↔ z = f env) :
    GroundDefinableFunction M f where
  formula := ex (.conj
    (SetFormula.reindex (extend 0 (fun i => i.succ.succ)) aux.formula) body)
  closed := closed
  correct := by
    intro env members z hz
    simp only [realize_ex, Realize]
    constructor
    · rintro ⟨value, hvalue, specified, result⟩
      have equal : value = a env := by
        apply (aux.correct env members value hvalue).1
        have meaning := (realize_reindex M.sets _ aux.formula _).1 specified
        rw [map_extend] at meaning
        exact meaning
      subst value
      exact (correct env members z hz).1 result
    · intro equal
      refine ⟨a env, aux.closed env members, ?_, (correct env members z hz).2 equal⟩
      rw [realize_reindex, map_extend]
      exact (aux.correct env members (a env) (aux.closed env members)).2 rfl

def withAuxFamily {M : TransitiveGround.{u}} {n k}
    {a : Fin k → (Fin n → ZFSet.{u}) → ZFSet.{u}}
    {f : (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (aux : ∀ j, GroundDefinableFunction M (a j)) (body : SetFormula (n + 1 + k))
    (closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets)
    (correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
      Realize M.sets body (extendMany k (fun j => a j env) (extend z env)) ↔ z = f env) :
    GroundDefinableFunction M f where
  formula := exBlock k (.conj
    (conjBlock k (fun j => SetFormula.reindex
      (extend (prefixIndex (n + 1) k j) (fun i => suffixIndex (n + 1) k i.succ)) (aux j).formula)) body)
  closed := closed
  correct := by
    intro env members z hz
    rw [realize_exBlock]
    constructor
    · rintro ⟨fields, fieldMembers, clauses, result⟩
      have each := (realize_conjBlock M.sets _ _ _).1 clauses
      have values : fields = fun j => a j env := by
        funext j
        have meaning := (realize_reindex M.sets _ _ _).1 (each j)
        rw [map_extend] at meaning
        simp only [extendMany_prefix, extendMany_suffix] at meaning
        exact ((aux j).correct env members (fields j) (fieldMembers j)).1 meaning
      exact (correct env members z hz).1 (values ▸ result)
    · intro equal
      let fields : Fin k → ZFSet.{u} := fun j => a j env
      have fieldMembers : ∀ j, fields j ∈ M.sets := fun j => (aux j).closed env members
      refine ⟨fields, fieldMembers, ?_, (correct env members z hz).2 equal⟩
      apply (realize_conjBlock M.sets _ _ _).2
      intro j
      rw [realize_reindex, map_extend]
      simp only [extendMany_prefix, extendMany_suffix]
      exact ((aux j).correct env members (fields j) (fieldMembers j)).2 rfl

end GroundDefinableFunction

section
open SetFormula
universe u

namespace SetFormula

def indexedDomainSetFormula {n} (output i qs qb : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.indexedAttachmentDomainEntryFormula 0 i.succ qs.succ qb.succ).toFormula

def batchTemplateSetFormula {n} (output domain carrier p i points es eb fresh : Fin n) : SetFormula n :=
  exactSetFormula output (reindex
    (Fin.cases 0 (Fin.cases domain.succ (Fin.cases carrier.succ (Fin.cases p.succ
      (Fin.cases i.succ (Fin.cases points.succ (Fin.cases es.succ
        (Fin.cases eb.succ (Fin.cases fresh.succ Fin.elim0)))))))))
    BoundedFormula.batchTemplateGraphFormula.toFormula)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_indexedDomainSetFormula {n} (output i qs qb : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (bound : env qb = ZFSet.sUnion (ZFSet.sUnion (env qs))) :
    Realize M.sets (indexedDomainSetFormula output i qs qb) env ↔
      env output = indexedAttachmentDomain (env i) (env qs) := by
  apply M.realize_exactBoundedSetFormula output _ env members
    (M.indexedAttachmentDomain_mem pairing unions powers separation (members i) (members qs))
  intro z
  rw [BoundedFormula.truth_indexedAttachmentDomainEntryFormula]
  change (∃ j ∈ env i, ∃ Q ∈ env qb, ∃ q ∈ Q,
    ZFSet.pair j Q ∈ env qs ∧ z = ZFSet.pair j q) ↔ _
  rw [bound, indexedAttachmentDomain, ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨j, hj, Q, _, q, hq, entry, equal⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hj, mem_familyPointBound_of_entry entry hq⟩
  · exact And.right

theorem realize_batchTemplateSetFormula {n}
    (output domain carrier p i qs rs anchors es points eb fresh : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ x, env x ∈ M.sets)
    (domain_eq : env domain = indexedAttachmentDomain (env i) (env qs))
    (fresh_eq : env fresh = indexedAttachmentFresh (env i) (env qs) (env rs) (env anchors))
    (carrier_eq : env carrier = taggedExtension (env p) (env fresh))
    (points_eq : env points = familyPointBound (env qs))
    (base_bound : env eb = ZFSet.sUnion (ZFSet.sUnion (env es))) :
    Realize M.sets (batchTemplateSetFormula output domain carrier p i points es eb fresh) env ↔
      env output = batchAttachmentTemplateGraph (env i) (env p) (env qs) (env rs) (env anchors) (env es) := by
  apply M.realize_exactReindexedBoundedSetFormula output _ _ env members
    (M.batchAttachmentTemplateGraph_mem pairing unions powers separation
      (members i) (members p) (members qs) (members rs) (members anchors) (members es))
  intro z
  rw [BoundedFormula.truth_batchTemplateGraphFormula]
  change (∃ x ∈ env domain, ∃ y ∈ env carrier, z = ZFSet.pair x y ∧
    ((∃ j ∈ env i, ∃ q ∈ env points, x = ZFSet.pair j q ∧
      ∃ ell ∈ env eb, ZFSet.pair j ell ∈ env es ∧ ZFSet.pair q y ∈ ell) ∨
      (x ∈ env fresh ∧ y = ZFSet.pair (env p) x))) ↔ _
  rw [domain_eq, carrier_eq, points_eq, base_bound, fresh_eq]
  dsimp only [batchAttachmentTemplateGraph]
  rw [ZFSet.mem_sep]
  constructor
  · intro witness
    refine ⟨?_, witness⟩
    obtain ⟨x, hx, y, hy, equal, _⟩ := witness
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, hy⟩
  · exact And.right

end TransitiveGround
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_sUnion (unions : Realize M.sets SetFormula.union Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (env 0)) where
  formula := sUnionSetFormula 0 1
  closed := fun _env members => M.union_mem unions (members 0)
  correct := fun env members z hz =>
    M.realize_sUnionSetFormula unions 0 1 (extend z env) (Fin.cases hz members)

noncomputable def definable_doubleUnion (unions : Realize M.sets SetFormula.union Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (ZFSet.sUnion (env 0))) :=
  (M.definable_sUnion unions).comp (fun _ => M.definable_sUnion unions)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_taggedExtension : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => taggedExtension (env 0) (env 1)) where
  formula := taggedExtensionSetFormula 0 1 2
  closed := fun _env members => M.taggedExtension_mem pairing unions powers separation (members 0) (members 1)
  correct := fun env members z hz => M.realize_taggedExtensionSetFormula pairing unions powers separation
    0 1 2 (extend z env) (Fin.cases hz members)

noncomputable def definable_canonicalMeet : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => canonicalMeetGraph (env 0) (env 1)) where
  formula := canonicalMeetSetFormula 0 1 2
  closed := fun _env members => M.canonicalMeetGraph_mem pairing unions powers separation (members 0) (members 1)
  correct := fun env members z hz => M.realize_canonicalMeetSetFormula pairing unions powers separation
    0 1 2 (extend z env) (Fin.cases hz members)

noncomputable def definable_recursiveIndices : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => recursiveAttachmentIndices
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) where
  formula := recursiveIndicesSetFormula 0 1 2 3 4 5 6
  closed := fun _env members => M.recursiveAttachmentIndices_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  correct := fun env members z hz => M.realize_recursiveIndicesSetFormula pairing unions powers separation
    0 1 2 3 4 5 6 (extend z env) (Fin.cases hz members)

noncomputable def definable_codedAttachmentOrder : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => codedAttachmentOrder
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let aux := (M.definable_taggedExtension pairing unions powers separation).reindex
    (Fin.cases (0 : Fin 6) (Fin.cases 1 Fin.elim0))
  refine aux.withAux (codedAttachmentOrderSetFormula 1 0 2 3 4 5 6 7) ?_ ?_
  · intro env members
    exact M.codedAttachmentOrder_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  · intro env members z hz
    exact M.realize_codedAttachmentOrderSetFormula pairing unions powers separation 1 0 2 3 4 5 6 7
      _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_pairSecondField : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => pairSecondField (env 0) (env 1) (env 2) (env 3)) := by
  let aux := (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => (3 : Fin 4))
  refine aux.withAux (pairFieldSetFormula false 1 2 3 4 0 5) ?_ ?_
  · intro env members
    exact M.pairFieldGraph_mem pairing unions powers separation false
      (members 0) (members 1) (members 2) (aux.closed env members) (members 3)
  · intro env members z hz
    exact M.realize_pairSecondFieldSetFormula pairing unions powers separation 1 2 3 4 0 5
      _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_indexedFresh : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => indexedAttachmentFresh (env 0) (env 1) (env 2) (env 3)) := by
  let aux := fun j : Fin 3 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => j.succ)
  refine GroundDefinableFunction.withAuxFamily aux (indexedFreshSetFormula 3 4 5 6 7 0 1 2) ?_ ?_
  · intro env members
    exact M.indexedAttachmentFresh_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3)
  · intro env members z hz
    exact M.realize_indexedFreshSetFormula pairing unions powers separation 3 4 5 6 7 0 1 2 _
      (extendMany_members 3 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl rfl

noncomputable def definable_batchInside : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => batchAttachmentInsideGraph (env 0) (env 1) (env 2)) := by
  let aux := fun j : Fin 2 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => j.succ)
  refine GroundDefinableFunction.withAuxFamily aux (batchInsideSetFormula 2 3 4 5 0 1) ?_ ?_
  · intro env members
    exact M.batchAttachmentInsideGraph_mem pairing unions powers separation (members 0) (members 1) (members 2)
  · intro env members z hz
    exact M.realize_batchInsideSetFormula pairing unions powers separation 2 3 4 5 0 1 _
      (extendMany_members 2 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl

noncomputable def definable_batchUpper : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => batchAttachmentUpperGraph (env 0) (env 1) (env 2) (env 3)) := by
  let slots : Fin 2 → Fin 4 := Fin.cases 2 (Fin.cases 3 Fin.elim0)
  let aux := fun j : Fin 2 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => slots j)
  refine GroundDefinableFunction.withAuxFamily aux (batchUpperSetFormula 2 3 4 5 6 0 1) ?_ ?_
  · intro env members
    exact M.batchAttachmentUpperGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3)
  · intro env members z hz
    exact M.realize_batchUpperSetFormula pairing unions powers separation 2 3 4 5 6 0 1 _
      (extendMany_members 2 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl

noncomputable def definable_batchShadow : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => batchAttachmentShadowGraph
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let slots : Fin 4 → Fin 6 := Fin.cases 2 (Fin.cases 3 (Fin.cases 4 (Fin.cases 5 Fin.elim0)))
  let aux := fun j : Fin 4 => (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => slots j)
  refine GroundDefinableFunction.withAuxFamily aux (batchShadowSetFormula 4 5 6 7 8 9 10 0 1 2 3) ?_ ?_
  · intro env members
    exact M.batchAttachmentShadowGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  · intro env members z hz
    exact M.realize_batchShadowSetFormula pairing unions powers separation 4 5 6 7 8 9 10 0 1 2 3 _
      (extendMany_members 4 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members)) rfl rfl rfl rfl

end TransitiveGround

section
universe u

theorem batchTemplateGraph_eq_section (I P Qs rs As Es i : ZFSet.{u}) :
    batchTemplateGraph I P Qs rs As Es i =
      indexedRelationSection (familyPointBound Qs)
        (taggedExtension P (indexedAttachmentFresh I Qs rs As))
        (batchAttachmentTemplateGraph I P Qs rs As Es) i := rfl

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

noncomputable def batchEmbeddingFamily (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I (familyPointBound Qs)
    (taggedExtension P (indexedAttachmentFresh I Qs rs As))
    (batchAttachmentTemplateGraph I P Qs rs As Es)

theorem batchEmbeddingFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    M.batchEmbeddingFamily I P Qs rs As Es ∈ M.sets ∧
      FunctionGraphOn I (M.batchEmbeddingFamily I P Qs rs As Es) ∧
      ∀ i f, ZFSet.pair i f ∈ M.batchEmbeddingFamily I P Qs rs As Es ↔
        i ∈ I ∧ f = batchTemplateGraph I P Qs rs As Es i := by
  have hN := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have hB := M.familyPointBound_mem unions hQs
  have hR := M.batchAttachmentTemplateGraph_mem pairing unions powers separation hI hP hQs hrs hAs hEs
  obtain ⟨member, function, entries⟩ := M.indexedRelationSections_spec
    pairing unions powers separation hI hB hL hR
  refine ⟨member, ⟨_, function⟩, ?_⟩
  intro i f
  exact (entries i f).trans (and_congr Iff.rfl (by rw [batchTemplateGraph_eq_section]))

theorem exists_batchAttachment_embedding_family
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
    (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
    (hP : P ∈ M.sets) (hrP : rP ∈ M.sets) (hI : I ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hμs : μs ∈ M.sets)
    (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) (hFs : Fs ∈ M.sets)
    (_hSs : Ss ∈ M.sets) :
    d.batchCarrier ∈ M.sets ∧ d.batchOrder ∈ M.sets ∧ d.batchMeetGraph ∈ M.sets ∧
    MeetOrderCode d.batchCarrier d.batchOrder d.batchMeetGraph ∧
    ∃ family ∈ M.sets, FunctionGraphOn I family ∧
      (∀ i f, ZFSet.pair i f ∈ family ↔ i ∈ I ∧ f = batchTemplateGraph I P Qs rs As Es i) ∧
      ∀ (i : {i : ZFSet.{u} // i ∈ I}) f, ZFSet.pair i.val f ∈ family →
        MeetEmbeddingCode (d.space i) d.batchCarrier (d.rel i) d.batchOrder
          (d.meet i) d.batchMeetGraph f := by
  obtain ⟨hL, hr, hm, _, _, _⟩ := M.batchAttachment_ground_codes
    pairing unions powers separation d hP hrP hI hQs hrs hμs hAs hEs hFs
  obtain ⟨member, function, entries⟩ := M.batchEmbeddingFamily_spec
    pairing unions powers separation hI hP hQs hrs hAs hEs
  refine ⟨hL, hr, hm, d.batch_meetOrder, M.batchEmbeddingFamily I P Qs rs As Es,
    member, function, entries, ?_⟩
  intro i f entry
  have eq := ((entries i.val f).1 entry).2
  exact eq.symm ▸ d.batch_template_embedding_code i

end TransitiveGround

end

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_liftedCompressionFamily
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 13 → ZFSet.{u} =>
      M.groundLiftedCompressionFamily (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)
        (env 6) (env 7) (env 8) (env 9) (env 10) (env 11) (env 12)) := by
  let doubleUnion : GroundDefinableFunction M
      (fun env : Fin 1 → ZFSet.{u} => ZFSet.sUnion (ZFSet.sUnion (env 0))) :=
    (M.definable_sUnion unions).comp (fun _ => M.definable_sUnion unions)
  let bounds : Fin 2 → (Fin 13 → ZFSet.{u}) → ZFSet.{u} :=
    ![(fun env => ZFSet.sUnion (ZFSet.sUnion (env 7))),
      (fun env => ZFSet.sUnion (ZFSet.sUnion (env 9)))]
  have definedBounds : ∀ j, GroundDefinableFunction M (bounds j) := by
    intro j
    exact Fin.cases (doubleUnion.reindex (fun _ => 7))
      (Fin.cases (doubleUnion.reindex (fun _ => 9)) (fun k => Fin.elim0 k)) j
  refine GroundDefinableFunction.withAuxFamily definedBounds
    (liftedCompressionFamilyFormula 2 3 4 5 6 7 8 9 10 11 12 13 14 15 0 1) ?_ ?_
  · intro env members
    exact (M.groundLiftedCompressionFamily_spec pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5) (members 6)
      (members 7) (members 8) (members 9) (members 10) (members 11) (members 12)).1
  · intro env members z hz
    exact M.realize_liftedCompressionFamilyFormula pairing unions powers separation
      2 3 4 5 6 7 8 9 10 11 12 13 14 15 0 1
      (extend (ZFSet.sUnion (ZFSet.sUnion (env 7)))
        (extend (ZFSet.sUnion (ZFSet.sUnion (env 9))) (extend z env)))
      (Fin.cases (M.union_mem unions (M.union_mem unions (members 7)))
        (Fin.cases (M.union_mem unions (M.union_mem unions (members 9)))
          (Fin.cases hz members))) rfl rfl

end TransitiveGround

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_indexedDomain : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => indexedAttachmentDomain (env 0) (env 1)) := by
  let aux := (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => (1 : Fin 2))
  refine aux.withAux (indexedDomainSetFormula 1 2 3 0) ?_ ?_
  · intro env members
    exact M.indexedAttachmentDomain_mem pairing unions powers separation (members 0) (members 1)
  · intro env members z hz
    exact M.realize_indexedDomainSetFormula pairing unions powers separation 1 2 3 0
      _ (Fin.cases (aux.closed env members) (Fin.cases hz members)) rfl

noncomputable def definable_batchTemplate : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => batchAttachmentTemplateGraph
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let domain := (M.definable_indexedDomain pairing unions powers separation).reindex
    (Fin.cases (0 : Fin 6) (Fin.cases 2 Fin.elim0))
  let fresh := (M.definable_indexedFresh pairing unions powers separation).reindex
    (Fin.cases (0 : Fin 6) (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 Fin.elim0))))
  let carrierValues : Fin 2 → (Fin 6 → ZFSet.{u}) → ZFSet.{u} :=
    Fin.cases (fun env => env 1) (Fin.cases
      (fun env => indexedAttachmentFresh (env 0) (env 2) (env 3) (env 4)) Fin.elim0)
  let carrier := (M.definable_taggedExtension pairing unions powers separation).comp
    (g := carrierValues)
    (Fin.cases (GroundDefinableFunction.projection M (1 : Fin 6)) (Fin.cases fresh (fun j => Fin.elim0 j)))
  let points := ((M.definable_sUnion unions).comp
    (fun _ : Fin 1 => M.definable_doubleUnion unions)).reindex (fun _ : Fin 1 => (2 : Fin 6))
  let bases := (M.definable_doubleUnion unions).reindex (fun _ : Fin 1 => (5 : Fin 6))
  let values : Fin 5 → (Fin 6 → ZFSet.{u}) → ZFSet.{u} := Fin.cases
    (fun env => indexedAttachmentDomain (env 0) (env 2)) (Fin.cases
    (fun env => indexedAttachmentFresh (env 0) (env 2) (env 3) (env 4)) (Fin.cases
    (fun env => taggedExtension (env 1) (indexedAttachmentFresh (env 0) (env 2) (env 3) (env 4))) (Fin.cases
    (fun env => familyPointBound (env 2))
      (Fin.cases (fun env => ZFSet.sUnion (ZFSet.sUnion (env 5))) Fin.elim0))))
  let aux : ∀ j, GroundDefinableFunction M (values j) :=
    Fin.cases domain (Fin.cases fresh (Fin.cases carrier (Fin.cases points (Fin.cases bases (fun j => Fin.elim0 j)))))
  refine GroundDefinableFunction.withAuxFamily aux (batchTemplateSetFormula 5 0 2 7 6 3 11 4 1) ?_ ?_
  · intro env members
    exact M.batchAttachmentTemplateGraph_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4) (members 5)
  · intro env members z hz
    exact M.realize_batchTemplateSetFormula pairing unions powers separation
      5 0 2 7 6 8 9 10 11 3 4 1 _
      (extendMany_members 5 _ _ (fun j => (aux j).closed env members) (Fin.cases hz members))
      rfl rfl rfl rfl rfl

noncomputable def definable_indexedSections : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => M.indexedRelationSections (env 0) (env 1) (env 2) (env 3)) where
  formula := sectionFamilyFormula 0 1 2 3 4
  closed := fun _ members => (M.indexedRelationSections_spec pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3)).1
  correct := fun env members z hz => M.realize_sectionFamilyFormula pairing 0 1 2 3 4
    (extend z env) (Fin.cases hz members)

noncomputable def definable_batchEmbeddingFamily : GroundDefinableFunction M
    (fun env : Fin 6 → ZFSet.{u} => M.batchEmbeddingFamily
      (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) := by
  let fresh := (M.definable_indexedFresh pairing unions powers separation).reindex
    (Fin.cases (0 : Fin 6) (Fin.cases 2 (Fin.cases 3 (Fin.cases 4 Fin.elim0))))
  let carrierValues : Fin 2 → (Fin 6 → ZFSet.{u}) → ZFSet.{u} :=
    Fin.cases (fun env => env 1) (Fin.cases
      (fun env => indexedAttachmentFresh (env 0) (env 2) (env 3) (env 4)) Fin.elim0)
  let carrier := (M.definable_taggedExtension pairing unions powers separation).comp
    (g := carrierValues)
    (Fin.cases (GroundDefinableFunction.projection M (1 : Fin 6)) (Fin.cases fresh (fun j => Fin.elim0 j)))
  let points := ((M.definable_sUnion unions).comp
    (fun _ : Fin 1 => M.definable_doubleUnion unions)).reindex (fun _ : Fin 1 => (2 : Fin 6))
  let values : Fin 4 → (Fin 6 → ZFSet.{u}) → ZFSet.{u} :=
    Fin.cases (fun env => env 0) (Fin.cases (fun env => familyPointBound (env 2))
      (Fin.cases (fun env => taggedExtension (env 1)
        (indexedAttachmentFresh (env 0) (env 2) (env 3) (env 4)))
        (Fin.cases (fun env => batchAttachmentTemplateGraph
          (env 0) (env 1) (env 2) (env 3) (env 4) (env 5)) Fin.elim0)))
  exact (M.definable_indexedSections pairing unions powers separation).comp (g := values)
    (Fin.cases (GroundDefinableFunction.projection M (0 : Fin 6))
      (Fin.cases points (Fin.cases carrier
        (Fin.cases (M.definable_batchTemplate pairing unions powers separation) (fun j => Fin.elim0 j)))))

noncomputable def batchEmbeddingFamilyFormula {n}
    (output I P Qs rs As Es : Fin n) : SetFormula n :=
  SetFormula.reindex
    (Fin.cases output (Fin.cases I (Fin.cases P (Fin.cases Qs
      (Fin.cases rs (Fin.cases As (Fin.cases Es Fin.elim0)))))))
    (M.definable_batchEmbeddingFamily pairing unions powers separation).formula

theorem realize_batchEmbeddingFamilyFormula {n}
    (output I P Qs rs As Es : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (M.batchEmbeddingFamilyFormula pairing unions powers separation output I P Qs rs As Es) env ↔
      env output = M.batchEmbeddingFamily (env I) (env P) (env Qs) (env rs) (env As) (env Es) := by
  let slots : Fin 6 → Fin n := Fin.cases I (Fin.cases P (Fin.cases Qs
    (Fin.cases rs (Fin.cases As (Fin.cases Es Fin.elim0)))))
  unfold batchEmbeddingFamilyFormula
  rw [realize_reindex]
  change Realize M.sets (M.definable_batchEmbeddingFamily pairing unions powers separation).formula
    (fun j => env (extend output slots j)) ↔ _
  rw [map_extend]
  exact (M.definable_batchEmbeddingFamily pairing unions powers separation).correct
    (fun j => env (slots j)) (fun j => members (slots j)) (env output) (members output)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
