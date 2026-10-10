import OAI.SetTheory.PartitionPrinciple.Geometry.GroundTemplateIntervalFamilies

namespace OAI

namespace PartitionPilot.Forcing

universe u

noncomputable def batchAttachmentShadowGraph (I P Qs μs As Es : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ Q ∈ ZFSet.sUnion (ZFSet.sUnion Qs),
    ∃ μ ∈ ZFSet.sUnion (ZFSet.sUnion μs), ∃ a ∈ ZFSet.sUnion (ZFSet.sUnion As),
    ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ∃ q ∈ Q, ∃ p ∈ P,
      z = ZFSet.pair (ZFSet.pair i q) p ∧ ZFSet.pair i Q ∈ Qs ∧
      ZFSet.pair i μ ∈ μs ∧ ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧
      ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c p ∈ ell)
    (ZFSet.prod (indexedAttachmentDomain I Qs) P)

noncomputable def batchAttachmentTemplateGraph (I P Qs rs As Es : ZFSet.{u}) : ZFSet.{u} :=
  let D := indexedAttachmentDomain I Qs
  let N := indexedAttachmentFresh I Qs rs As
  let L := taggedExtension P N
  ZFSet.sep (fun z => ∃ x ∈ D, ∃ y ∈ L, z = ZFSet.pair x y ∧
    ((∃ i ∈ I, ∃ q ∈ familyPointBound Qs, x = ZFSet.pair i q ∧
      ∃ ell ∈ ZFSet.sUnion (ZFSet.sUnion Es), ZFSet.pair i ell ∈ Es ∧ ZFSet.pair q y ∈ ell) ∨
      (x ∈ N ∧ y = ZFSet.pair P x))) (ZFSet.prod D L)

noncomputable def batchTemplateGraph (I P Qs rs As Es i : ZFSet.{u}) : ZFSet.{u} :=
  let L := taggedExtension P (indexedAttachmentFresh I Qs rs As)
  ZFSet.sep (fun z => ∃ q ∈ familyPointBound Qs, ∃ y ∈ L,
    z = ZFSet.pair q y ∧ ZFSet.pair (ZFSet.pair i q) y ∈
      batchAttachmentTemplateGraph I P Qs rs As Es)
    (ZFSet.prod (familyPointBound Qs) L)

theorem batchAttachmentShadowGraph_shape (I P Qs μs As Es : ZFSet.{u}) :
    batchAttachmentShadowGraph I P Qs μs As Es ⊆ ZFSet.prod (indexedAttachmentDomain I Qs) P :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_batchAttachmentShadowGraph (I P Qs μs As Es i q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) p ∈ batchAttachmentShadowGraph I P Qs μs As Es ↔
      i ∈ I ∧ ∃ Q μ a ell, ZFSet.pair i Q ∈ Qs ∧ ZFSet.pair i μ ∈ μs ∧
        ZFSet.pair i a ∈ As ∧ ZFSet.pair i ell ∈ Es ∧
          ZFSet.pair q p ∈ attachmentShadowGraph Q P μ ell a := by
  constructor
  · intro hz
    obtain ⟨j, hj, Q, _, μ, _, a, _, ell, _, u, hu, v, hv,
      equal, eQ, eμ, ea, eell, c, hc, meet, image⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨indices, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 indices
    exact ⟨hj, Q, μ, a, ell, eQ, eμ, ea, eell,
      (pair_mem_attachmentShadowGraph Q P μ ell a _ _).2 ⟨hu, hv, c, hc, meet, image⟩⟩
  · rintro ⟨hi, Q, μ, a, ell, eQ, eμ, ea, eell, entry⟩
    obtain ⟨hq, hp, c, hc, meet, image⟩ := (pair_mem_attachmentShadowGraph Q P μ ell a q p).1 entry
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain I Qs i q).2 ⟨hi, Q, eQ, hq⟩, hp⟩,
      i, hi, Q, pair_second_mem_doubleUnion eQ, μ, pair_second_mem_doubleUnion eμ,
      a, pair_second_mem_doubleUnion ea, ell, pair_second_mem_doubleUnion eell,
      q, hq, p, hp, rfl, eQ, eμ, ea, eell, c, hc, meet, image⟩

theorem batchAttachmentTemplateGraph_shape (I P Qs rs As Es : ZFSet.{u}) :
    batchAttachmentTemplateGraph I P Qs rs As Es ⊆
      ZFSet.prod (indexedAttachmentDomain I Qs) (taggedExtension P (indexedAttachmentFresh I Qs rs As)) := by
  intro z hz
  dsimp only [batchAttachmentTemplateGraph] at hz
  exact (ZFSet.mem_sep.1 hz).1

theorem pair_mem_batchAttachmentTemplateGraph (I P Qs rs As Es i q y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es ↔
      ZFSet.pair i q ∈ indexedAttachmentDomain I Qs ∧
      y ∈ taggedExtension P (indexedAttachmentFresh I Qs rs As) ∧
      ((∃ ell, ZFSet.pair i ell ∈ Es ∧ ZFSet.pair q y ∈ ell) ∨
        (ZFSet.pair i q ∈ indexedAttachmentFresh I Qs rs As ∧ y = ZFSet.pair P (ZFSet.pair i q))) := by
  dsimp only [batchAttachmentTemplateGraph]
  constructor
  · intro hz
    have shape := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hz).1
    obtain ⟨x, _, v, _, equal, branch⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    refine ⟨shape.1, shape.2, ?_⟩
    rcases branch with ⟨j, _, u, _, equal, ell, _, entry, image⟩ | fresh
    · obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
      exact Or.inl ⟨ell, entry, image⟩
    · exact Or.inr fresh
  · rintro ⟨domain, hy, branch⟩
    refine ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨domain, hy⟩,
      ZFSet.pair i q, domain, y, hy, rfl, ?_⟩
    rcases branch with ⟨ell, entry, image⟩ | fresh
    · obtain ⟨hi, hq⟩ := ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset I Qs domain)
      exact Or.inl ⟨i, hi, q, hq, rfl, ell, pair_second_mem_doubleUnion entry, entry, image⟩
    · exact Or.inr fresh

theorem pair_mem_batchTemplateGraph (I P Qs rs As Es i q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ batchTemplateGraph I P Qs rs As Es i ↔
      ZFSet.pair (ZFSet.pair i q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es := by
  dsimp only [batchTemplateGraph]
  constructor
  · intro hz
    obtain ⟨u, _, v, _, equal, entry⟩ := (ZFSet.mem_sep.1 hz).2
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact entry
  · intro entry
    have shape := ZFSet.pair_mem_prod.1 (batchAttachmentTemplateGraph_shape I P Qs rs As Es entry)
    have hq := (ZFSet.pair_mem_prod.1 (indexedAttachmentDomain_subset I Qs shape.1)).2
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hq, shape.2⟩, q, hq, y, shape.2, rfl, entry⟩

namespace AttachmentBatchInputs

variable {P rP μP I Qs rs μs As Es Fs Ss : ZFSet.{u}}
variable (d : AttachmentBatchInputs P rP μP I Qs rs μs As Es Fs Ss)
include d

theorem batch_shadow_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q p : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) p ∈ batchAttachmentShadowGraph I P Qs μs As Es ↔
      ZFSet.pair q p ∈ attachmentShadowGraph (d.space i) P (d.meet i) (d.embed i) (d.anchor i) := by
  rw [pair_mem_batchAttachmentShadowGraph]
  constructor
  · rintro ⟨_, Q, μ, a, ell, eQ, eμ, ea, eell, entry⟩
    have eqQ := d.spaces.unique eQ (d.space_entry i)
    have eqμ := d.meets.unique eμ (d.meet_entry i)
    have eqa := d.anchors.unique ea (d.anchor_entry i)
    have eqell := d.embeddings.unique eell (d.embed_entry i)
    exact eqQ ▸ eqμ ▸ eqa ▸ eqell ▸ entry
  · intro entry
    exact ⟨i.property, d.space i, d.meet i, d.anchor i, d.embed i,
      d.space_entry i, d.meet_entry i, d.anchor_entry i, d.embed_entry i, entry⟩

theorem batch_shadow_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) P (batchAttachmentShadowGraph I P Qs μs As Es) := by
  refine ⟨batchAttachmentShadowGraph_shape I P Qs μs As Es, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨p, entry, unique⟩ := (attachmentShadowGraph_function
    (d.fiber j).templateOrder (d.fiber j).anchor_mem (d.fiber j).base_function).2 q qQ
  exact ⟨p, (d.batch_shadow_entry_iff j q p).2 entry,
    fun y hy => unique y ((d.batch_shadow_entry_iff j q y).1 hy)⟩

theorem batch_template_entry_iff (i : {i : ZFSet.{u} // i ∈ I}) (q y : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es ↔
      ZFSet.pair q y ∈ d.embed i ∨
        (q ∈ freshPart (d.space i) (d.rel i) (d.anchor i) ∧
          y = ZFSet.pair P (ZFSet.pair i.val q)) := by
  rw [pair_mem_batchAttachmentTemplateGraph]
  constructor
  · rintro ⟨_, _, branch⟩
    rcases branch with ⟨ell, eell, entry⟩ | ⟨fresh, equal⟩
    · exact Or.inl (d.embeddings.unique eell (d.embed_entry i) ▸ entry)
    · exact Or.inr ⟨(pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
        (d.space_entry i) (d.rel_entry i) (d.anchor_entry i)).1 fresh, equal⟩
  · intro branch
    rcases branch with entry | ⟨fresh, rfl⟩
    · have shape := ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 entry)
      exact ⟨(pair_mem_indexedAttachmentDomain_of_entry d.spaces (d.space_entry i)).2
        ((mem_attachmentIdeal _ _ _ _).1 shape.1).1, old_mem_taggedExtension shape.2,
        Or.inl ⟨d.embed i, d.embed_entry i, entry⟩⟩
    · have indexed := (pair_mem_indexedAttachmentFresh_of_entries d.spaces d.relations d.anchors
        (d.space_entry i) (d.rel_entry i) (d.anchor_entry i)).2 fresh
      exact ⟨indexedAttachmentFresh_subset I Qs rs As indexed, pair_mem_taggedExtension.2 indexed,
        Or.inr ⟨indexed, rfl⟩⟩

theorem batch_template_total (i : {i : ZFSet.{u} // i ∈ I}) {q : ZFSet.{u}}
    (hq : q ∈ d.space i) :
    ∃ y, ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es := by
  classical
  by_cases below : ZFSet.pair q (d.anchor i) ∈ d.rel i
  · obtain ⟨y, entry, _⟩ := (d.fiber i).base_function.2 q
      ((mem_attachmentIdeal _ _ _ _).2 ⟨hq, below⟩)
    exact ⟨y, (d.batch_template_entry_iff i q y).2 (Or.inl entry)⟩
  · exact ⟨ZFSet.pair P (ZFSet.pair i.val q), (d.batch_template_entry_iff i q _).2
      (Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨hq, below⟩, rfl⟩)⟩

theorem batch_template_unique (i : {i : ZFSet.{u} // i ∈ I}) {q y z : ZFSet.{u}}
    (hy : ZFSet.pair (ZFSet.pair i.val q) y ∈ batchAttachmentTemplateGraph I P Qs rs As Es)
    (hz : ZFSet.pair (ZFSet.pair i.val q) z ∈ batchAttachmentTemplateGraph I P Qs rs As Es) : y = z := by
  rcases (d.batch_template_entry_iff i q y).1 hy with hy | hy
  · rcases (d.batch_template_entry_iff i q z).1 hz with hz | hz
    · have source := (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hy)).1
      obtain ⟨v, _, unique⟩ := (d.fiber i).base_function.2 q source
      exact (unique y hy).trans (unique z hz).symm
    · exact False.elim (attachmentIdeal_not_freshPart
        (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hy)).1 hz.1)
  · rcases (d.batch_template_entry_iff i q z).1 hz with hz | hz
    · exact False.elim (attachmentIdeal_not_freshPart
        (ZFSet.pair_mem_prod.1 ((d.fiber i).base_function.1 hz)).1 hy.1)
    · exact hy.2.trans hz.2.symm

theorem batch_template_function :
    ZFSet.IsFunc (indexedAttachmentDomain I Qs) (taggedExtension P (indexedAttachmentFresh I Qs rs As))
      (batchAttachmentTemplateGraph I P Qs rs As Es) := by
  refine ⟨batchAttachmentTemplateGraph_shape I P Qs rs As Es, ?_⟩
  intro x hx
  obtain ⟨i, hi, q, rfl, Q, eQ, hq⟩ := (mem_indexedAttachmentDomain I Qs x).1 hx
  let j : {i : ZFSet.{u} // i ∈ I} := ⟨i, hi⟩
  have qQ : q ∈ d.space j := d.spaces.unique eQ (d.space_entry j) ▸ hq
  obtain ⟨y, entry⟩ := d.batch_template_total j qQ
  exact ⟨y, entry, fun z hz => d.batch_template_unique j hz entry⟩

theorem batch_template_fiber_function (i : {i : ZFSet.{u} // i ∈ I}) :
    ZFSet.IsFunc (d.space i) (taggedExtension P (indexedAttachmentFresh I Qs rs As))
      (batchTemplateGraph I P Qs rs As Es i.val) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    dsimp only [batchTemplateGraph] at hz
    obtain ⟨q, _, y, hy, rfl, entry⟩ := (ZFSet.mem_sep.1 hz).2
    have domain := (ZFSet.pair_mem_prod.1 (d.batch_template_function.1 entry)).1
    exact ZFSet.pair_mem_prod.2
      ⟨(pair_mem_indexedAttachmentDomain_of_entry d.spaces (d.space_entry i)).1 domain, hy⟩
  · intro q hq
    obtain ⟨y, entry⟩ := d.batch_template_total i hq
    exact ⟨y, (pair_mem_batchTemplateGraph I P Qs rs As Es i.val q y).2 entry,
      fun z hz => d.batch_template_unique i
        ((pair_mem_batchTemplateGraph I P Qs rs As Es i.val q z).1 hz) entry⟩

end AttachmentBatchInputs

namespace BoundedFormula

open SetFormula

def batchShadowGraphFormula : BoundedFormula 11 :=
  exMem 1 (exMem 8 (exMem 10 (exMem 12 (exMem 14 (exMem 3 (exMem 8
    (.conj (orderedTripleFormula 7 6 1 0)
      (.conj (pairMembershipFormula 6 5 10)
        (.conj (pairMembershipFormula 6 4 11)
          (.conj (pairMembershipFormula 6 3 12)
            (.conj (pairMembershipFormula 6 2 13)
              (exMem 5 (.conj (tripleMembershipFormula 2 4 0 5)
                (pairMembershipFormula 0 1 3))))))))))))))

theorem truth_batchShadowGraphFormula (env : Fin 11 → ZFSet.{u}) :
    Truth batchShadowGraphFormula env ↔
      ∃ i ∈ env 1, ∃ Q ∈ env 7, ∃ μ ∈ env 8, ∃ a ∈ env 9, ∃ ell ∈ env 10,
        ∃ q ∈ Q, ∃ p ∈ env 2, env 0 = ZFSet.pair (ZFSet.pair i q) p ∧
          ZFSet.pair i Q ∈ env 3 ∧ ZFSet.pair i μ ∈ env 4 ∧
          ZFSet.pair i a ∈ env 5 ∧ ZFSet.pair i ell ∈ env 6 ∧
          ∃ c ∈ Q, ZFSet.pair (ZFSet.pair q a) c ∈ μ ∧ ZFSet.pair c p ∈ ell := by
  simp only [batchShadowGraphFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula]
  rfl

def batchTemplateGraphFormula : BoundedFormula 9 :=
  exMem 1 (exMem 3 (.conj (orderedPairFormula 2 1 0)
    (disj (exMem 6 (exMem 8 (.conj (orderedPairFormula 3 1 0)
      (exMem 11 (.conj (pairMembershipFormula 2 0 11) (pairMembershipFormula 1 3 0))))))
      (.conj (.mem 1 10) (orderedPairFormula 0 5 1)))))

theorem truth_batchTemplateGraphFormula (env : Fin 9 → ZFSet.{u}) :
    Truth batchTemplateGraphFormula env ↔
      ∃ x ∈ env 1, ∃ y ∈ env 2, env 0 = ZFSet.pair x y ∧
        ((∃ i ∈ env 4, ∃ q ∈ env 5, x = ZFSet.pair i q ∧
          ∃ ell ∈ env 7, ZFSet.pair i ell ∈ env 6 ∧ ZFSet.pair q y ∈ ell) ∨
          (x ∈ env 8 ∧ y = ZFSet.pair (env 3) x)) := by
  simp only [batchTemplateGraphFormula, truth_exMem, Truth, truth_disj,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

def batchTemplateFiberFormula : BoundedFormula 5 :=
  exMem 1 (exMem 3 (.conj (orderedPairFormula 2 1 0) (tripleMembershipFormula 5 1 0 6)))

theorem truth_batchTemplateFiberFormula (env : Fin 5 → ZFSet.{u}) :
    Truth batchTemplateFiberFormula env ↔
      ∃ q ∈ env 1, ∃ y ∈ env 2, env 0 = ZFSet.pair q y ∧
        ZFSet.pair (ZFSet.pair (env 3) q) y ∈ env 4 := by
  simp only [batchTemplateFiberFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_tripleMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem batchAttachmentShadowGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs μs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hμs : μs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    batchAttachmentShadowGraph I P Qs μs As Es ∈ M.sets := by
  have doubleUnion {x : ZFSet.{u}} (hx : x ∈ M.sets) : ZFSet.sUnion (ZFSet.sUnion x) ∈ M.sets :=
    M.union_mem unions (M.union_mem unions hx)
  let params := extend I (extend P (extend Qs (extend μs (extend As (extend Es
    (extend (ZFSet.sUnion (ZFSet.sUnion Qs)) (extend (ZFSet.sUnion (ZFSet.sUnion μs))
      (extend (ZFSet.sUnion (ZFSet.sUnion As)) (extend (ZFSet.sUnion (ZFSet.sUnion Es)) Fin.elim0)))))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchShadowGraphFormula params
    (Fin.cases hI (Fin.cases hP (Fin.cases hQs (Fin.cases hμs (Fin.cases hAs (Fin.cases hEs
      (Fin.cases (doubleUnion hQs) (Fin.cases (doubleUnion hμs)
        (Fin.cases (doubleUnion hAs) (Fin.cases (doubleUnion hEs) (fun j => Fin.elim0 j)))))))))))
    (M.prod_mem pairing unions powers separation
      (M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs) hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchShadowGraphFormula
      (extend z params)) (ZFSet.prod (indexedAttachmentDomain I Qs) P) =
        batchAttachmentShadowGraph I P Qs μs As Es := by
    apply ZFSet.ext
    intro z
    rw [batchAttachmentShadowGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchShadowGraphFormula _)
  exact equal ▸ selected

theorem batchAttachmentTemplateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets) :
    batchAttachmentTemplateGraph I P Qs rs As Es ∈ M.sets := by
  let D := indexedAttachmentDomain I Qs
  let N := indexedAttachmentFresh I Qs rs As
  let L := taggedExtension P N
  have hD : D ∈ M.sets := M.indexedAttachmentDomain_mem pairing unions powers separation hI hQs
  have hN : N ∈ M.sets := M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs
  have hL : L ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP hN
  have hPoints := M.familyPointBound_mem unions hQs
  have hE := M.union_mem unions (M.union_mem unions hEs)
  let params := extend D (extend L (extend P (extend I (extend (familyPointBound Qs)
    (extend Es (extend (ZFSet.sUnion (ZFSet.sUnion Es)) (extend N Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchTemplateGraphFormula params
    (Fin.cases hD (Fin.cases hL (Fin.cases hP (Fin.cases hI (Fin.cases hPoints
      (Fin.cases hEs (Fin.cases hE (Fin.cases hN (fun j => Fin.elim0 j)))))))))
    (M.prod_mem pairing unions powers separation hD hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchTemplateGraphFormula
      (extend z params)) (ZFSet.prod D L) = batchAttachmentTemplateGraph I P Qs rs As Es := by
    apply ZFSet.ext
    intro z
    dsimp only [batchAttachmentTemplateGraph]
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchTemplateGraphFormula _)
  exact equal ▸ selected

theorem batchTemplateGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P Qs rs As Es i : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets)
    (hQs : Qs ∈ M.sets) (hrs : rs ∈ M.sets) (hAs : As ∈ M.sets) (hEs : Es ∈ M.sets)
    (hi : i ∈ M.sets) : batchTemplateGraph I P Qs rs As Es i ∈ M.sets := by
  let L := taggedExtension P (indexedAttachmentFresh I Qs rs As)
  let graph := batchAttachmentTemplateGraph I P Qs rs As Es
  have hPoints := M.familyPointBound_mem unions hQs
  have hL : L ∈ M.sets := M.taggedExtension_mem pairing unions powers separation hP
    (M.indexedAttachmentFresh_mem pairing unions powers separation hI hQs hrs hAs)
  have hGraph : graph ∈ M.sets := M.batchAttachmentTemplateGraph_mem
    pairing unions powers separation hI hP hQs hrs hAs hEs
  let params := extend (familyPointBound Qs) (extend L (extend i (extend graph Fin.elim0)))
  have selected := M.bounded_separation_mem separation BoundedFormula.batchTemplateFiberFormula params
    (Fin.cases hPoints (Fin.cases hL (Fin.cases hi (Fin.cases hGraph (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hPoints hL)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.batchTemplateFiberFormula
      (extend z params)) (ZFSet.prod (familyPointBound Qs) L) = batchTemplateGraph I P Qs rs As Es i := by
    apply ZFSet.ext
    intro z
    dsimp only [batchTemplateGraph]
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_batchTemplateFiberFormula _)
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end OAI
