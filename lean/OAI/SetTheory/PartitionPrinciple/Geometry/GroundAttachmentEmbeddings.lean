import OAI.SetTheory.PartitionPrinciple.Definability.IndexedAttachmentCodes

namespace OAI


namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem taggedExtension_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N : ZFSet.{u}} (hP : P ∈ M.sets) (hN : N ∈ M.sets) :
    taggedExtension P N ∈ M.sets := by
  have singleton : ({P} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hP hP
  exact M.binary_union_mem pairing unions hP
    (M.prod_mem pairing unions powers separation singleton hN)

end TransitiveGround




universe u

namespace BoundedFormula

open SetFormula

def attachmentShadowEntryFormula {n} (z q p μ ell a : Fin n) : BoundedFormula n :=
  exMem q (exMem p.succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (exMem q.succ.succ
        (.conj (tripleMembershipFormula 2 a.succ.succ.succ 0 μ.succ.succ.succ)
          (pairMembershipFormula 0 1 ell.succ.succ.succ)))))

theorem truth_attachmentShadowEntryFormula {n} (z q p μ ell a : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (attachmentShadowEntryFormula z q p μ ell a) env ↔
      env z ∈ attachmentShadowGraph (env q) (env p) (env μ) (env ell) (env a) := by
  simp only [attachmentShadowEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_tripleMembershipFormula, truth_pairMembershipFormula,
    mem_attachmentShadowGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem attachmentIdeal_mem (separation : SeparationSchema M.sets)
    {Q rQ a : ZFSet.{u}} (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
    (ha : a ∈ M.sets) : attachmentIdeal Q rQ a ∈ M.sets := by
  let params := extend a (extend rQ Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.pairMembershipFormula 0 1 2) params
    (Fin.cases ha (Fin.cases hrQ (fun i => Fin.elim0 i))) hQ
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth
      (BoundedFormula.pairMembershipFormula 0 1 2) (extend q params)) Q =
      attachmentIdeal Q rQ a := by
    apply ZFSet.ext
    intro q
    rw [ZFSet.mem_sep, mem_attachmentIdeal, BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ selected

theorem freshPart_mem (separation : SeparationSchema M.sets)
    {Q rQ a : ZFSet.{u}} (hQ : Q ∈ M.sets) (hrQ : rQ ∈ M.sets)
    (ha : a ∈ M.sets) : freshPart Q rQ a ∈ M.sets := by
  let params := extend a (extend rQ Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) params
    (Fin.cases ha (Fin.cases hrQ (fun i => Fin.elim0 i))) hQ
  have equal : ZFSet.sep (fun q => BoundedFormula.Truth
      (.neg (BoundedFormula.pairMembershipFormula 0 1 2)) (extend q params)) Q =
      freshPart Q rQ a := by
    apply ZFSet.ext
    intro q
    simp only [ZFSet.mem_sep, mem_freshPart, BoundedFormula.Truth,
      BoundedFormula.truth_pairMembershipFormula]
    rfl
  exact equal ▸ selected

theorem attachmentShadowGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q P μQ ell a : ZFSet.{u}} (hQ : Q ∈ M.sets) (hP : P ∈ M.sets)
    (hμQ : μQ ∈ M.sets) (hell : ell ∈ M.sets) (ha : a ∈ M.sets) :
    attachmentShadowGraph Q P μQ ell a ∈ M.sets := by
  let params := extend Q (extend P (extend μQ (extend ell (extend a Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.attachmentShadowEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hQ (Fin.cases hP (Fin.cases hμQ (Fin.cases hell
      (Fin.cases ha (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hQ hP)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.attachmentShadowEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod Q P) = attachmentShadowGraph Q P μQ ell a := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_attachmentShadowEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround






noncomputable def attachmentOldEmbeddingGraph (P : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ P, z = ZFSet.pair x x) (ZFSet.prod P P)

noncomputable def attachmentFreshEmbeddingGraph (P N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ q ∈ N, z = ZFSet.pair q (ZFSet.pair P q))
    (ZFSet.prod N (taggedExtension P N))

noncomputable def attachmentTemplateEmbeddingGraph (P Q rQ ell a : ZFSet.{u}) : ZFSet.{u} :=
  ell ∪ attachmentFreshEmbeddingGraph P (freshPart Q rQ a)

theorem mem_attachmentOldEmbeddingGraph (P z : ZFSet.{u}) :
    z ∈ attachmentOldEmbeddingGraph P ↔ ∃ x ∈ P, z = ZFSet.pair x x := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨x, hx, rfl⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, hx⟩, x, hx, rfl⟩

theorem pair_mem_attachmentOldEmbeddingGraph (P x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ attachmentOldEmbeddingGraph P ↔ x ∈ P ∧ y = x := by
  rw [mem_attachmentOldEmbeddingGraph]
  constructor
  · rintro ⟨z, hz, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hz, rfl⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨_, hx, rfl⟩

theorem attachmentOldEmbeddingGraph_isFunc (P N : ZFSet.{u}) :
    ZFSet.IsFunc P (taggedExtension P N) (attachmentOldEmbeddingGraph P) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_attachmentOldEmbeddingGraph P z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, old_mem_taggedExtension hx⟩
  · intro x hx
    exact ⟨x, (pair_mem_attachmentOldEmbeddingGraph P x x).2 ⟨hx, rfl⟩,
      fun y hy => ((pair_mem_attachmentOldEmbeddingGraph P x y).1 hy).2⟩

theorem attachmentOldEmbeddingGraph_injection (P N : ZFSet.{u}) :
    InjectionCode P (taggedExtension P N) (attachmentOldEmbeddingGraph P) := by
  refine ⟨attachmentOldEmbeddingGraph_isFunc P N, ?_⟩
  intro x y z hx hy
  exact ((pair_mem_attachmentOldEmbeddingGraph P x z).1 hx).2.symm.trans
    ((pair_mem_attachmentOldEmbeddingGraph P y z).1 hy).2

theorem mem_attachmentFreshEmbeddingGraph (P N z : ZFSet.{u}) :
    z ∈ attachmentFreshEmbeddingGraph P N ↔ ∃ q ∈ N, z = ZFSet.pair q (ZFSet.pair P q) := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨q, hq, rfl⟩
    exact ZFSet.mem_sep.2
      ⟨ZFSet.pair_mem_prod.2 ⟨hq, pair_mem_taggedExtension.2 hq⟩, q, hq, rfl⟩

theorem pair_mem_attachmentFreshEmbeddingGraph (P N q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ attachmentFreshEmbeddingGraph P N ↔ q ∈ N ∧ y = ZFSet.pair P q := by
  rw [mem_attachmentFreshEmbeddingGraph]
  constructor
  · rintro ⟨r, hr, eq⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hr, rfl⟩
  · rintro ⟨hq, rfl⟩
    exact ⟨q, hq, rfl⟩

theorem mem_attachmentTemplateEmbeddingGraph (P Q rQ ell a z : ZFSet.{u}) :
    z ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ↔
      z ∈ ell ∨ ∃ q ∈ freshPart Q rQ a, z = ZFSet.pair q (ZFSet.pair P q) := by
  rw [attachmentTemplateEmbeddingGraph, ZFSet.mem_union, mem_attachmentFreshEmbeddingGraph]

theorem pair_mem_attachmentTemplateEmbeddingGraph (P Q rQ ell a q y : ZFSet.{u}) :
    ZFSet.pair q y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ↔
      ZFSet.pair q y ∈ ell ∨ (q ∈ freshPart Q rQ a ∧ y = ZFSet.pair P q) := by
  rw [attachmentTemplateEmbeddingGraph, ZFSet.mem_union, pair_mem_attachmentFreshEmbeddingGraph]

theorem attachmentTemplateEmbeddingGraph_of_ideal {P Q rQ ell a q y : ZFSet.{u}}
    (hq : q ∈ attachmentIdeal Q rQ a) :
    ZFSet.pair q y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ↔ ZFSet.pair q y ∈ ell := by
  rw [pair_mem_attachmentTemplateEmbeddingGraph]
  exact ⟨fun h => h.elim id (fun h => False.elim (attachmentIdeal_not_freshPart hq h.1)), Or.inl⟩

theorem attachmentTemplateEmbeddingGraph_of_fresh {P Q rQ ell a q y : ZFSet.{u}}
    (function : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell)
    (hq : q ∈ freshPart Q rQ a) :
    ZFSet.pair q y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell a ↔ y = ZFSet.pair P q := by
  rw [pair_mem_attachmentTemplateEmbeddingGraph]
  constructor
  · intro h
    rcases h with h | h
    · exact False.elim (attachmentIdeal_not_freshPart (ZFSet.pair_mem_prod.1 (function.1 h)).1 hq)
    · exact h.2
  · exact fun eq => Or.inr ⟨hq, eq⟩

theorem attachmentTemplateEmbeddingGraph_isFunc {P Q rQ ell a : ZFSet.{u}}
    (function : ZFSet.IsFunc (attachmentIdeal Q rQ a) P ell) :
    ZFSet.IsFunc Q (taggedExtension P (freshPart Q rQ a))
      (attachmentTemplateEmbeddingGraph P Q rQ ell a) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases (mem_attachmentTemplateEmbeddingGraph P Q rQ ell a z).1 hz with old | ⟨q, hq, rfl⟩
    · obtain ⟨q, hq, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 old)
      exact ZFSet.pair_mem_prod.2 ⟨((mem_attachmentIdeal Q rQ a q).1 hq).1, old_mem_taggedExtension hy⟩
    · exact ZFSet.pair_mem_prod.2
        ⟨((mem_freshPart Q rQ a q).1 hq).1, pair_mem_taggedExtension.2 hq⟩
  · intro q hq
    by_cases below : ZFSet.pair q a ∈ rQ
    · have ideal := (mem_attachmentIdeal Q rQ a q).2 ⟨hq, below⟩
      obtain ⟨y, entry, unique⟩ := function.2 q ideal
      exact ⟨y, attachmentTemplateEmbeddingGraph_of_ideal ideal |>.2 entry,
        fun z hz => unique z ((attachmentTemplateEmbeddingGraph_of_ideal ideal).1 hz)⟩
    · have fresh := (mem_freshPart Q rQ a q).2 ⟨hq, below⟩
      exact ⟨ZFSet.pair P q, (attachmentTemplateEmbeddingGraph_of_fresh function fresh).2 rfl,
        fun y hy => (attachmentTemplateEmbeddingGraph_of_fresh function fresh).1 hy⟩

theorem attachmentTemplateEmbeddingGraph_injection {P Q rQ ell a : ZFSet.{u}}
    (embedding : InjectionCode (attachmentIdeal Q rQ a) P ell) :
    InjectionCode Q (taggedExtension P (freshPart Q rQ a))
      (attachmentTemplateEmbeddingGraph P Q rQ ell a) := by
  refine ⟨attachmentTemplateEmbeddingGraph_isFunc embedding.function, ?_⟩
  intro x y z hx hy
  rcases (pair_mem_attachmentTemplateEmbeddingGraph P Q rQ ell a x z).1 hx with hx | hx
  · rcases (pair_mem_attachmentTemplateEmbeddingGraph P Q rQ ell a y z).1 hy with hy | hy
    · exact embedding.injective x y z hx hy
    · exact False.elim (pair_tag_not_mem P y (hy.2 ▸ (ZFSet.pair_mem_prod.1 (embedding.function.1 hx)).2))
  · rcases (pair_mem_attachmentTemplateEmbeddingGraph P Q rQ ell a y z).1 hy with hy | hy
    · exact False.elim (pair_tag_not_mem P x (hx.2 ▸ (ZFSet.pair_mem_prod.1 (embedding.function.1 hy)).2))
    · exact (ZFSet.pair_inj.1 (hx.2.symm.trans hy.2)).2






namespace BoundedFormula

open SetFormula

def attachmentOldEmbeddingEntryFormula {n} (z p : Fin n) : BoundedFormula n :=
  exMem p (orderedPairFormula z.succ 0 0)

def attachmentFreshEmbeddingEntryFormula {n} (z p d : Fin n) : BoundedFormula n :=
  exMem d (exMem z.succ (exMem 0
    (.conj (orderedPairFormula 0 p.succ.succ.succ 2)
      (orderedPairFormula z.succ.succ.succ 2 0))))

theorem truth_attachmentOldEmbeddingEntryFormula {n} (z p : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (attachmentOldEmbeddingEntryFormula z p) env ↔
      ∃ x ∈ env p, env z = ZFSet.pair x x := by
  simp only [attachmentOldEmbeddingEntryFormula, truth_exMem, truth_orderedPairFormula]
  rfl

theorem truth_attachmentFreshEmbeddingEntryFormula {n} (z p d : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (attachmentFreshEmbeddingEntryFormula z p d) env ↔
      ∃ q ∈ env d, env z = ZFSet.pair q (ZFSet.pair (env p) q) := by
  simp only [attachmentFreshEmbeddingEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ q ∈ env d, ∃ a ∈ env z, ∃ b ∈ a,
    b = ZFSet.pair (env p) q ∧ env z = ZFSet.pair q b) ↔ _
  constructor
  · rintro ⟨q, hq, _, _, b, _, rfl, eq⟩
    exact ⟨q, hq, eq⟩
  · rintro ⟨q, hq, eq⟩
    refine ⟨q, hq, {q, ZFSet.pair (env p) q}, ?_, ZFSet.pair (env p) q,
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, eq⟩
    rw [eq]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem attachmentOldEmbeddingGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P : ZFSet.{u}} (hP : P ∈ M.sets) : attachmentOldEmbeddingGraph P ∈ M.sets := by
  let params := extend P Fin.elim0
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.attachmentOldEmbeddingEntryFormula 0 1) params
    (Fin.cases hP (fun i => Fin.elim0 i))
    (M.prod_mem pairing unions powers separation hP hP)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.attachmentOldEmbeddingEntryFormula 0 1) (extend z params))
      (ZFSet.prod P P) = attachmentOldEmbeddingGraph P := by
    apply ZFSet.ext
    intro z
    rw [attachmentOldEmbeddingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_attachmentOldEmbeddingEntryFormula 0 1 _)
  exact eq ▸ selected

theorem attachmentFreshEmbeddingGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N : ZFSet.{u}} (hP : P ∈ M.sets) (hN : N ∈ M.sets) :
    attachmentFreshEmbeddingGraph P N ∈ M.sets := by
  let params := extend P (extend N Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.attachmentFreshEmbeddingEntryFormula 0 1 2) params
    (Fin.cases hP (Fin.cases hN (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation hN
      (M.taggedExtension_mem pairing unions powers separation hP hN))
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.attachmentFreshEmbeddingEntryFormula 0 1 2) (extend z params))
      (ZFSet.prod N (taggedExtension P N)) = attachmentFreshEmbeddingGraph P N := by
    apply ZFSet.ext
    intro z
    rw [attachmentFreshEmbeddingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_attachmentFreshEmbeddingEntryFormula 0 1 2 _)
  exact eq ▸ selected

theorem attachmentTemplateEmbeddingGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P Q rQ ell a : ZFSet.{u}} (hP : P ∈ M.sets) (hQ : Q ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hell : ell ∈ M.sets) (ha : a ∈ M.sets) :
    attachmentTemplateEmbeddingGraph P Q rQ ell a ∈ M.sets :=
  M.binary_union_mem pairing unions hell
    (M.attachmentFreshEmbeddingGraph_mem pairing unions powers separation hP
      (M.freshPart_mem separation hQ hrQ ha))

end TransitiveGround


end PartitionPilot.Forcing

end OAI
