import OAI.SetTheory.PartitionPrinciple.Definability.FixedTopCodes

namespace OAI


namespace PartitionPilot.Forcing

universe u

def singleAttachmentLe (P N rP rQ shadow F x y : ZFSet.{u}) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ ZFSet.pair x y ∈ rP) ∨
  (x ∈ P ∧ ∃ q ∈ N, ∃ s ∈ P,
    y = ZFSet.pair P q ∧ ZFSet.pair q s ∈ shadow ∧ ZFSet.pair x s ∈ rP) ∨
  ((∃ q ∈ N, x = ZFSet.pair P q) ∧ y ∈ F) ∨
  (∃ q ∈ N, ∃ t ∈ N,
    x = ZFSet.pair P q ∧ y = ZFSet.pair P t ∧ ZFSet.pair q t ∈ rQ)

def singleAttachmentOrder (P N rP rQ shadow F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ taggedExtension P N, ∃ y ∈ taggedExtension P N,
    z = ZFSet.pair x y ∧ singleAttachmentLe P N rP rQ shadow F x y)
    (ZFSet.prod (taggedExtension P N) (taggedExtension P N))

theorem pair_mem_singleAttachmentOrder (P N rP rQ shadow F x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ singleAttachmentOrder P N rP rQ shadow F ↔
      x ∈ taggedExtension P N ∧ y ∈ taggedExtension P N ∧
        singleAttachmentLe P N rP rQ shadow F x y := by
  simp only [singleAttachmentOrder, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, ⟨rfl, rfl⟩, lower⟩
    exact ⟨hx, hy, lower⟩
  · rintro ⟨hx, hy, lower⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, ⟨rfl, rfl⟩, lower⟩

theorem singleAttachmentOrder_shape (P N rP rQ shadow F : ZFSet.{u}) :
    singleAttachmentOrder P N rP rQ shadow F ⊆
      ZFSet.prod (taggedExtension P N) (taggedExtension P N) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

namespace BoundedFormula

open SetFormula

def attachmentTagFormula {n} (x p nset : Fin n) : BoundedFormula n :=
  exMem nset (orderedPairFormula x.succ p.succ 0)

def attachmentOldNewFormula {n} (x y p nset shadow r : Fin n) : BoundedFormula n :=
  .conj (.mem x p) (exMem nset (exMem p.succ
    (.conj (orderedPairFormula y.succ.succ p.succ.succ 1)
      (.conj (pairMembershipFormula 1 0 shadow.succ.succ)
        (pairMembershipFormula x.succ.succ 0 r.succ.succ)))))

def attachmentNewNewFormula {n} (x y p nset r : Fin n) : BoundedFormula n :=
  exMem nset (exMem nset.succ
    (.conj (orderedPairFormula x.succ.succ p.succ.succ 1)
      (.conj (orderedPairFormula y.succ.succ p.succ.succ 0)
        (pairMembershipFormula 1 0 r.succ.succ))))

def singleAttachmentLeFormula {n} (x y p nset rP rQ shadow f : Fin n) : BoundedFormula n :=
  disj (.conj (.mem x p) (.conj (.mem y p) (pairMembershipFormula x y rP)))
    (disj (attachmentOldNewFormula x y p nset shadow rP)
      (disj (.conj (attachmentTagFormula x p nset) (.mem y f))
        (attachmentNewNewFormula x y p nset rQ)))

def singleAttachmentOrderEntryFormula {n} (z l p nset rP rQ shadow f : Fin n) :
    BoundedFormula n :=
  exMem l (exMem l.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (singleAttachmentLeFormula 1 0 p.succ.succ nset.succ.succ
      rP.succ.succ rQ.succ.succ shadow.succ.succ f.succ.succ)))

theorem truth_singleAttachmentLeFormula {n} (x y p nset rP rQ shadow f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (singleAttachmentLeFormula x y p nset rP rQ shadow f) env ↔
      singleAttachmentLe (env p) (env nset) (env rP) (env rQ) (env shadow)
        (env f) (env x) (env y) := by
  simp only [singleAttachmentLeFormula, attachmentOldNewFormula, attachmentTagFormula,
    attachmentNewNewFormula, truth_disj, Truth, truth_exMem,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_singleAttachmentOrderEntryFormula {n} (z l p nset rP rQ shadow f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (singleAttachmentOrderEntryFormula z l p nset rP rQ shadow f) env ↔
      ∃ x ∈ env l, ∃ y ∈ env l, env z = ZFSet.pair x y ∧
        singleAttachmentLe (env p) (env nset) (env rP) (env rQ)
          (env shadow) (env f) x y := by
  simp only [singleAttachmentOrderEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_singleAttachmentLeFormula]
  rfl

end BoundedFormula





def codedAttachmentFreshLe (P inside shadow upper x y : ZFSet.{u}) : Prop :=
  ZFSet.pair x y ∈ inside ∨
    ∃ s ∈ P, ZFSet.pair y s ∈ shadow ∧ ZFSet.pair x s ∈ upper

def codedAttachmentLe (P N r inside shadow upper x y : ZFSet.{u}) : Prop :=
  (x ∈ P ∧ y ∈ P ∧ ZFSet.pair x y ∈ r) ∨
  (x ∈ P ∧ ∃ q ∈ N, ∃ s ∈ P,
    y = ZFSet.pair P q ∧ ZFSet.pair q s ∈ shadow ∧ ZFSet.pair x s ∈ r) ∨
  (y ∈ P ∧ ∃ q ∈ N, x = ZFSet.pair P q ∧ ZFSet.pair q y ∈ upper) ∨
  (∃ q ∈ N, ∃ t ∈ N, x = ZFSet.pair P q ∧ y = ZFSet.pair P t ∧
    codedAttachmentFreshLe P inside shadow upper q t)

noncomputable def codedAttachmentOrder (P N r inside shadow upper : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ taggedExtension P N, ∃ y ∈ taggedExtension P N,
    z = ZFSet.pair x y ∧ codedAttachmentLe P N r inside shadow upper x y)
    (ZFSet.prod (taggedExtension P N) (taggedExtension P N))

theorem pair_mem_codedAttachmentOrder (P N r inside shadow upper x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ codedAttachmentOrder P N r inside shadow upper ↔
      x ∈ taggedExtension P N ∧ y ∈ taggedExtension P N ∧
        codedAttachmentLe P N r inside shadow upper x y := by
  simp only [codedAttachmentOrder, ZFSet.mem_sep, ZFSet.pair_mem_prod, ZFSet.pair_inj]
  constructor
  · rintro ⟨⟨hx, hy⟩, a, _, b, _, ⟨rfl, rfl⟩, lower⟩
    exact ⟨hx, hy, lower⟩
  · rintro ⟨hx, hy, lower⟩
    exact ⟨⟨hx, hy⟩, x, hx, y, hy, ⟨rfl, rfl⟩, lower⟩

theorem codedAttachmentOrder_shape (P N r inside shadow upper : ZFSet.{u}) :
    codedAttachmentOrder P N r inside shadow upper ⊆
      ZFSet.prod (taggedExtension P N) (taggedExtension P N) :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

namespace BoundedFormula
open SetFormula

def codedAttachmentFreshLeFormula {n} (x y p inside shadow upper : Fin n) : BoundedFormula n :=
  disj (pairMembershipFormula x y inside) (exMem p
    (.conj (pairMembershipFormula y.succ 0 shadow.succ)
      (pairMembershipFormula x.succ 0 upper.succ)))

def codedAttachmentLeFormula {n} (x y p nset r inside shadow upper : Fin n) : BoundedFormula n :=
  disj (.conj (.mem x p) (.conj (.mem y p) (pairMembershipFormula x y r)))
    (disj (attachmentOldNewFormula x y p nset shadow r)
      (disj (.conj (.mem y p) (exMem nset
        (.conj (orderedPairFormula x.succ p.succ 0)
          (pairMembershipFormula 0 y.succ upper.succ))))
        (exMem nset (exMem nset.succ
          (.conj (orderedPairFormula x.succ.succ p.succ.succ 1)
            (.conj (orderedPairFormula y.succ.succ p.succ.succ 0)
              (codedAttachmentFreshLeFormula 1 0 p.succ.succ inside.succ.succ
                shadow.succ.succ upper.succ.succ)))))))

def codedAttachmentOrderEntryFormula {n} (z l p nset r inside shadow upper : Fin n) :
    BoundedFormula n :=
  exMem l (exMem l.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (codedAttachmentLeFormula 1 0 p.succ.succ nset.succ.succ r.succ.succ
      inside.succ.succ shadow.succ.succ upper.succ.succ)))

theorem truth_codedAttachmentFreshLeFormula {n} (x y p inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentFreshLeFormula x y p inside shadow upper) env ↔
      codedAttachmentFreshLe (env p) (env inside) (env shadow) (env upper) (env x) (env y) := by
  simp only [codedAttachmentFreshLeFormula, truth_disj, truth_exMem, Truth,
    truth_pairMembershipFormula]
  rfl

theorem truth_codedAttachmentLeFormula {n} (x y p nset r inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentLeFormula x y p nset r inside shadow upper) env ↔
      codedAttachmentLe (env p) (env nset) (env r) (env inside) (env shadow)
        (env upper) (env x) (env y) := by
  simp only [codedAttachmentLeFormula, attachmentOldNewFormula, truth_disj, truth_exMem,
    Truth, truth_pairMembershipFormula, truth_orderedPairFormula, truth_codedAttachmentFreshLeFormula]
  rfl

theorem truth_codedAttachmentOrderEntryFormula {n} (z l p nset r inside shadow upper : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (codedAttachmentOrderEntryFormula z l p nset r inside shadow upper) env ↔
      ∃ x ∈ env l, ∃ y ∈ env l, env z = ZFSet.pair x y ∧
        codedAttachmentLe (env p) (env nset) (env r) (env inside) (env shadow) (env upper) x y := by
  simp only [codedAttachmentOrderEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_codedAttachmentLeFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem singleAttachmentOrder_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P N rP rQ shadow F : ZFSet.{u}}
    (hP : P ∈ M.sets) (hN : N ∈ M.sets) (hrP : rP ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hs : shadow ∈ M.sets) (hF : F ∈ M.sets) :
    singleAttachmentOrder P N rP rQ shadow F ∈ M.sets := by
  let L := taggedExtension P N
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  let params := extend L (extend P (extend N (extend rP (extend rQ
    (extend shadow (extend F Fin.elim0))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.singleAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7) params
    (Fin.cases hL (Fin.cases hP (Fin.cases hN (Fin.cases hrP (Fin.cases hrQ
      (Fin.cases hs (Fin.cases hF (fun i => Fin.elim0 i))))))))
    (M.prod_mem pairing unions powers separation hL hL)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.singleAttachmentOrderEntryFormula 0 1 2 3 4 5 6 7)
      (extend z params)) (ZFSet.prod L L) = singleAttachmentOrder P N rP rQ shadow F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, singleAttachmentOrder, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_singleAttachmentOrderEntryFormula
      0 1 2 3 4 5 6 7 _)
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def greatestLowerBoundFormula {n} (l r x y z : Fin n) : BoundedFormula n :=
  .conj (pairMembershipFormula z x r) (.conj (pairMembershipFormula z y r)
    (allMem l (imp (pairMembershipFormula 0 x.succ r.succ)
      (imp (pairMembershipFormula 0 y.succ r.succ) (pairMembershipFormula 0 z.succ r.succ)))))

theorem truth_greatestLowerBoundFormula {n} (l r x y z : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (greatestLowerBoundFormula l r x y z) env ↔
      GreatestLowerBoundCode (env l) (env r) (env x) (env y) (env z) := by
  simp only [greatestLowerBoundFormula, Truth, truth_imp,
    truth_pairMembershipFormula, GreatestLowerBoundCode]
  rfl

def canonicalMeetEntryFormula {n} (v l r : Fin n) : BoundedFormula n :=
  exMem l (exMem l.succ (exMem l.succ.succ
    (.conj (orderedTripleFormula v.succ.succ.succ 2 1 0)
      (greatestLowerBoundFormula l.succ.succ.succ r.succ.succ.succ 2 1 0))))

theorem truth_canonicalMeetEntryFormula {n} (v l r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (canonicalMeetEntryFormula v l r) env ↔
      env v ∈ canonicalMeetGraph (env l) (env r) := by
  simp only [canonicalMeetEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_greatestLowerBoundFormula, mem_canonicalMeetGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula

theorem canonicalMeetGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L r : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets) :
    canonicalMeetGraph L r ∈ M.sets := by
  let params := extend L (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.canonicalMeetEntryFormula 0 1 2) params
    (Fin.cases hL (Fin.cases hr (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hL hL) hL)
  have eq : ZFSet.sep (fun v => BoundedFormula.Truth
      (BoundedFormula.canonicalMeetEntryFormula 0 1 2) (extend v params))
      (ZFSet.prod (ZFSet.prod L L) L) = canonicalMeetGraph L r := by
    apply ZFSet.ext
    intro v
    rw [ZFSet.mem_sep, BoundedFormula.truth_canonicalMeetEntryFormula]
    exact ⟨And.right, fun hv => ⟨canonicalMeetGraph_subset L r hv, hv⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open Compression.RecursiveMaps
universe u

structure CodedPrincipalTile {P Q rP rQ μP μQ : ZFSet.{u}}
    (old : MeetOrderCode P rP μP) (right : MeetOrderCode Q rQ μQ)
    (g : PrincipalAmalgamation.Input old.toMeetOrder right.toMeetOrder) (ell : ZFSet.{u}) where
  base_function : ZFSet.IsFunc (attachmentIdeal Q rQ g.rightAnchor.val) P ell
  base_entry : ∀ x, ZFSet.pair x.val.val (g.overlap.toFun x).val.val ∈ ell

namespace CodedPrincipalTile
variable {P Q rP rQ μP μQ ell : ZFSet.{u}}
variable {old : MeetOrderCode P rP μP} {right : MeetOrderCode Q rQ μQ}
variable {g : PrincipalAmalgamation.Input old.toMeetOrder right.toMeetOrder}
variable (d : CodedPrincipalTile old right g ell)

abbrev Nodes := g.Node

def encode (_d : CodedPrincipalTile old right g ell) : g.Node → ZFSet.{u}
  | .inl p => p.val
  | .inr q => ZFSet.pair P q.val.val

noncomputable abbrev carrier (_d : CodedPrincipalTile old right g ell) :=
  taggedExtension P (freshPart Q rQ g.rightAnchor.val)
noncomputable abbrev order (_d : CodedPrincipalTile old right g ell) :=
  singleAttachmentOrder P (freshPart Q rQ g.rightAnchor.val) rP rQ
    (attachmentShadowGraph Q P μQ ell g.rightAnchor.val) ∅
noncomputable abbrev meetGraph := canonicalMeetGraph d.carrier d.order

include d

omit d in
theorem fresh_mem (_d : CodedPrincipalTile old right g ell) (q : g.Fresh) : q.val.val ∈ freshPart Q rQ g.rightAnchor.val :=
  (mem_freshPart _ _ _ _).2 ⟨q.val.property, q.property⟩

theorem shadow_entry (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair q.val (g.shadow q).val ∈ attachmentShadowGraph Q P μQ ell g.rightAnchor.val := by
  apply (pair_mem_attachmentShadowGraph _ _ _ _ _ _ _).2
  exact ⟨q.property, (g.shadow q).property,
    (right.toMeetOrder.meet q g.rightAnchor).val,
    (right.toMeetOrder.meet q g.rightAnchor).property,
    right.toMeetOrder_meet_entry q g.rightAnchor,
    d.base_entry (Attachment.cut right.toMeetOrder g.rightAnchor q)⟩

theorem encode_mem (x : g.Node) : d.encode x ∈ d.carrier := by
  cases x with
  | inl p => exact old_mem_taggedExtension p.property
  | inr q => exact pair_mem_taggedExtension.2 (d.fresh_mem q)

theorem encode_injective : Function.Injective d.encode := by
  intro x y eq
  cases x with
  | inl p =>
    cases y with
    | inl s => exact congrArg Sum.inl (Subtype.ext eq)
    | inr q =>
      change p.val = ZFSet.pair P q.val.val at eq
      exact False.elim (pair_tag_not_mem P q.val.val (eq ▸ p.property))
  | inr q =>
    cases y with
    | inl p =>
      change ZFSet.pair P q.val.val = p.val at eq
      exact False.elim (pair_tag_not_mem P q.val.val (eq.symm ▸ p.property))
    | inr t => exact congrArg Sum.inr (Subtype.ext (Subtype.ext (ZFSet.pair_inj.1 eq).2))

theorem encode_surjective : ∀ z ∈ d.carrier, ∃ x : g.Node, d.encode x = z := by
  intro z hz
  rcases mem_taggedExtension.1 hz with old | ⟨q, hq, eq⟩
  · exact ⟨.inl ⟨z, old⟩, rfl⟩
  · have fresh := (mem_freshPart Q rQ g.rightAnchor.val q).1 hq
    exact ⟨.inr ⟨⟨q, fresh.1⟩, fresh.2⟩, eq.symm⟩

omit d in
theorem fresh_lower_iff (_d : CodedPrincipalTile old right g ell) (q t : g.Fresh) :
    g.order.le (.inr q) (.inr t) ↔ ZFSet.pair q.val.val t.val.val ∈ rQ := by
  change (_ ∨ False) ↔ _
  exact ⟨fun h => h.elim id False.elim, Or.inl⟩

theorem le_encode (x y : g.Node) :
    ZFSet.pair (d.encode x) (d.encode y) ∈ d.order ↔ g.order.le x y := by
  rw [pair_mem_singleAttachmentOrder]
  have bounded : d.encode x ∈ d.carrier ∧ d.encode y ∈ d.carrier :=
    ⟨d.encode_mem x, d.encode_mem y⟩
  simp only [bounded.1, bounded.2, true_and]
  cases x with
  | inl p =>
    cases y with
    | inl s =>
      change singleAttachmentLe P _ rP rQ _ (∅ : ZFSet) p.val s.val ↔ ZFSet.pair p.val s.val ∈ rP
      constructor
      · rintro (h | h | h | h)
        · exact h.2.2
        · obtain ⟨_, q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ s.property))
        · obtain ⟨⟨q, _, eq⟩, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
        · obtain ⟨q, _, t, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P q (eq ▸ p.property))
      · intro lower
        exact Or.inl ⟨p.property, s.property, lower⟩
    | inr q =>
      change singleAttachmentLe P _ rP rQ _ (∅ : ZFSet) p.val (ZFSet.pair P q.val.val) ↔
        ZFSet.pair p.val (g.shadow q.val).val ∈ rP
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.val.val h.2.1)
        · obtain ⟨_, t, _, s, _, eq, image, lower⟩ := h
          have same : q.val.val = t := (ZFSet.pair_inj.1 eq).2
          subst t
          have graph := attachmentShadowGraph_function right g.rightAnchor.property d.base_function
          obtain ⟨v, _, unique⟩ := graph.2 q.val.val q.val.property
          have sameValue := (unique s image).trans (unique _ (d.shadow_entry q.val)).symm
          exact sameValue ▸ lower
        · obtain ⟨⟨t, _, eq⟩, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
        · obtain ⟨t, _, s, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro lower
        exact Or.inr (Or.inl ⟨p.property, q.val.val, d.fresh_mem q,
          (g.shadow q.val).val, (g.shadow q.val).property, rfl,
          d.shadow_entry q.val, lower⟩)
  | inr q =>
    cases y with
    | inl p =>
      change singleAttachmentLe P _ rP rQ _ (∅ : ZFSet) (ZFSet.pair P q.val.val) p.val ↔ False
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.val.val h.1)
        · exact False.elim (pair_tag_not_mem P q.val.val h.1)
        · exact ZFSet.notMem_empty _ h.2
        · obtain ⟨s, _, t, _, _, eq, _⟩ := h
          exact False.elim (pair_tag_not_mem P t (eq ▸ p.property))
      · intro upper
        exact False.elim upper
    | inr t =>
      rw [d.fresh_lower_iff]
      change singleAttachmentLe P _ rP rQ _ (∅ : ZFSet)
        (ZFSet.pair P q.val.val) (ZFSet.pair P t.val.val) ↔
          ZFSet.pair q.val.val t.val.val ∈ rQ
      constructor
      · rintro (h | h | h | h)
        · exact False.elim (pair_tag_not_mem P q.val.val h.1)
        · exact False.elim (pair_tag_not_mem P q.val.val h.1)
        · exact False.elim (ZFSet.notMem_empty _ h.2)
        · obtain ⟨s, _, v, _, eqQ, eqT, lower⟩ := h
          have sameQ := (ZFSet.pair_inj.1 eqQ).2
          have sameT := (ZFSet.pair_inj.1 eqT).2
          exact sameQ.symm ▸ sameT.symm ▸ lower
      · intro lower
        exact Or.inr (Or.inr (Or.inr ⟨q.val.val, d.fresh_mem q,
          t.val.val, d.fresh_mem t, rfl, rfl, lower⟩))

theorem partialOrder : PartialOrderCode d.carrier d.order where
  relation := singleAttachmentOrder_shape P _ rP rQ _ (∅ : ZFSet)
  refl z hz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    exact (d.le_encode x x).2 (g.order.refl x)
  antisymm z hz w hw zw wz := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    exact congrArg d.encode (g.order.antisymm
      ((d.le_encode x y).1 zw) ((d.le_encode y x).1 wz))
  trans z hz w hw v hv zw wv := by
    obtain ⟨x, rfl⟩ := d.encode_surjective z hz
    obtain ⟨y, rfl⟩ := d.encode_surjective w hw
    obtain ⟨t, rfl⟩ := d.encode_surjective v hv
    exact (d.le_encode x t).2 (g.order.trans
      ((d.le_encode x y).1 zw) ((d.le_encode y t).1 wv))

theorem encoded_meet_glb (x y : g.Node) :
    GreatestLowerBoundCode d.carrier d.order (d.encode x) (d.encode y)
      (d.encode (g.order.meet x y)) := by
  refine ⟨(d.le_encode _ _).2 (g.order.meet_le_left x y),
    (d.le_encode _ _).2 (g.order.meet_le_right x y), ?_⟩
  intro w hw wx wy
  obtain ⟨z, rfl⟩ := d.encode_surjective w hw
  exact (d.le_encode _ _).2 (g.order.le_meet
    ((d.le_encode _ _).1 wx) ((d.le_encode _ _).1 wy))

theorem meetOrder : MeetOrderCode d.carrier d.order d.meetGraph := by
  apply canonicalMeetGraph_code d.partialOrder
  intro x hx y hy
  obtain ⟨s, rfl⟩ := d.encode_surjective x hx
  obtain ⟨t, rfl⟩ := d.encode_surjective y hy
  exact ⟨d.encode (g.order.meet s t), d.encode_mem _, d.encoded_meet_glb s t⟩

theorem encoded_meet_entry (x y : g.Node) :
    ZFSet.pair (ZFSet.pair (d.encode x) (d.encode y))
      (d.encode (g.order.meet x y)) ∈ d.meetGraph :=
  (pair_mem_canonicalMeetGraph _ _ _ _ _).2
    ⟨d.encode_mem x, d.encode_mem y, d.encode_mem _, d.encoded_meet_glb x y⟩

end CodedPrincipalTile

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.CodedPrincipalTile
open Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ ell : ZFSet.{u}}
variable {old : MeetOrderCode P rP μP} {right : MeetOrderCode Q rQ μQ}
variable {g : PrincipalAmalgamation.Input old.toMeetOrder right.toMeetOrder}
variable (d : CodedPrincipalTile old right g ell)

theorem encoded_embedding_order_iff {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder g.order)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph)
    {x y x' y' : ZFSet.{u}} (hx : ZFSet.pair x x' ∈ graph) (hy : ZFSet.pair y y' ∈ graph) :
    ZFSet.pair x' y' ∈ d.order ↔ ZFSet.pair x y ∈ r := by
  have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
  have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
  obtain ⟨w, _, uniqueX⟩ := function.2 x hxA
  obtain ⟨v, _, uniqueY⟩ := function.2 y hyA
  have eqX := (uniqueX x' hx).trans (uniqueX _ (entries ⟨x, hxA⟩)).symm
  have eqY := (uniqueY y' hy).trans (uniqueY _ (entries ⟨y, hyA⟩)).symm
  rw [eqX, eqY, d.le_encode]
  exact embedding.le_iff ⟨x, hxA⟩ ⟨y, hyA⟩

theorem encoded_embedding_code {A r μ graph : ZFSet.{u}}
    (source : MeetOrderCode A r μ)
    (embedding : MeetEmbedding source.toMeetOrder g.order)
    (function : ZFSet.IsFunc A d.carrier graph)
    (entries : ∀ x : {x : ZFSet.{u} // x ∈ A},
      ZFSet.pair x.val (d.encode (embedding.toFun x)) ∈ graph) :
    MeetEmbeddingCode A d.carrier r d.order μ d.meetGraph graph := by
  refine ⟨⟨function, ?_⟩, ?_, ?_⟩
  · intro x y z hx hy
    have xA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have yA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have zL := (ZFSet.pair_mem_prod.1 (function.1 hx)).2
    have refl := d.partialOrder.refl z zL
    exact source.order.antisymm x xA y yA
      ((d.encoded_embedding_order_iff source embedding function entries hx hy).1 refl)
      ((d.encoded_embedding_order_iff source embedding function entries hy hx).1 refl)
  · intro x y x' y' lower hx hy
    exact (d.encoded_embedding_order_iff source embedding function entries hx hy).2 lower
  · intro x y z x' y' z' meet hx hy hz
    have hxA := (ZFSet.pair_mem_prod.1 (function.1 hx)).1
    have hyA := (ZFSet.pair_mem_prod.1 (function.1 hy)).1
    have hzA := (ZFSet.pair_mem_prod.1 (function.1 hz)).1
    let X : {x : ZFSet.{u} // x ∈ A} := ⟨x, hxA⟩
    let Y : {y : ZFSet.{u} // y ∈ A} := ⟨y, hyA⟩
    let Z : {z : ZFSet.{u} // z ∈ A} := ⟨z, hzA⟩
    have image_eq (t : {t : ZFSet.{u} // t ∈ A}) (v : ZFSet.{u})
        (entry : ZFSet.pair t.val v ∈ graph) : v = d.encode (embedding.toFun t) := by
      obtain ⟨w, _, unique⟩ := function.2 t.val t.property
      exact (unique v entry).trans (unique _ (entries t)).symm
    have meet_eq : source.toMeetOrder.meet X Y = Z := by
      apply Subtype.ext
      obtain ⟨w, _, unique⟩ := source.operation.2 (ZFSet.pair x y)
        (ZFSet.pair_mem_prod.2 ⟨hxA, hyA⟩)
      exact (unique _ (source.toMeetOrder_meet_entry X Y)).trans (unique z meet).symm
    have mapped : embedding.toFun Z =
        g.order.meet (embedding.toFun X) (embedding.toFun Y) := by
      rw [← meet_eq]
      exact embedding.map_meet X Y
    rw [image_eq X x' hx, image_eq Y y' hy, image_eq Z z' hz, mapped]
    exact d.encoded_meet_entry (embedding.toFun X) (embedding.toFun Y)

theorem old_embedding_code :
    MeetEmbeddingCode P d.carrier rP d.order μP d.meetGraph (attachmentOldEmbeddingGraph P) := by
  apply d.encoded_embedding_code old g.left
    (attachmentOldEmbeddingGraph_isFunc P (freshPart Q rQ g.rightAnchor.val))
  intro p
  exact (pair_mem_attachmentOldEmbeddingGraph P p.val p.val).2 ⟨p.property, rfl⟩

theorem template_entry (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair q.val (d.encode (g.right.toFun q)) ∈
      attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val := by
  classical
  change ZFSet.pair q.val (d.encode (g.represent q)) ∈ _
  by_cases h : right.toMeetOrder.le q g.rightAnchor
  · rw [g.represent_old q h]
    exact (pair_mem_attachmentTemplateEmbeddingGraph _ _ _ _ _ _ _).2
      (Or.inl (d.base_entry ⟨q, h⟩))
  · rw [g.represent_new q h]
    exact (pair_mem_attachmentTemplateEmbeddingGraph _ _ _ _ _ _ _).2
      (Or.inr ⟨(mem_freshPart _ _ _ _).2 ⟨q.property, h⟩, rfl⟩)

theorem template_embedding_code :
    MeetEmbeddingCode Q d.carrier rQ d.order μQ d.meetGraph
      (attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val) :=
  d.encoded_embedding_code right g.right (attachmentTemplateEmbeddingGraph_isFunc d.base_function)
    d.template_entry

theorem template_entry_iff (q : {q : ZFSet.{u} // q ∈ Q}) (y : ZFSet.{u}) :
    ZFSet.pair q.val y ∈ attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val ↔
      y = d.encode (g.right.toFun q) := by
  constructor
  · intro entry
    obtain ⟨z, _, unique⟩ := (attachmentTemplateEmbeddingGraph_isFunc d.base_function).2 q.val q.property
    exact (unique y entry).trans (unique _ (d.template_entry q)).symm
  · intro eq
    exact eq.symm ▸ d.template_entry q

include d in
theorem template_old_overlap (p : {p : ZFSet.{u} // p ∈ P})
    (q : {q : ZFSet.{u} // q ∈ Q}) :
    ZFSet.pair q.val p.val ∈ attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val ↔
      ∃ h : right.toMeetOrder.le q g.rightAnchor,
        (g.overlap.toFun ⟨q, h⟩).val = p := by
  rw [d.template_entry_iff]
  have equal : p.val = d.encode (g.right.toFun q) ↔ g.right.toFun q = g.left.toFun p := by
    exact ⟨fun eq => d.encode_injective eq.symm, fun eq => congrArg d.encode eq.symm⟩
  exact equal.trans (g.overlap_exact p q)

theorem old_ideal (p : {p : ZFSet.{u} // p ∈ P}) (x : g.Node)
    (lower : ZFSet.pair (d.encode x) p.val ∈ d.order) : ∃ q, g.left.toFun q = x :=
  g.left_ideal p x ((d.le_encode x (g.left.toFun p)).1 lower)

theorem template_ideal (q : {q : ZFSet.{u} // q ∈ Q}) (x : g.Node)
    (lower : ZFSet.pair (d.encode x) (d.encode (g.right.toFun q)) ∈ d.order) :
    ∃ p, g.right.toFun p = x :=
  g.right_ideal q x ((d.le_encode x (g.right.toFun q)).1 lower)

end PartitionPilot.Forcing.CodedPrincipalTile



namespace PartitionPilot.Forcing.CodedPrincipalTile
open SetFormula Compression.RecursiveMaps
universe u
variable {P Q rP rQ μP μQ ell : ZFSet.{u}}
variable {old : MeetOrderCode P rP μP} {right : MeetOrderCode Q rQ μQ}
variable {g : PrincipalAmalgamation.Input old.toMeetOrder right.toMeetOrder}
variable (d : CodedPrincipalTile old right g ell) (M : TransitiveGround.{u})

theorem ground_codes
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hrP : rP ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hμQ : μQ ∈ M.sets) (hell : ell ∈ M.sets) :
    d.carrier ∈ M.sets ∧ d.order ∈ M.sets ∧ d.meetGraph ∈ M.sets ∧
      attachmentOldEmbeddingGraph P ∈ M.sets ∧
      attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val ∈ M.sets := by
  have ha := M.transitive hQ g.rightAnchor.property
  have hN := M.freshPart_mem separation hQ hrQ ha
  have hL := M.taggedExtension_mem pairing unions powers separation hP hN
  have hs := M.attachmentShadowGraph_mem pairing unions powers separation hQ hP hμQ hell ha
  have hr := M.singleAttachmentOrder_mem pairing unions powers separation hP hN hrP hrQ hs
    (M.empty_mem ⟨P, hP⟩)
  exact ⟨hL, hr, M.canonicalMeetGraph_mem pairing unions powers separation hL hr,
    M.attachmentOldEmbeddingGraph_mem pairing unions powers separation hP,
    M.attachmentTemplateEmbeddingGraph_mem pairing unions powers separation hP hQ hrQ hell ha⟩

theorem exists_ground_tile
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hP : P ∈ M.sets) (hQ : Q ∈ M.sets) (hrP : rP ∈ M.sets)
    (hrQ : rQ ∈ M.sets) (hμQ : μQ ∈ M.sets) (hell : ell ∈ M.sets) :
    ∃ L ∈ M.sets, ∃ r ∈ M.sets, ∃ μ ∈ M.sets, ∃ leftMap ∈ M.sets, ∃ rightMap ∈ M.sets,
      L = d.carrier ∧ r = d.order ∧ μ = d.meetGraph ∧
      leftMap = attachmentOldEmbeddingGraph P ∧
      rightMap = attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val ∧
      MeetOrderCode L r μ ∧ MeetEmbeddingCode P L rP r μP μ leftMap ∧
      MeetEmbeddingCode Q L rQ r μQ μ rightMap := by
  obtain ⟨hL, hr, hμ, hl, ht⟩ := d.ground_codes M pairing unions powers separation hP hQ hrP hrQ hμQ hell
  exact ⟨d.carrier, hL, d.order, hr, d.meetGraph, hμ,
    attachmentOldEmbeddingGraph P, hl,
    attachmentTemplateEmbeddingGraph P Q rQ ell g.rightAnchor.val, ht,
    rfl, rfl, rfl, rfl, rfl, d.meetOrder, d.old_embedding_code, d.template_embedding_code⟩

end PartitionPilot.Forcing.CodedPrincipalTile



namespace PartitionPilot.Forcing
open Compression.RecursiveMaps SetFormula
universe u

noncomputable def separationTileBase (P r W : ZFSet.{u}) : ZFSet.{u} :=
  attachmentOldEmbeddingGraph (attachmentIdeal P r W)

noncomputable def separationTileCarrier (P r W : ZFSet.{u}) : ZFSet.{u} :=
  taggedExtension P (freshPart P r W)

noncomputable def separationTileOrder (P r μ W : ZFSet.{u}) : ZFSet.{u} :=
  singleAttachmentOrder P (freshPart P r W) r r
    (attachmentShadowGraph P P μ (separationTileBase P r W) W) ∅

noncomputable def separationTileMeet (P r μ W : ZFSet.{u}) : ZFSet.{u} :=
  canonicalMeetGraph (separationTileCarrier P r W) (separationTileOrder P r μ W)

noncomputable def separationTileMap (P r W : ZFSet.{u}) : ZFSet.{u} :=
  attachmentTemplateEmbeddingGraph P P r (separationTileBase P r W) W

theorem separationTileBase_function (P r W : ZFSet.{u}) :
    ZFSet.IsFunc (attachmentIdeal P r W) P (separationTileBase P r W) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := (mem_attachmentOldEmbeddingGraph _ z).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx, ((mem_attachmentIdeal _ _ _ _).1 hx).1⟩
  · intro x hx
    exact ⟨x, (pair_mem_attachmentOldEmbeddingGraph _ _ _).2 ⟨hx, rfl⟩,
      fun y hy => ((pair_mem_attachmentOldEmbeddingGraph _ _ _).1 hy).2⟩

theorem separationTileCoding {P r μ : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (W : {x : ZFSet.{u} // x ∈ P}) :
    CodedPrincipalTile old old (BinaryTiles.separation old.toMeetOrder W)
      (separationTileBase P r W.val) := by
  refine ⟨separationTileBase_function P r W.val, ?_⟩
  intro point
  exact (pair_mem_attachmentOldEmbeddingGraph _ _ _).2
    ⟨(mem_attachmentIdeal _ _ _ _).2 ⟨point.val.property, point.property⟩, rfl⟩

theorem pair_mem_separationTileMap (P r W x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ separationTileMap P r W ↔
      x ∈ P ∧ ((ZFSet.pair x W ∈ r ∧ y = x) ∨
        (ZFSet.pair x W ∉ r ∧ y = ZFSet.pair P x)) := by
  rw [separationTileMap, pair_mem_attachmentTemplateEmbeddingGraph]
  rw [separationTileBase, pair_mem_attachmentOldEmbeddingGraph, mem_attachmentIdeal, mem_freshPart]
  tauto

theorem separationTile_meetOrder {P r μ W : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hW : W ∈ P) :
    MeetOrderCode (separationTileCarrier P r W) (separationTileOrder P r μ W)
      (separationTileMeet P r μ W) :=
  (separationTileCoding old ⟨W, hW⟩).meetOrder

theorem separationTile_embeddings {P r μ W : ZFSet.{u}}
    (old : MeetOrderCode P r μ) (hW : W ∈ P) :
    MeetEmbeddingCode P (separationTileCarrier P r W) r (separationTileOrder P r μ W)
      μ (separationTileMeet P r μ W) (attachmentOldEmbeddingGraph P) ∧
    MeetEmbeddingCode P (separationTileCarrier P r W) r (separationTileOrder P r μ W)
      μ (separationTileMeet P r μ W) (separationTileMap P r W) :=
  ⟨(separationTileCoding old ⟨W, hW⟩).old_embedding_code,
    (separationTileCoding old ⟨W, hW⟩).template_embedding_code⟩

theorem separationTile_exact_overlap {P r W x y : ZFSet.{u}} (hy : y ∈ P) :
    ZFSet.pair x y ∈ separationTileMap P r W ↔ x ∈ P ∧ ZFSet.pair x W ∈ r ∧ y = x := by
  rw [pair_mem_separationTileMap]
  constructor
  · rintro ⟨hx, h | h⟩
    · exact ⟨hx, h⟩
    · exact False.elim (pair_tag_not_mem P x (h.2 ▸ hy))
  · exact fun ⟨hx, h⟩ => ⟨hx, Or.inl h⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem separationTile_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P r μ W : ZFSet.{u}} (old : MeetOrderCode P r μ)
    (hP : P ∈ M.sets) (hr : r ∈ M.sets) (hμ : μ ∈ M.sets) (hW : W ∈ P) :
    separationTileCarrier P r W ∈ M.sets ∧ separationTileOrder P r μ W ∈ M.sets ∧
      separationTileMeet P r μ W ∈ M.sets ∧ attachmentOldEmbeddingGraph P ∈ M.sets ∧
      separationTileMap P r W ∈ M.sets := by
  have hBase := M.attachmentOldEmbeddingGraph_mem pairing unions powers separation
    (M.attachmentIdeal_mem separation hP hr (M.transitive hP hW))
  exact (separationTileCoding old ⟨W, hW⟩).ground_codes M pairing unions powers separation
    hP hP hr hr hμ hBase

end TransitiveGround

end PartitionPilot.Forcing

end OAI
