import OAI.SetTheory.PartitionPrinciple.Definability.GroundSelectedSupportTupleFamilies
import OAI.SetTheory.PartitionPrinciple.Forcing.RenamedPairNameFamilies
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundCountableProducts

namespace OAI

open scoped ZFSet

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def pairedGraph (L H K f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ L, ∃ a ∈ H, ∃ b ∈ K,
    z = ZFSet.pair x (ZFSet.pair a b) ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g)
    (ZFSet.prod L (ZFSet.prod H K))

theorem mem_pairedGraph (L H K f g z : ZFSet.{u}) : z ∈ pairedGraph L H K f g ↔
    ∃ x ∈ L, ∃ a ∈ H, ∃ b ∈ K,
      z = ZFSet.pair x (ZFSet.pair a b) ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g := by
  constructor
  · exact fun hz => (ZFSet.mem_sep.1 hz).2
  · rintro ⟨x, hx, a, ha, b, hb, rfl, first, second⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.pair_mem_prod.2 ⟨ha, hb⟩⟩,
      x, hx, a, ha, b, hb, rfl, first, second⟩

theorem pair_mem_pairedGraph (L H K f g x a b : ZFSet.{u}) :
    ZFSet.pair x (ZFSet.pair a b) ∈ pairedGraph L H K f g ↔
      x ∈ L ∧ a ∈ H ∧ b ∈ K ∧ ZFSet.pair x a ∈ f ∧ ZFSet.pair x b ∈ g := by
  rw [mem_pairedGraph]
  constructor
  · rintro ⟨x', hx, a', ha, b', hb, equal, first, second⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    subst x'
    exact ⟨hx, ha, hb, first, second⟩
  · rintro ⟨hx, ha, hb, first, second⟩
    exact ⟨x, hx, a, ha, b, hb, rfl, first, second⟩

theorem pairedGraph_eq {A B C : Type u} (s : Presentation A) (t : Presentation B)
    (v : Presentation C) (f : A → B) (g : A → C) :
    pairedGraph s.carrier t.carrier v.carrier (s.graph t f) (s.graph v g) =
      s.graph (t.product v) (fun x => (f x, g x)) := by
  apply ZFSet.ext
  intro z
  rw [mem_pairedGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨x, hx, a, ha, b, hb, rfl, first, second⟩
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (v.mem_carrier b).1 hb
    have fa := (s.pair_mem_graph t f x a).1 first
    have gb := (s.pair_mem_graph v g x b).1 second
    exact ⟨x, congrArg (ZFSet.pair (s.encode x)) (congrArg₂ ZFSet.pair (congrArg t.encode fa) (congrArg v.encode gb))⟩
  · rintro ⟨x, rfl⟩
    exact ⟨s.encode x, s.encode_mem x, t.encode (f x), t.encode_mem _, v.encode (g x), v.encode_mem _, rfl,
      (s.pair_mem_graph t f _ _).2 rfl, (s.pair_mem_graph v g _ _).2 rfl⟩

namespace BoundedFormula

def pairedGraphEntryFormula {n} (z L H K f g : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ
  exMem L (exMem H.succ (exMem K.succ.succ
    (.conj (orderedRightTripleFormula (lift z) 2 1 0)
      (.conj (pairMembershipFormula 2 1 (lift f)) (pairMembershipFormula 2 0 (lift g))))))

theorem truth_pairedGraphEntryFormula {n} (z L H K f g : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (pairedGraphEntryFormula z L H K f g) env ↔
      env z ∈ pairedGraph (env L) (env H) (env K) (env f) (env g) := by
  simp only [pairedGraphEntryFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, mem_pairedGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem pairedGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L H K f g : ZFSet.{u}} (hL : L ∈ M.sets) (hH : H ∈ M.sets) (hK : K ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets) : pairedGraph L H K f g ∈ M.sets := by
  let params := extend L (extend H (extend K (extend f (extend g Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairedGraphEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hL (Fin.cases hH (Fin.cases hK (Fin.cases hf (Fin.cases hg (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hL (M.prod_mem pairing unions powers separation hH hK))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.pairedGraphEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod L (ZFSet.prod H K)) = pairedGraph L H K f g := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_pairedGraphEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

section

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P Q : Type u}

theorem recode_subset (s t : Presentation P) (predicate : P → Prop) :
    relationImage (s.subset predicate) t.carrier (s.graph t id) = t.subset predicate := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, t.mem_subset]
  constructor
  · rintro ⟨hy, x, hx, entry⟩
    obtain ⟨p, hp, rfl⟩ := (s.mem_subset predicate x).1 hx
    obtain ⟨q, rfl⟩ := (t.mem_carrier y).1 hy
    have equal := (s.pair_mem_graph t id p q).1 entry
    exact ⟨p, hp, congrArg t.encode equal⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨t.encode_mem p, s.encode p, (s.encode_mem_subset predicate p).2 hp,
      (s.pair_mem_graph t id p p).2 rfl⟩

theorem product_identity_graph (s t : Presentation P) (v w : Presentation Q) :
    (s.product v).graph (t.product w) id =
      relationProduct s.carrier v.carrier t.carrier w.carrier (s.graph t id) (v.graph w id) := by
  apply ZFSet.ext
  intro z
  rw [(s.product v).mem_graph, mem_relationProduct]
  constructor
  · rintro ⟨⟨p, q⟩, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, v.encode q, v.encode_mem q,
      t.encode p, t.encode_mem p, w.encode q, w.encode_mem q, rfl,
      (s.pair_mem_graph t id p p).2 rfl, (v.pair_mem_graph w id q q).2 rfl⟩
  · rintro ⟨x, hx, y, hy, x', hx', y', hy', rfl, first, second⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (v.mem_carrier y).1 hy
    obtain ⟨p', rfl⟩ := (t.mem_carrier x').1 hx'
    obtain ⟨q', rfl⟩ := (w.mem_carrier y').1 hy'
    have ep := (s.pair_mem_graph t id p p').1 first
    have eq := (v.pair_mem_graph w id q q').1 second
    change p = p' at ep
    change q = q' at eq
    subst p'
    subst q'
    exact ⟨(p, q), rfl⟩

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {P Q : Type u}

include separation in
theorem recode_subset_mem (s t : Presentation P) (predicate : P → Prop)
    (ht : t.carrier ∈ M.sets) (graph : s.graph t id ∈ M.sets)
    (subset : s.subset predicate ∈ M.sets) : t.subset predicate ∈ M.sets := by
  rw [← s.recode_subset t predicate]
  exact M.relationImage_mem separation subset ht graph

include pairing unions powers separation

theorem product_identity_graph_mem (s t : Presentation P) (v w : Presentation Q)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (hv : v.carrier ∈ M.sets) (hw : w.carrier ∈ M.sets)
    (first : s.graph t id ∈ M.sets) (second : v.graph w id ∈ M.sets) :
    (s.product v).graph (t.product w) id ∈ M.sets := by
  rw [s.product_identity_graph t v w]
  exact M.relationProduct_mem pairing unions powers separation hs hv ht hw first second

theorem recode_conditionOrder_mem [Preorder P] (s t : Presentation P)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (graph : s.graph t id ∈ M.sets) (order : s.conditionOrder ∈ M.sets) :
    t.conditionOrder ∈ M.sets :=
  M.recode_subset_mem separation (s.product s) (t.product t) (fun pq => pq.1 ≤ pq.2)
    (M.prod_mem pairing unions powers separation ht ht)
    (M.product_identity_graph_mem pairing unions powers separation s t s t hs ht hs ht graph graph) order

theorem recode_actionGraph_mem {G : Type u} [Group G] [PartialOrder P]
    (a : PosetAction G P) (s t : Presentation P) (b : Presentation G)
    (hs : s.carrier ∈ M.sets) (ht : t.carrier ∈ M.sets)
    (hb : b.carrier ∈ M.sets) (graph : s.graph t id ∈ M.sets)
    (identity : b.graph b id ∈ M.sets) (action : a.actionGraph s b ∈ M.sets) :
    a.actionGraph t b ∈ M.sets := by
  apply M.recode_subset_mem separation ((b.product s).product s) ((b.product t).product t)
    (fun gpq => a.iso gpq.1.1 gpq.1.2 = gpq.2)
  · exact M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hb ht) ht
  · exact M.product_identity_graph_mem pairing unions powers separation (b.product s) (b.product t) s t
      (M.prod_mem pairing unions powers separation hb hs)
      (M.prod_mem pairing unions powers separation hb ht) hs ht
      (M.product_identity_graph_mem pairing unions powers separation b b s t hb hb hs ht identity graph) graph
  · exact action

end PartitionPilot.Forcing.TransitiveGround

end

namespace PartitionPilot.SetRealization.Presentation
open Forcing
universe u
variable {P : Type u} (s : Presentation P)

noncomputable def pairEmpty : Presentation P where
  carrier := ZFSet.prod s.carrier {∅}
  encode p := ZFSet.pair (s.encode p) ∅
  injective := fun _ _ eq => s.injective (ZFSet.pair_inj.1 eq).1
  mem_carrier z := by
    rw [ZFSet.mem_prod]
    constructor
    · rintro ⟨x, hx, y, hy, eq⟩
      have empty : y = ∅ := ZFSet.mem_singleton.1 hy
      obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
      exact ⟨p, by rw [empty] at eq; exact eq.symm⟩
    · rintro ⟨p, rfl⟩
      exact ⟨s.encode p, s.encode_mem p, ∅, ZFSet.mem_singleton.2 rfl, rfl⟩

theorem pairEmpty_forwardGraph :
    s.graph s.pairEmpty id = pairedGraph s.carrier s.carrier {∅}
      (identityFunctionGraph s.carrier) (constantFamilyGraph s.carrier ∅) := by
  apply ZFSet.ext
  intro z
  rw [s.mem_graph, mem_pairedGraph]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, s.encode p, s.encode_mem p,
      ∅, ZFSet.mem_singleton.2 rfl, rfl,
      (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, s.encode_mem p⟩,
      (pair_mem_constantFamilyGraph _ _ _ _).2 ⟨s.encode_mem p, rfl⟩⟩
  · rintro ⟨x, hx, y, _, e, _, rfl, identity, constant⟩
    have xy := ((pair_mem_identityFunctionGraph _ _ _).1 identity).1
    have empty := ((pair_mem_constantFamilyGraph _ _ _ _).1 constant).2
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    subst y
    subst e
    exact ⟨p, rfl⟩

theorem pairEmpty_inverseGraph :
    s.pairEmpty.graph s id = relationConverse s.carrier s.pairEmpty.carrier (s.graph s.pairEmpty id) := by
  apply ZFSet.ext
  intro z
  rw [s.pairEmpty.mem_graph, mem_relationConverse]
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨s.encode p, s.encode_mem p, s.pairEmpty.encode p, s.pairEmpty.encode_mem p, rfl,
      (s.pair_mem_graph s.pairEmpty id p p).2 rfl⟩
  · rintro ⟨x, hx, y, hy, rfl, entry⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨q, rfl⟩ := (s.pairEmpty.mem_carrier y).1 hy
    have eq := (s.pair_mem_graph s.pairEmpty id p q).1 entry
    change p = q at eq
    subst q
    exact ⟨p, rfl⟩

theorem pairEmpty_order_iff [Preorder P] (p q : P) :
    ZFSet.pair (ZFSet.pair (s.encode p) ∅) (ZFSet.pair (s.encode q) ∅) ∈
      s.pairEmpty.conditionOrder ↔ p ≤ q := s.pairEmpty.pair_mem_conditionOrder p q

end PartitionPilot.SetRealization.Presentation

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {P : Type u} (s : Presentation P)
include pairing unions powers separation

theorem pairEmpty_carrier_mem (hs : s.carrier ∈ M.sets) : s.pairEmpty.carrier ∈ M.sets := by
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.prod_mem pairing unions powers separation hs single

theorem pairEmpty_forwardGraph_mem (hs : s.carrier ∈ M.sets) : s.graph s.pairEmpty id ∈ M.sets := by
  rw [s.pairEmpty_forwardGraph]
  have empty := M.empty_mem ⟨s.carrier, hs⟩
  have single : ({∅} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing empty empty
  exact M.pairedGraph_mem pairing unions powers separation hs hs single
    (M.identityFunctionGraph_mem pairing unions powers separation hs)
    (M.constantFamilyGraph_mem pairing unions powers separation hs empty)

theorem pairEmpty_inverseGraph_mem (hs : s.carrier ∈ M.sets) : s.pairEmpty.graph s id ∈ M.sets := by
  rw [s.pairEmpty_inverseGraph]
  exact M.relationConverse_mem pairing unions powers separation hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs)
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs)

theorem pairEmpty_order_mem [Preorder P] (hs : s.carrier ∈ M.sets)
    (order : s.conditionOrder ∈ M.sets) : s.pairEmpty.conditionOrder ∈ M.sets :=
  M.recode_conditionOrder_mem pairing unions powers separation s s.pairEmpty hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs)
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs) order

theorem pairEmpty_actionGraph_mem {G : Type u} [Group G] [PartialOrder P]
    (a : PosetAction G P) (b : Presentation G)
    (hs : s.carrier ∈ M.sets) (hb : b.carrier ∈ M.sets)
    (action : a.actionGraph s b ∈ M.sets) : a.actionGraph s.pairEmpty b ∈ M.sets := by
  have identity : b.graph b id = identityFunctionGraph b.carrier := by
    apply ZFSet.ext
    intro z
    rw [b.mem_graph, mem_identityFunctionGraph]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨b.encode g, b.encode_mem g, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨g, rfl⟩ := (b.mem_carrier x).1 hx
      exact ⟨g, rfl⟩
  exact M.recode_actionGraph_mem pairing unions powers separation a s s.pairEmpty b hs
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs) hb
    (M.pairEmpty_forwardGraph_mem pairing unions powers separation s hs)
    (identity ▸ M.identityFunctionGraph_mem pairing unions powers separation hb) action

theorem pairEmpty_conditionMapFamily_mem {G : Type u} [Group G] [PartialOrder P]
    (a : PosetAction G P) (b : Presentation G) (collection : CollectionSchema M.sets)
    (hs : s.carrier ∈ M.sets) (hb : b.carrier ∈ M.sets)
    (action : a.actionGraph s b ∈ M.sets) : a.conditionMapFamily s.pairEmpty b ∈ M.sets :=
  M.conditionMapFamily_mem_of_actionGraph a s.pairEmpty b pairing unions powers separation collection
    (M.pairEmpty_carrier_mem pairing unions powers separation s hs) hb
    (M.pairEmpty_actionGraph_mem pairing unions powers separation s a b hs hb action)

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
variable {P : Type u} (c : Presentation P)
variable (one mu I W rows S : ZFSet.{u})
variable (valid : ∀ z ∈ (rowTupleTerms one mu I W rows S), IsName c z)

noncomputable def liftedRowTupleFamily (valid : ∀ z ∈ rowTupleTerms one mu I W rows S, IsName c z) : ZFSet.{u} :=
  relationCompose S (rowTupleTerms one mu I W rows S)
    (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid)
    (rowTupleFamily one mu I W rows S)
    (Name.renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid)

include valid

theorem pair_mem_liftedRowTupleFamily (f z : ZFSet.{u}) :
    ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) ↔
      f ∈ S ∧ ∃ τ : Name c, τ.val = rowTupleCode one mu I W rows f ∧
        z = (Name.rename c.pairEmpty id τ).val := by
  rw [liftedRowTupleFamily, pair_mem_relationCompose]
  constructor
  · rintro ⟨hf, _, x, hx, tuple, rename⟩
    let τ : Name c := ⟨x, valid x hx⟩
    exact ⟨hf, τ, ((pair_mem_rowTupleFamily one mu I W rows S f x).1 tuple).2,
      ((Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).1 rename).2⟩
  · rintro ⟨hf, τ, tuple, equal⟩
    have member : τ.val ∈ (rowTupleTerms one mu I W rows S) := (mem_rowTupleTerms one mu I W rows S τ.val).2 ⟨f, hf, tuple⟩
    have target : z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).2
      ⟨τ, member, equal⟩
    exact ⟨hf, target, τ.val, member,
      (pair_mem_rowTupleFamily one mu I W rows S f τ.val).2 ⟨hf, tuple⟩,
      (Name.pair_mem_renameFamilyGraph c.pairEmpty id (rowTupleTerms one mu I W rows S) valid τ z).2 ⟨member, equal⟩⟩

theorem liftedRowTupleFamily_function : ZFSet.IsFunc S (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) (liftedRowTupleFamily c one mu I W rows S valid) :=
  relationCompose_function_of_subset (rowTupleTerms_function one mu I W rows S)
    (Name.renameFamilyGraph_function c.pairEmpty id (rowTupleTerms one mu I W rows S) valid) (fun _ h => h)

theorem liftedRowTupleFamily_surjective :
    ∀ z ∈ (Name.renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid), ∃ f ∈ S, ZFSet.pair f z ∈ (liftedRowTupleFamily c one mu I W rows S valid) := by
  intro z hz
  obtain ⟨τ, member, equal⟩ := (Name.mem_renamedFamily c.pairEmpty id (rowTupleTerms one mu I W rows S) valid z).1 hz
  obtain ⟨f, hf, tuple⟩ := (mem_rowTupleTerms one mu I W rows S τ.val).1 member
  exact ⟨f, hf, (pair_mem_liftedRowTupleFamily c one mu I W rows S valid f z).2
    ⟨hf, τ, tuple, equal⟩⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem liftedRowTupleFamily_mem (carrier : c.carrier ∈ M.sets)
    (hone : one ∈ M.sets) (hmu : mu ∈ M.sets) (hI : I ∈ M.sets)
    (hW : W ∈ M.sets) (hrows : rows ∈ M.sets) (hS : S ∈ M.sets) :
    (liftedRowTupleFamily c one mu I W rows S valid) ∈ M.sets := by
  have tuples := M.rowTupleFamily_mem pairing unions powers separation collection hone hmu hI hW hrows hS
  have terms := M.rowTupleTerms_mem unions separation hS tuples
  have target := M.pairEmpty_carrier_mem pairing unions powers separation c carrier
  have forward := M.pairEmpty_forwardGraph_mem pairing unions powers separation c carrier
  have rename := M.renameFamilyGraph_mem c c.pairEmpty pairing unions powers separation collection
    carrier target id forward (rowTupleTerms one mu I W rows S) terms valid
  have liftedGround := M.renamedFamily_mem c c.pairEmpty pairing unions powers separation collection
    carrier target id forward (rowTupleTerms one mu I W rows S) terms valid
  exact M.relationCompose_mem pairing unions powers separation hS terms liftedGround tuples rename

omit c one mu I W rows S valid in
theorem binaryLiftedRowTupleFamily_mem (infinite : Realize M.sets infinity Fin.elim0)
    {L r I C mu : ZFSet.{u}} (hL : L ∈ M.sets) (hr : r ∈ M.sets)
    (hI : I ∈ M.sets) (hC : C ∈ M.sets) (hmu : mu ∈ M.sets)
    (one : SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) :
    let c := SetMembers.presentation (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph I C one
    let S := M.rowPositionSequences L r I mu
    ∀ valid : ∀ z ∈ rowTupleTerms (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S, IsName c z,
      liftedRowTupleFamily c (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S valid ∈ M.sets := by
  intro c rows S valid
  have carrier := M.countablePartialFunctions_mem pairing unions powers separation infinite
    (M.prod_mem pairing unions powers separation hI hC) (M.natSetCode_mem separation infinite 2)
  have groundRows := M.binaryRowNameGraph_mem pairing unions powers separation collection infinite hI hC one
  exact liftedRowTupleFamily_mem c (SetMembers.raw one) mu I (⋃₀ ⋃₀ rows) rows S valid M
    pairing unions powers separation collection carrier (M.transitive carrier (SetMembers.raw_mem one))
    hmu hI (M.union_mem unions (M.union_mem unions groundRows)) groundRows
    (M.rowPositionSequences_mem pairing unions powers separation hL hr hI hmu)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
