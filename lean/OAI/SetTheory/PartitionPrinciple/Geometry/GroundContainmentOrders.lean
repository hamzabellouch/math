import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompleteProjectionGenericity

namespace OAI

section

namespace PartitionPilot.Forcing.PartialOrderCode

open SetRealization
universe u
variable {Q R : ZFSet.{u}} (h : PartialOrderCode Q R)

@[instance_reducible]
noncomputable def toPartialOrder : PartialOrder (SetMembers Q) where
  le x y := ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) ∈ R
  le_refl x := h.refl _ (SetMembers.raw_mem x)
  le_trans x y z xy yz := h.trans _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y)
    _ (SetMembers.raw_mem z) xy yz
  le_antisymm x y xy yx := SetMembers.raw_injective Q
    (h.antisymm _ (SetMembers.raw_mem x) _ (SetMembers.raw_mem y) xy yx)

theorem conditionOrder_eq :
    letI _decodedOrder := h.toPartialOrder
    (SetMembers.presentation Q).conditionOrder = R := by
  let decodedOrder := h.toPartialOrder
  apply ZFSet.ext
  intro z
  rw [Presentation.conditionOrder, Presentation.mem_subset]
  constructor
  · rintro ⟨⟨x, y⟩, le, eq⟩
    change ZFSet.pair (SetMembers.raw x) (SetMembers.raw y) = z at eq
    exact eq ▸ le
  · intro hz
    obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 (h.relation hz)
    refine ⟨(SetMembers.ofMem x hx, SetMembers.ofMem y hy), ?_, ?_⟩
    · change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx))
        (SetMembers.raw (SetMembers.ofMem y hy)) ∈ R
      rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem, ← eq]
      exact hz
    · change ZFSet.pair (SetMembers.raw (SetMembers.ofMem x hx))
        (SetMembers.raw (SetMembers.ofMem y hy)) = z
      rw [SetMembers.raw_ofMem, SetMembers.raw_ofMem]
      exact eq.symm

@[instance_reducible]
noncomputable def toOrderTop (one : ZFSet.{u}) (hone : one ∈ Q)
    (greatest : ∀ x ∈ Q, ZFSet.pair x one ∈ R) :
    letI _decodedOrder := h.toPartialOrder
    OrderTop (SetMembers Q) := by
  letI decodedOrder := h.toPartialOrder
  refine { top := SetMembers.ofMem one hone, le_top := ?_ }
  intro x
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem one hone)) ∈ R
  rw [SetMembers.raw_ofMem]
  exact greatest _ (SetMembers.raw_mem x)

end PartitionPilot.Forcing.PartialOrderCode

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem decoded_order_mem {Q R : ZFSet.{u}} (h : PartialOrderCode Q R) (hR : R ∈ M.sets) :
    letI _decodedOrder := h.toPartialOrder
    (SetMembers.presentation Q).conditionOrder ∈ M.sets := by
  let decodedOrder := h.toPartialOrder
  rw [h.conditionOrder_eq]
  exact hR

theorem exists_decoded_generic (small : M.sets.Countable)
    {Q R : ZFSet.{u}} (hQ : Q ∈ M.sets) (hR : R ∈ M.sets)
    (laws : Realize M.sets (BoundedFormula.partialOrderFormula 0 1).toFormula
      (extend Q (extend R Fin.elim0))) (p : SetMembers Q) :
    letI _decodedOrder := ((M.realize_partialOrderCode hQ hR).1 laws).toPartialOrder
    ∃ H : ConditionFilter (SetMembers Q), H.mem p ∧
      H.GenericFor (M.codedFamily (SetMembers.presentation Q)) ∧
      H.GenericFor (formulaFamily (M.nameDomain (SetMembers.presentation Q))) := by
  let h := (M.realize_partialOrderCode hQ hR).1 laws
  let decodedOrder := h.toPartialOrder
  let decodedCountable := M.setMembers_countable small hQ
  let s := SetMembers.presentation Q
  have ordinary := formulaFamily_countable (M.nameDomain s) (M.nameDomain_countable s small)
  obtain ⟨H, hp, generic⟩ := exists_generic_for_countable_family p
    (M.codedFamily s ∪ formulaFamily (M.nameDomain s)) ((M.codedFamily_countable s small).union ordinary)
  exact ⟨H, hp, (fun E hE => generic E (Or.inl hE)), fun E hE => generic E (Or.inr hE)⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

universe u

noncomputable def reverseInclusionCode (Q : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ Q, ∃ q ∈ Q, z = ZFSet.pair p q ∧ q ⊆ p) (ZFSet.prod Q Q)

theorem mem_reverseInclusionCode (Q z : ZFSet.{u}) :
    z ∈ reverseInclusionCode Q ↔ ∃ p ∈ Q, ∃ q ∈ Q, z = ZFSet.pair p q ∧ q ⊆ p := by
  rw [reverseInclusionCode, ZFSet.mem_sep]
  exact ⟨And.right, fun ⟨p, hp, q, hq, eq, subset⟩ =>
    ⟨ZFSet.mem_prod.2 ⟨p, hp, q, hq, eq⟩, p, hp, q, hq, eq, subset⟩⟩

theorem pair_mem_reverseInclusionCode (Q p q : ZFSet.{u}) :
    ZFSet.pair p q ∈ reverseInclusionCode Q ↔ p ∈ Q ∧ q ∈ Q ∧ q ⊆ p := by
  rw [mem_reverseInclusionCode]
  constructor
  · rintro ⟨a, ha, b, hb, eq, subset⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, subset⟩
  · rintro ⟨hp, hq, subset⟩
    exact ⟨p, hp, q, hq, rfl, subset⟩

theorem reverseInclusion_partialOrder (Q : ZFSet.{u}) : PartialOrderCode Q (reverseInclusionCode Q) where
  relation := fun _ hz => (ZFSet.mem_sep.1 hz).1
  refl p hp := (pair_mem_reverseInclusionCode Q p p).2 ⟨hp, hp, fun _ hx => hx⟩
  antisymm p _ q _ pq qp := ZFSet.ext (fun _ =>
    ⟨fun hz => ((pair_mem_reverseInclusionCode Q q p).1 qp).2.2 hz,
      fun hz => ((pair_mem_reverseInclusionCode Q p q).1 pq).2.2 hz⟩)
  trans p hp q _ r hr pq qr := (pair_mem_reverseInclusionCode Q p r).2 ⟨hp, hr,
    fun _ hx => ((pair_mem_reverseInclusionCode Q p q).1 pq).2.2
      (((pair_mem_reverseInclusionCode Q q r).1 qr).2.2 hx)⟩

theorem reverseInclusion_empty_top {Q : ZFSet.{u}} (empty : (∅ : ZFSet.{u}) ∈ Q) :
    ∀ p ∈ Q, ZFSet.pair p ∅ ∈ reverseInclusionCode Q :=
  fun p hp => (pair_mem_reverseInclusionCode Q p ∅).2 ⟨hp, empty, ZFSet.empty_subset p⟩

namespace BoundedFormula

open SetFormula

def subsetFormula {n} (a b : Fin n) : BoundedFormula n := .allMem a (.mem 0 b.succ)

def reverseInclusionEntryFormula {n} (z q : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (.conj (orderedPairFormula z.succ.succ 1 0) (subsetFormula 0 1)))

theorem truth_subsetFormula {n} (a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (subsetFormula a b) env ↔ env a ⊆ env b := Iff.rfl

theorem truth_reverseInclusionEntryFormula {n} (z q : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (reverseInclusionEntryFormula z q) env ↔ env z ∈ reverseInclusionCode (env q) := by
  simp only [reverseInclusionEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_subsetFormula]
  exact (mem_reverseInclusionCode (env q) (env z)).symm

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem reverseInclusionCode_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {Q : ZFSet.{u}} (hQ : Q ∈ M.sets) : reverseInclusionCode Q ∈ M.sets := by
  have pairs := M.prod_mem pairing unions powers separation hQ hQ
  let params := extend Q Fin.elim0
  have selected := M.separation_mem separation (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula
    params (Fin.cases hQ (fun j => Fin.elim0 j)) pairs
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula (extend z params) ↔
        z ∈ reverseInclusionCode Q :=
    (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz (Fin.cases hQ (fun j => Fin.elim0 j)))).trans
      (BoundedFormula.truth_reverseInclusionEntryFormula 0 1 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.reverseInclusionEntryFormula 0 1).toFormula (extend z params)) (ZFSet.prod Q Q) =
        reverseInclusionCode Q := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive pairs hz)).1 rel
    · intro hz
      have hzP := (reverseInclusion_partialOrder Q).relation hz
      exact ⟨hzP, (correct z (M.transitive pairs hzP)).2 hz⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
