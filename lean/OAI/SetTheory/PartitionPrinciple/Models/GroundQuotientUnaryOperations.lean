import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

def quotientUnaryGraph (W Q classifier op : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
    ∃ x ∈ W, ∃ y ∈ W, ZFSet.pair x a ∈ classifier ∧
      ZFSet.pair y b ∈ classifier ∧ ZFSet.pair x y ∈ op) (ZFSet.prod Q Q)

theorem mem_quotientUnaryGraph (W Q classifier op z : ZFSet.{u}) :
    z ∈ quotientUnaryGraph W Q classifier op ↔
      ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧ ∃ x ∈ W, ∃ y ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧ ZFSet.pair x y ∈ op := by
  rw [quotientUnaryGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, eq, rest⟩
  exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, eq, rest⟩

theorem pair_mem_quotientUnaryGraph (W Q classifier op a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ quotientUnaryGraph W Q classifier op ↔
      a ∈ Q ∧ b ∈ Q ∧ ∃ x ∈ W, ∃ y ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧ ZFSet.pair x y ∈ op := by
  rw [mem_quotientUnaryGraph]
  constructor
  · rintro ⟨a', ha, b', hb, eq, rest⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, rest⟩
  · rintro ⟨ha, hb, rest⟩
    exact ⟨a, ha, b, hb, rfl, rest⟩

theorem quotientUnaryGraph_eq_graph {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A) (target : B → B)
    (onto : Function.Surjective q) (compatible : ∀ x, q (source x) = target (q x)) :
    quotientUnaryGraph s.carrier t.carrier (s.graph t q) (s.graph s source) = t.graph t target := by
  apply ZFSet.ext
  intro z
  rw [mem_quotientUnaryGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨a, ha, b, hb, rfl, x, hx, y, hy, xa, yb, op⟩
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    have first := (s.pair_mem_graph t q x a).1 xa
    have output := (s.pair_mem_graph t q y b).1 yb
    have value := (s.pair_mem_graph s source x y).1 op
    have equal : target a = b := by
      rw [← first, ← compatible, value]
      exact output
    exact ⟨a, by rw [equal]⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨x, rfl⟩ := onto a
    exact ⟨t.encode (q x), t.encode_mem _, t.encode (target (q x)), t.encode_mem _, rfl,
      s.encode x, s.encode_mem _, s.encode (source x), s.encode_mem _,
      (s.pair_mem_graph t q _ _).2 rfl, (s.pair_mem_graph t q _ _).2 (compatible x),
      (s.pair_mem_graph s source _ _).2 rfl⟩

theorem quotientUnaryGraph_function {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A) (target : B → B)
    (onto : Function.Surjective q) (compatible : ∀ x, q (source x) = target (q x)) :
    ZFSet.IsFunc t.carrier t.carrier
      (quotientUnaryGraph s.carrier t.carrier (s.graph t q) (s.graph s source)) := by
  rw [quotientUnaryGraph_eq_graph s t q source target onto compatible]
  exact t.graph_isFunc t target

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def quotientUnaryEntryFormula {n} (z w q classifier op : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem w.succ.succ (exMem w.succ.succ.succ
      (.conj (pairMembershipFormula 1 3 classifier.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 0 2 classifier.succ.succ.succ.succ)
          (pairMembershipFormula 1 0 op.succ.succ.succ.succ)))))))

theorem truth_quotientUnaryEntryFormula {n} (z w q classifier op : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (quotientUnaryEntryFormula z w q classifier op) env ↔
      env z ∈ quotientUnaryGraph (env w) (env q) (env classifier) (env op) := by
  simp only [quotientUnaryEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, mem_quotientUnaryGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem quotientUnaryGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W Q classifier op : ZFSet.{u}} (hW : W ∈ M.sets) (hQ : Q ∈ M.sets)
    (hc : classifier ∈ M.sets) (ho : op ∈ M.sets) :
    quotientUnaryGraph W Q classifier op ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation hQ hQ
  let params := extend W (extend Q (extend classifier (extend op Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.quotientUnaryEntryFormula 0 1 2 3 4) params
    (Fin.cases hW (Fin.cases hQ (Fin.cases hc (Fin.cases ho (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.quotientUnaryEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod Q Q) = quotientUnaryGraph W Q classifier op := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_quotientUnaryEntryFormula]
    change (z ∈ ZFSet.prod Q Q ∧ z ∈ quotientUnaryGraph W Q classifier op) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
