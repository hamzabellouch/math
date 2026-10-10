import OAI.SetTheory.PartitionPrinciple.Definability.GroundFlatCopyGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

def quotientBinaryGraph (W Q classifier op : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q,
    z = ZFSet.pair (ZFSet.pair a b) c ∧
      ∃ x ∈ W, ∃ y ∈ W, ∃ t ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧
          ZFSet.pair t c ∈ classifier ∧ ZFSet.pair (ZFSet.pair x y) t ∈ op)
    (ZFSet.prod (ZFSet.prod Q Q) Q)

theorem mem_quotientBinaryGraph (W Q classifier op z : ZFSet.{u}) :
    z ∈ quotientBinaryGraph W Q classifier op ↔
      ∃ a ∈ Q, ∃ b ∈ Q, ∃ c ∈ Q, z = ZFSet.pair (ZFSet.pair a b) c ∧
        ∃ x ∈ W, ∃ y ∈ W, ∃ t ∈ W,
          ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧
            ZFSet.pair t c ∈ classifier ∧ ZFSet.pair (ZFSet.pair x y) t ∈ op := by
  rw [quotientBinaryGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, c, hc, eq, rest⟩
  exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, hc⟩,
    a, ha, b, hb, c, hc, eq, rest⟩

theorem pair_mem_quotientBinaryGraph (W Q classifier op a b c : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair a b) c ∈ quotientBinaryGraph W Q classifier op ↔
      a ∈ Q ∧ b ∈ Q ∧ c ∈ Q ∧ ∃ x ∈ W, ∃ y ∈ W, ∃ t ∈ W,
        ZFSet.pair x a ∈ classifier ∧ ZFSet.pair y b ∈ classifier ∧
          ZFSet.pair t c ∈ classifier ∧ ZFSet.pair (ZFSet.pair x y) t ∈ op := by
  rw [mem_quotientBinaryGraph]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, eq, rest⟩
    obtain ⟨ab, rfl⟩ := ZFSet.pair_inj.1 eq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ab
    exact ⟨ha, hb, hc, rest⟩
  · rintro ⟨ha, hb, hc, rest⟩
    exact ⟨a, ha, b, hb, c, hc, rfl, rest⟩

theorem quotientBinaryGraph_eq_graph {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A → A) (target : B → B → B)
    (onto : Function.Surjective q)
    (compatible : ∀ x y, q (source x y) = target (q x) (q y)) :
    quotientBinaryGraph s.carrier t.carrier (s.graph t q)
      ((s.product s).graph s (fun p => source p.1 p.2)) =
        (t.product t).graph t (fun p => target p.1 p.2) := by
  apply ZFSet.ext
  intro z
  rw [mem_quotientBinaryGraph, Presentation.mem_graph]
  constructor
  · rintro ⟨a, ha, b, hb, c, hc, rfl, x, hx, y, hy, w, hw, xa, yb, wc, op⟩
    obtain ⟨a, rfl⟩ := (t.mem_carrier a).1 ha
    obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
    obtain ⟨c, rfl⟩ := (t.mem_carrier c).1 hc
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨y, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨w, rfl⟩ := (s.mem_carrier w).1 hw
    have first := (s.pair_mem_graph t q x a).1 xa
    have second := (s.pair_mem_graph t q y b).1 yb
    have output := (s.pair_mem_graph t q w c).1 wc
    have value := ((s.product s).pair_mem_graph s (fun p => source p.1 p.2) (x, y) w).1 op
    have equal : target a b = c := by
      rw [← first, ← second, ← compatible, value]
      exact output
    exact ⟨(a, b), by change ZFSet.pair (ZFSet.pair _ _) (t.encode (target a b)) = _; rw [equal]⟩
  · rintro ⟨⟨a, b⟩, rfl⟩
    obtain ⟨x, rfl⟩ := onto a
    obtain ⟨y, rfl⟩ := onto b
    refine ⟨t.encode (q x), t.encode_mem _, t.encode (q y), t.encode_mem _,
      t.encode (target (q x) (q y)), t.encode_mem _, rfl,
      s.encode x, s.encode_mem _, s.encode y, s.encode_mem _,
      s.encode (source x y), s.encode_mem _, ?_, ?_, ?_, ?_⟩
    · exact (s.pair_mem_graph t q _ _).2 rfl
    · exact (s.pair_mem_graph t q _ _).2 rfl
    · exact (s.pair_mem_graph t q _ _).2 (compatible x y)
    · exact ((s.product s).pair_mem_graph s (fun p => source p.1 p.2) (x, y) _).2 rfl

theorem quotientBinaryGraph_function {A B : Type u} (s : Presentation A) (t : Presentation B)
    (q : A → B) (source : A → A → A) (target : B → B → B)
    (onto : Function.Surjective q)
    (compatible : ∀ x y, q (source x y) = target (q x) (q y)) :
    ZFSet.IsFunc (ZFSet.prod t.carrier t.carrier) t.carrier
      (quotientBinaryGraph s.carrier t.carrier (s.graph t q)
        ((s.product s).graph s (fun p => source p.1 p.2))) := by
  rw [quotientBinaryGraph_eq_graph s t q source target onto compatible]
  exact (t.product t).graph_isFunc t _

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def quotientBinaryEntryFormula {n} (z w q classifier op : Fin n) : BoundedFormula n :=
  exMem q (exMem q.succ (exMem q.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
      (exMem w.succ.succ.succ (exMem w.succ.succ.succ.succ
        (exMem w.succ.succ.succ.succ.succ
          (.conj (pairMembershipFormula 2 5 classifier.succ.succ.succ.succ.succ.succ)
            (.conj (pairMembershipFormula 1 4 classifier.succ.succ.succ.succ.succ.succ)
              (.conj (pairMembershipFormula 0 3 classifier.succ.succ.succ.succ.succ.succ)
                (tripleMembershipFormula 2 1 0 op.succ.succ.succ.succ.succ.succ))))))))))

theorem truth_quotientBinaryEntryFormula {n} (z w q classifier op : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (quotientBinaryEntryFormula z w q classifier op) env ↔
      env z ∈ quotientBinaryGraph (env w) (env q) (env classifier) (env op) := by
  simp only [quotientBinaryEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, mem_quotientBinaryGraph]
  rfl

end BoundedFormula

namespace TransitiveGround

theorem quotientBinaryGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W Q classifier op : ZFSet.{u}} (hW : W ∈ M.sets) (hQ : Q ∈ M.sets)
    (hc : classifier ∈ M.sets) (ho : op ∈ M.sets) :
    quotientBinaryGraph W Q classifier op ∈ M.sets := by
  have bound := M.prod_mem pairing unions powers separation
    (M.prod_mem pairing unions powers separation hQ hQ) hQ
  let params := extend W (extend Q (extend classifier (extend op Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.quotientBinaryEntryFormula 0 1 2 3 4) params
    (Fin.cases hW (Fin.cases hQ (Fin.cases hc (Fin.cases ho (fun i => Fin.elim0 i))))) bound
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.quotientBinaryEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod (ZFSet.prod Q Q) Q) = quotientBinaryGraph W Q classifier op := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_quotientBinaryEntryFormula]
    change (z ∈ ZFSet.prod (ZFSet.prod Q Q) Q ∧ z ∈ quotientBinaryGraph W Q classifier op) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
