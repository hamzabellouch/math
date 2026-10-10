import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

def natIterate {B : Type u} (f : B → B) (b : B) : Nat → B
  | 0 => b
  | n + 1 => f (natIterate f b n)

structure IterationTraceCode (N D B step base t : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc D B t
  seed : ZFSet.pair ∅ base ∈ t
  next : ∀ i ∈ N, ∀ j ∈ D, ∀ x ∈ B, ∀ y ∈ B,
    j = insert i i → ZFSet.pair i x ∈ t → ZFSet.pair j y ∈ t → ZFSet.pair x y ∈ step

noncomputable def finiteIterationTrace {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n : Nat) : ZFSet.{u} :=
  (natInitialPresentation (n + 1)).graph s (fun i => natIterate f b i.down.val)

theorem pair_mem_finiteIterationTrace {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n k : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) y ∈ finiteIterationTrace s f b n ↔
      k ≤ n ∧ y = s.encode (natIterate f b k) := by
  rw [finiteIterationTrace, Presentation.mem_graph]
  constructor
  · rintro ⟨i, eq⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    have same : i.down.val = k := natSetCode_injective first
    exact ⟨by have := i.down.isLt; omega, by simpa only [same] using second.symm⟩
  · rintro ⟨hk, rfl⟩
    exact ⟨⟨⟨k, by omega⟩⟩, rfl⟩

theorem finiteIterationTrace_code {B : Type u} (s : Presentation B) (f : B → B)
    (b : B) (n : Nat) :
    IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) (finiteIterationTrace s f b n) := by
  refine ⟨(natInitialPresentation (n + 1)).graph_isFunc s _, ?_, ?_⟩
  · exact (pair_mem_finiteIterationTrace s f b n 0 _).2 ⟨Nat.zero_le _, rfl⟩
  · intro i hi j _ x _ y _ successor prev next
    obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i n).1 hi
    have previous := ((pair_mem_finiteIterationTrace s f b n k x).1 prev).2
    have jcode : j = natSetCode (k + 1) := successor
    have following := ((pair_mem_finiteIterationTrace s f b n (k + 1) y).1 (jcode ▸ next)).2
    rw [previous, following]
    exact (s.pair_mem_graph s f _ _).2 rfl

theorem IterationTraceCode.value {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    {n : Nat} {t : ZFSet.{u}}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) t) :
    ∀ k ≤ n, ZFSet.pair (natSetCode k) (s.encode (natIterate f b k)) ∈ t := by
  intro k
  induction k with
  | zero => exact fun _ => trace.seed
  | succ k ih =>
    intro hk
    have domain := (natSetCode_mem_iff (k + 1) (n + 1)).2 (by omega)
    obtain ⟨y, rel, _⟩ := trace.function.2 (natSetCode (k + 1)) domain
    have hy := (ZFSet.pair_mem_prod.1 (trace.function.1 rel)).2
    obtain ⟨c, eq⟩ := (s.mem_carrier y).1 hy
    have step := trace.next (natSetCode k) ((natSetCode_mem_iff k n).2 (by omega))
      (natSetCode (k + 1)) domain _ (s.encode_mem _) y hy rfl (ih (by omega)) rel
    rw [← eq] at step
    have output := (s.pair_mem_graph s f _ c).1 step
    have same : y = s.encode (natIterate f b (k + 1)) := eq.symm.trans (congrArg s.encode output.symm)
    exact same ▸ rel

theorem IterationTraceCode.output {B : Type u} (s : Presentation B) (f : B → B) (b : B)
    {n : Nat} {t y : ZFSet.{u}}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier
      (s.graph s f) (s.encode b) t) (rel : ZFSet.pair (natSetCode n) y ∈ t) :
    y = s.encode (natIterate f b n) := by
  obtain ⟨z, _, unique⟩ := trace.function.2 (natSetCode n)
    ((natSetCode_mem_iff n (n + 1)).2 (by omega))
  exact (unique y rel).trans (unique _ (trace.value s f b n (Nat.le_refl n))).symm

namespace TransitiveGround

open SetFormula

theorem finiteIterationTrace_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (f : B → B) (b : B) (n : Nat)
    (hB : s.carrier ∈ M.sets) : finiteIterationTrace s f b n ∈ M.sets :=
  M.finite_function_graph_mem pairing unions (natInitialPresentation (n + 1)) s _
    (M.natSetCode_mem separation infinite (n + 1)) hB

end TransitiveGround

end PartitionPilot.Forcing

end OAI
