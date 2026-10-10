import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSerialOrbits

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula SetRealization
universe u

noncomputable def stagedGraphRelation (W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n m h k,
    z = ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∧ m = insert n n ∧ h ⊆ k)
    (ZFSet.prod W W)

theorem pair_mem_stagedGraphRelation (W n m h k : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∈ stagedGraphRelation W ↔
      ZFSet.pair n h ∈ W ∧ ZFSet.pair m k ∈ W ∧ m = insert n n ∧ h ⊆ k := by
  rw [stagedGraphRelation, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨first, second⟩, a, b, c, d, equal, successor, subset⟩
    obtain ⟨firstEq, secondEq⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 firstEq
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 secondEq
    exact ⟨first, second, successor, subset⟩
  · rintro ⟨first, second, successor, subset⟩
    exact ⟨⟨first, second⟩, n, m, h, k, rfl, successor, subset⟩

namespace BoundedFormula

def stagedGraphEntryFormula {n} (z omega b : Fin n) : BoundedFormula n :=
  exMem omega (exMem omega.succ (exMem b.succ.succ (exMem b.succ.succ.succ
    (.conj (pairOfPairsFormula z.succ.succ.succ.succ 3 1 2 0)
      (.conj (successorFormula 2 3) (subsetFormula 1 0))))))

theorem truth_stagedGraphEntryFormula {n} (z omega b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (stagedGraphEntryFormula z omega b) env ↔
      ∃ a ∈ env omega, ∃ c ∈ env omega, ∃ h ∈ env b, ∃ k ∈ env b,
        env z = ZFSet.pair (ZFSet.pair a h) (ZFSet.pair c k) ∧ c = insert a a ∧ h ⊆ k := by
  simp only [stagedGraphEntryFormula, truth_exMem, Truth, truth_pairOfPairsFormula,
    truth_successorFormula, truth_subsetFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem stagedGraphRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {W B : ZFSet.{u}} (hW : W ∈ M.sets) (hB : B ∈ M.sets)
    (shape : W ⊆ ZFSet.prod ZFSet.omega B) : stagedGraphRelation W ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend ZFSet.omega (extend B Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.stagedGraphEntryFormula 0 1 2)
    params (Fin.cases hOmega (Fin.cases hB (fun i => Fin.elim0 i)))
    (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.stagedGraphEntryFormula 0 1 2)
      (extend z params)) (ZFSet.prod W W) = stagedGraphRelation W := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, stagedGraphRelation, ZFSet.mem_sep,
      BoundedFormula.truth_stagedGraphEntryFormula]
    change (_ ∧ ∃ n ∈ ZFSet.omega, ∃ m ∈ ZFSet.omega, ∃ h ∈ B, ∃ k ∈ B,
      z = ZFSet.pair (ZFSet.pair n h) (ZFSet.pair m k) ∧ m = insert n n ∧ h ⊆ k) ↔ _
    constructor
    · rintro ⟨bound, n, _, m, _, h, _, k, _, eq, successor, subset⟩
      exact ⟨bound, n, m, h, k, eq, successor, subset⟩
    · rintro ⟨bound, n, m, h, k, rfl, successor, subset⟩
      have points := ZFSet.pair_mem_prod.1 bound
      have first := ZFSet.pair_mem_prod.1 (shape points.1)
      have second := ZFSet.pair_mem_prod.1 (shape points.2)
      exact ⟨bound, n, first.1, m, second.1, h, first.2, k, second.2, rfl, successor, subset⟩
  exact equal ▸ selected

theorem exists_groundCoherentChoices
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {W B initial : ZFSet.{u}} (hW : W ∈ M.sets) (hB : B ∈ M.sets)
    (shape : W ⊆ ZFSet.prod ZFSet.omega B) (start : ZFSet.pair ∅ initial ∈ W)
    (extendable : ∀ n ∈ ZFSet.omega, ∀ h, ZFSet.pair n h ∈ W →
      ∃ k, ZFSet.pair (insert n n) k ∈ W ∧ h ⊆ k) :
    ∃ history ∈ M.sets, ZFSet.IsFunc ZFSet.omega B history ∧
      (∀ h, ZFSet.pair ∅ h ∈ history ↔ h = initial) ∧
      (∀ n ∈ ZFSet.omega, ∀ h, ZFSet.pair n h ∈ history → ZFSet.pair n h ∈ W) ∧
      ∀ n ∈ ZFSet.omega, ∀ h k,
        ZFSet.pair n h ∈ history → ZFSet.pair (insert n n) k ∈ history → h ⊆ k := by
  have hOmega := M.omega_mem separation infinite
  have relationGround := M.stagedGraphRelation_mem pairing unions powers separation infinite hW hB shape
  have serial : ∀ x ∈ W, ∃ y ∈ W, ZFSet.pair x y ∈ stagedGraphRelation W := by
    intro x hx
    obtain ⟨n, hn, h, _, rfl⟩ := ZFSet.mem_prod.1 (shape hx)
    obtain ⟨k, next, subset⟩ := extendable n hn h hx
    exact ⟨ZFSet.pair (insert n n) k, next,
      (pair_mem_stagedGraphRelation W n (insert n n) h k).2 ⟨hx, next, rfl, subset⟩⟩
  obtain ⟨orbit, hOrbit, orbitFunction, zero, step⟩ :=
    M.exists_groundSerialOrbit pairing unions powers separation infinite choice hW relationGround start serial
  have stageValue : ∀ n : Nat, ∀ z, ZFSet.pair (natSetCode n) z ∈ orbit →
      ∃ h, z = ZFSet.pair (natSetCode n) h := by
    intro n
    induction n with
    | zero =>
      intro z entry
      exact ⟨initial, (zero z).1 entry⟩
    | succ n ih =>
      intro z entry
      obtain ⟨w, previous, _⟩ := orbitFunction.2 (natSetCode n) (natSetCode_mem_omega n)
      obtain ⟨h, rfl⟩ := ih w previous
      have rel := step (natSetCode n) (natSetCode_mem_omega n) _ z previous entry
      obtain ⟨_, a, b, c, d, equal, successor, _⟩ := ZFSet.mem_sep.1 rel
      obtain ⟨source, target⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 source
      refine ⟨d, ?_⟩
      rw [successor] at target
      exact target
  have stageValueRaw (n z : ZFSet.{u}) (hn : n ∈ ZFSet.omega)
      (entry : ZFSet.pair n z ∈ orbit) : ∃ h, z = ZFSet.pair n h := by
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact stageValue k z entry
  let history := relationCompose ZFSet.omega W B orbit (productSecond ZFSet.omega B)
  have historyGround : history ∈ M.sets := M.relationCompose_mem pairing unions powers separation
    hOmega hW hB hOrbit (M.productSecond_mem pairing unions powers separation hOmega hB)
  have historyFunction : ZFSet.IsFunc ZFSet.omega B history :=
    relationCompose_function_of_subset orbitFunction (productSecond_function ZFSet.omega B) shape
  have projected (n h : ZFSet.{u}) (hn : n ∈ ZFSet.omega) :
      ZFSet.pair n h ∈ history ↔ ZFSet.pair n (ZFSet.pair n h) ∈ orbit := by
    change ZFSet.pair n h ∈ relationCompose _ _ _ _ _ ↔ _
    rw [pair_mem_relationCompose]
    constructor
    · rintro ⟨_, _, z, _, entry, projection⟩
      obtain ⟨k, rfl⟩ := stageValueRaw n z hn entry
      obtain ⟨a, _, b, _, equal⟩ := (mem_productSecond _ _ _).1 projection
      obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
      exact second ▸ entry
    · intro entry
      have point := (ZFSet.pair_mem_prod.1 (orbitFunction.1 entry)).2
      have inB := (ZFSet.pair_mem_prod.1 (shape point)).2
      exact ⟨hn, inB, ZFSet.pair n h, point, entry,
        (mem_productSecond _ _ _).2 ⟨n, hn, h, inB, rfl⟩⟩
  refine ⟨history, historyGround, historyFunction, ?_, ?_, ?_⟩
  · intro h
    rw [projected ∅ h (natSetCode_mem_omega 0), zero, ZFSet.pair_inj]
    exact ⟨And.right, fun eq => ⟨rfl, eq⟩⟩
  · intro n hn h entry
    exact (ZFSet.pair_mem_prod.1 (orbitFunction.1 ((projected n h hn).1 entry))).2
  · intro n hn h k first second
    have successorMem : insert n n ∈ ZFSet.omega := by
      obtain ⟨j, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
      exact natSetCode_mem_omega (j + 1)
    have rel := step n hn _ _ ((projected n h hn).1 first)
      ((projected (insert n n) k successorMem).1 second)
    exact ((pair_mem_stagedGraphRelation W n (insert n n) h k).1 rel).2.2.2

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
