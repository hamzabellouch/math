import OAI.SetTheory.PartitionPrinciple.Geometry.FiniteIterationTraces

namespace OAI

namespace PartitionPilot.Forcing

section
open SetRealization
universe u
variable {B : Type u} (s : Presentation B)

noncomputable def finiteWordGraph (xs : List B) : ZFSet.{u} :=
  (natInitialPresentation xs.length).graph s (fun i => xs.get i.down)

theorem finiteWordGraph_function (xs : List B) :
    ZFSet.IsFunc (natSetCode xs.length) s.carrier (finiteWordGraph s xs) :=
  (natInitialPresentation xs.length).graph_isFunc s _

theorem mem_finiteWordGraph (xs : List B) (z : ZFSet.{u}) :
    z ∈ finiteWordGraph s xs ↔
      ∃ i : Fin xs.length, z = ZFSet.pair (natSetCode i.val) (s.encode (xs.get i)) := by
  rw [finiteWordGraph, Presentation.mem_graph]
  exact ⟨fun ⟨i, eq⟩ => ⟨i.down, eq.symm⟩, fun ⟨i, eq⟩ => ⟨⟨i⟩, eq.symm⟩⟩

theorem pair_mem_finiteWordGraph (xs : List B) (k : Nat) (y : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) y ∈ finiteWordGraph s xs ↔
      ∃ h : k < xs.length, y = s.encode (xs.get ⟨k, h⟩) := by
  rw [mem_finiteWordGraph]
  constructor
  · rintro ⟨i, eq⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    have same : k = i.val := natSetCode_injective first
    subst k
    exact ⟨i.isLt, second⟩
  · rintro ⟨h, eq⟩
    exact ⟨⟨k, h⟩, congrArg (ZFSet.pair (natSetCode k)) eq⟩

theorem finiteWordGraph_nil : finiteWordGraph s [] = ∅ := by
  apply ZFSet.ext
  intro z
  rw [mem_finiteWordGraph]
  exact ⟨fun ⟨i, _⟩ => False.elim (Nat.not_lt_zero i.val i.isLt),
    fun h => False.elim (ZFSet.notMem_empty z h)⟩

theorem exists_finiteWordGraph {n : Nat} {f : ZFSet.{u}}
    (function : ZFSet.IsFunc (natSetCode n) s.carrier f) :
    ∃ xs : List B, xs.length = n ∧ finiteWordGraph s xs = f := by
  classical
  have values (i : Fin n) : ∃ b : B, ZFSet.pair (natSetCode i.val) (s.encode b) ∈ f := by
    obtain ⟨y, entry, _⟩ := function.2 (natSetCode i.val) ((natSetCode_mem_iff i.val n).2 i.isLt)
    obtain ⟨b, eq⟩ := (s.mem_carrier y).1 (ZFSet.pair_mem_prod.1 (function.1 entry)).2
    exact ⟨b, eq.symm ▸ entry⟩
  let value : Fin n → B := fun i => Classical.choose (values i)
  have entry (i : Fin n) : ZFSet.pair (natSetCode i.val) (s.encode (value i)) ∈ f :=
    Classical.choose_spec (values i)
  let xs := List.ofFn value
  have length : xs.length = n := List.length_ofFn
  refine ⟨xs, length, ?_⟩
  have graphFunction : FunctionGraphOn (natSetCode n) (finiteWordGraph s xs) := by
    rw [← length]
    exact ⟨s.carrier, finiteWordGraph_function s xs⟩
  apply graphFunction.eq_of_agree ⟨s.carrier, function⟩
  intro x y z xy xz
  obtain ⟨i, eq⟩ := (mem_finiteWordGraph s xs _).1 xy
  obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
  have hi : i.val < n := length ▸ i.isLt
  have getValue : xs.get i = value ⟨i.val, hi⟩ := by
    simp only [xs, List.get_eq_getElem, List.getElem_ofFn]
  have original : ZFSet.pair x y ∈ f := by
    rw [first, second, getValue]
    exact entry ⟨i.val, hi⟩
  exact (show FunctionGraphOn (natSetCode n) f from ⟨s.carrier, function⟩).unique original xz

namespace TransitiveGround
open SetFormula

theorem finiteWordGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (xs : List B) (hB : s.carrier ∈ M.sets) : finiteWordGraph s xs ∈ M.sets :=
  M.finite_function_graph_mem pairing unions (natInitialPresentation xs.length) s _
    (M.natSetCode_mem separation infinite xs.length) hB

end TransitiveGround

theorem finiteWordGraph_injective : Function.Injective (finiteWordGraph s) := by
  intro xs ys eq
  have other : ZFSet.IsFunc (natSetCode ys.length) s.carrier (finiteWordGraph s xs) :=
    eq.symm ▸ finiteWordGraph_function s ys
  have length := finiteWord_domain_unique (finiteWordGraph_function s xs) other
  apply List.ext_get length
  intro k hx hy
  apply s.injective
  have first := (pair_mem_finiteWordGraph s xs k _).2 ⟨hx, rfl⟩
  have second := (pair_mem_finiteWordGraph s ys k _).2 ⟨hy, rfl⟩
  rw [eq] at first
  exact (show FunctionGraphOn (natSetCode ys.length) (finiteWordGraph s ys) from
    ⟨s.carrier, finiteWordGraph_function s ys⟩).unique first second

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
variable (hB : s.carrier ∈ M.sets)

include pairing unions separation infinite hB
theorem finiteWordGraph_mem_finiteWords (xs : List B) :
    finiteWordGraph s xs ∈ M.finiteWords s.carrier :=
  (M.mem_finiteWords s.carrier _).2
    ⟨finiteWordGraph_mem s M pairing unions separation infinite xs hB,
      xs.length, finiteWordGraph_function s xs⟩

theorem finiteWords_exact_lists (f : ZFSet.{u}) :
    f ∈ M.finiteWords s.carrier ↔ ∃ xs : List B, finiteWordGraph s xs = f := by
  constructor
  · intro hf
    obtain ⟨_, n, function⟩ := (M.mem_finiteWords s.carrier f).1 hf
    obtain ⟨xs, _, eq⟩ := exists_finiteWordGraph s function
    exact ⟨xs, eq⟩
  · rintro ⟨xs, rfl⟩
    exact finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs

noncomputable def finiteWordPresentation : Presentation (List B) where
  carrier := M.finiteWords s.carrier
  encode := finiteWordGraph s
  injective := finiteWordGraph_injective s
  mem_carrier := finiteWords_exact_lists s M pairing unions separation infinite hB

end TransitiveGround

end

open SetRealization SetFormula
universe u

def FiniteWordMapCode (omega A B e f g : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ZFSet.IsFunc n A f ∧ ZFSet.IsFunc n B g ∧
    ∀ i ∈ n, ∀ x ∈ A, ∀ y ∈ B,
      ZFSet.pair i x ∈ f → ZFSet.pair i y ∈ g → ZFSet.pair x y ∈ e

namespace BoundedFormula

def finiteWordMapFormula {k} (omega a b e f g : Fin k) : BoundedFormula k :=
  exMem omega (.conj (functionFormula 0 a.succ f.succ)
    (.conj (functionFormula 0 b.succ g.succ)
      (.allMem 0 (.allMem a.succ.succ (.allMem b.succ.succ.succ
        (imp (pairMembershipFormula 2 1 f.succ.succ.succ.succ)
          (imp (pairMembershipFormula 2 0 g.succ.succ.succ.succ)
            (pairMembershipFormula 1 0 e.succ.succ.succ.succ))))))))

theorem truth_finiteWordMapFormula {k} (omega a b e f g : Fin k)
    (env : Fin k → ZFSet.{u}) :
    Truth (finiteWordMapFormula omega a b e f g) env ↔
      FiniteWordMapCode (env omega) (env a) (env b) (env e) (env f) (env g) := by
  simp only [finiteWordMapFormula, truth_exMem, Truth, truth_functionFormula,
    truth_imp, truth_pairMembershipFormula, FiniteWordMapCode]
  rfl

end BoundedFormula

theorem finiteWordMapCode_iff {B D : Type u} (s : Presentation B) (t : Presentation D)
    (e : B → D) (xs : List B) (ys : List D) :
    FiniteWordMapCode ZFSet.omega s.carrier t.carrier (s.graph t e)
      (finiteWordGraph s xs) (finiteWordGraph t ys) ↔ ys = xs.map e := by
  constructor
  · rintro ⟨n, hn, first, second, maps⟩
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have firstLength := finiteWord_domain_unique first (finiteWordGraph_function s xs)
    have secondLength := finiteWord_domain_unique second (finiteWordGraph_function t ys)
    have length : ys.length = (xs.map e).length := by simp only [List.length_map]; omega
    apply List.ext_get length
    intro i hi hj
    have hxs : i < xs.length := by simpa only [List.length_map] using hj
    have entry := maps (natSetCode i) ((natSetCode_mem_iff i n).2 (by omega))
      (s.encode (xs.get ⟨i, hxs⟩)) (s.encode_mem _)
      (t.encode (ys.get ⟨i, hi⟩)) (t.encode_mem _)
      ((pair_mem_finiteWordGraph s xs i _).2 ⟨hxs, rfl⟩)
      ((pair_mem_finiteWordGraph t ys i _).2 ⟨hi, rfl⟩)
    have same := (s.pair_mem_graph t e _ _).1 entry
    simpa only [List.get_eq_getElem, List.getElem_map] using same.symm
  · rintro rfl
    refine ⟨natSetCode xs.length, natSetCode_mem_omega _, finiteWordGraph_function s xs, ?_, ?_⟩
    · simpa only [List.length_map] using finiteWordGraph_function t (xs.map e)
    · intro i hi x _ y _ source target
      obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i xs.length).1 hi
      obtain ⟨_, rfl⟩ := (pair_mem_finiteWordGraph s xs k x).1 source
      obtain ⟨_, rfl⟩ := (pair_mem_finiteWordGraph t (xs.map e) k y).1 target
      apply (s.pair_mem_graph t e _ _).2
      simp only [List.get_eq_getElem, List.getElem_map]

end PartitionPilot.Forcing

end OAI
