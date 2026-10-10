import Mathlib.Data.List.Chain
import OAI.SetTheory.PartitionPrinciple.Definability.FiniteWordMapCodes
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundIndexedClassInclusions
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundNaturalRecursion

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

def FiniteRelationPathCode (omega A R x y t : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ∃ d ∈ omega, d = insert n n ∧
    IterationTraceCode n d A R x t ∧ ZFSet.pair n y ∈ t

theorem IterationTraceCode.reflTransGen {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {t : ZFSet.{u}} {x : B}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier R
      (s.encode x) t) :
    ∀ k ≤ n, ∀ y, ZFSet.pair (natSetCode k) (s.encode y) ∈ t →
      Relation.ReflTransGen r x y := by
  intro k
  induction k with
  | zero =>
    intro _ y entry
    have same := (show FunctionGraphOn (natSetCode (n + 1)) t from
      ⟨s.carrier, trace.function⟩).unique trace.seed entry
    have equal : x = y := s.injective same
    subst y
    exact .refl
  | succ k ih =>
    intro hk y entry
    have domain := (natSetCode_mem_iff k (n + 1)).2 (by omega)
    obtain ⟨a, prev, _⟩ := trace.function.2 (natSetCode k) domain
    have ha := (ZFSet.pair_mem_prod.1 (trace.function.1 prev)).2
    obtain ⟨b, eq⟩ := (s.mem_carrier a).1 ha
    have previous : ZFSet.pair (natSetCode k) (s.encode b) ∈ t := eq.symm ▸ prev
    have step := trace.next (natSetCode k) ((natSetCode_mem_iff k n).2 (by omega))
      (natSetCode (k + 1)) ((natSetCode_mem_iff _ _).2 (by omega))
      _ (s.encode_mem b) _ (s.encode_mem y) rfl previous entry
    exact (ih (by omega) b previous).tail ((edges b y).1 step)

theorem FiniteRelationPathCode.reflTransGen {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {x y : B} {t : ZFSet.{u}}
    (path : FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x) (s.encode y) t) :
    Relation.ReflTransGen r x y := by
  obtain ⟨n, hn, d, _, succ, trace, out⟩ := path
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
  have dcode : d = natSetCode (n + 1) := succ
  exact (dcode ▸ trace).reflTransGen s r edges n (Nat.le_refl n) y out

theorem finiteWordGraph_chain_trace {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (x : B) (xs : List B) (chain : List.IsChain r (x :: xs)) :
    IterationTraceCode (natSetCode xs.length) (natSetCode (xs.length + 1))
      s.carrier R (s.encode x) (finiteWordGraph s (x :: xs)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [List.length_cons] using finiteWordGraph_function s (x :: xs)
  · apply (pair_mem_finiteWordGraph s (x :: xs) 0 _).2
    exact ⟨by simp, rfl⟩
  · intro i hi j _ a _ b _ succ prev next
    obtain ⟨k, hk, rfl⟩ := (mem_natSetCode i xs.length).1 hi
    have jcode : j = natSetCode (k + 1) := succ
    obtain ⟨_, avalue⟩ := (pair_mem_finiteWordGraph s (x :: xs) k a).1 prev
    obtain ⟨_, bvalue⟩ := (pair_mem_finiteWordGraph s (x :: xs) (k + 1) b).1 (jcode ▸ next)
    rw [avalue, bvalue, edges]
    simpa only [List.get_eq_getElem] using
      chain.getElem k (by simpa only [List.length_cons] using Nat.succ_lt_succ hk)

theorem finiteWordGraph_chain_path {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (x : B) (xs : List B) (chain : List.IsChain r (x :: xs)) :
    FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x)
      (s.encode ((x :: xs).getLast (List.cons_ne_nil _ _)))
      (finiteWordGraph s (x :: xs)) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, natSetCode (xs.length + 1),
    natSetCode_mem_omega _, rfl, finiteWordGraph_chain_trace s r edges x xs chain, ?_⟩
  apply (pair_mem_finiteWordGraph s (x :: xs) xs.length _).2
  refine ⟨by simp, ?_⟩
  simp only [List.get_eq_getElem, List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel]

theorem reflTransGen_iff_finiteWordGraph_path {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y) (x y : B) :
    Relation.ReflTransGen r x y ↔ ∃ xs : List B,
      FiniteRelationPathCode ZFSet.omega s.carrier R (s.encode x) (s.encode y)
        (finiteWordGraph s xs) := by
  constructor
  · intro path
    obtain ⟨xs, chain, last⟩ := List.exists_isChain_cons_of_relationReflTransGen path
    exact ⟨x :: xs, last ▸ finiteWordGraph_chain_path s r edges x xs chain⟩
  · rintro ⟨xs, code⟩
    exact code.reflTransGen s r edges





inductive RelationPathSteps {B : Type u} (r : B → B → Prop) : Nat → B → B → Prop
  | nil (x : B) : RelationPathSteps r 0 x x
  | tail {n : Nat} {x y z : B} : RelationPathSteps r n x y → r y z → RelationPathSteps r (n + 1) x z

theorem chain_append_last {B : Type u} {r : B → B → Prop} {x z : B} {xs : List B}
    (chain : List.IsChain r (x :: xs)) (edge : r ((x :: xs).getLast (List.cons_ne_nil _ _)) z) :
    List.IsChain r (x :: (xs ++ [z])) := by
  induction xs generalizing x with
  | nil => exact .cons_cons edge (.singleton _)
  | cons next rest ih =>
    obtain ⟨first, tail⟩ := List.isChain_cons_cons.mp chain
    exact .cons_cons first (ih tail (by simpa only [List.getLast_cons_cons] using edge))

namespace RelationPathSteps
variable {B : Type u} {r : B → B → Prop} {n : Nat} {x y z : B}

theorem append {m : Nat} (first : RelationPathSteps r n x y) (second : RelationPathSteps r m y z) :
    RelationPathSteps r (n + m) x z := by
  induction second with
  | nil => exact first
  | tail previous edge ih => exact .tail (ih first) edge

theorem cons (edge : r x y) (path : RelationPathSteps r n y z) : RelationPathSteps r (n + 1) x z := by
  simpa only [Nat.add_comm] using (RelationPathSteps.tail (RelationPathSteps.nil x) edge).append path

theorem chain (path : RelationPathSteps r n x y) :
    ∃ xs : List B, List.IsChain r (x :: xs) ∧
      (x :: xs).getLast (List.cons_ne_nil _ _) = y ∧ xs.length = n := by
  induction path with
  | nil x => exact ⟨[], .singleton _, rfl, rfl⟩
  | @tail n x y z previous edge ih =>
    obtain ⟨xs, chain, last, length⟩ := ih
    refine ⟨xs ++ [z], chain_append_last chain (last.symm ▸ edge), ?_, ?_⟩
    · simp
    · simp only [List.length_append, List.length_singleton, length]

end RelationPathSteps

theorem IterationTraceCode.pathSteps {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {t : ZFSet.{u}} {x : B}
    (trace : IterationTraceCode (natSetCode n) (natSetCode (n + 1)) s.carrier R (s.encode x) t) :
    ∀ k ≤ n, ∀ y, ZFSet.pair (natSetCode k) (s.encode y) ∈ t → RelationPathSteps r k x y := by
  intro k
  induction k with
  | zero =>
    intro _ y entry
    have same := (show FunctionGraphOn (natSetCode (n + 1)) t from ⟨s.carrier, trace.function⟩).unique trace.seed entry
    have equal := s.injective same
    subst y
    exact .nil x
  | succ k ih =>
    intro hk y entry
    obtain ⟨a, prev, _⟩ := trace.function.2 (natSetCode k) ((natSetCode_mem_iff _ _).2 (by omega))
    obtain ⟨b, equal⟩ := (s.mem_carrier a).1 (ZFSet.pair_mem_prod.1 (trace.function.1 prev)).2
    have previous : ZFSet.pair (natSetCode k) (s.encode b) ∈ t := equal.symm ▸ prev
    have edge := trace.next (natSetCode k) ((natSetCode_mem_iff _ _).2 (by omega))
      (natSetCode (k + 1)) ((natSetCode_mem_iff _ _).2 (by omega))
      _ (s.encode_mem b) _ (s.encode_mem y) rfl previous entry
    exact .tail (ih (by omega) b previous) ((edges b y).1 edge)

theorem RelationPathSteps.exists_trace {B : Type u} (s : Presentation B)
    (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    {n : Nat} {x y : B} (path : RelationPathSteps r n x y) :
    ∃ xs : List B, IterationTraceCode (natSetCode n) (natSetCode (n + 1))
      s.carrier R (s.encode x) (finiteWordGraph s xs) ∧ ZFSet.pair (natSetCode n) (s.encode y) ∈ finiteWordGraph s xs := by
  obtain ⟨xs, chain, last, rfl⟩ := path.chain
  refine ⟨x :: xs, finiteWordGraph_chain_trace s r edges x xs chain, ?_⟩
  apply (pair_mem_finiteWordGraph s (x :: xs) xs.length _).2
  refine ⟨by simp, ?_⟩
  rw [← last]
  simp only [List.get_eq_getElem, List.getLast_eq_getElem, List.length_cons, Nat.add_sub_cancel]

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

namespace BoundedFormula

def finiteRelationPathFormula {k} (omega A R x y t zero : Fin k) : BoundedFormula k :=
  exMem omega (exMem omega.succ (.conj (successorFormula 0 1)
    (.conj (iterationTraceFormula 1 0 A.succ.succ R.succ.succ x.succ.succ
      t.succ.succ zero.succ.succ) (pairMembershipFormula 1 y.succ.succ t.succ.succ))))

theorem truth_finiteRelationPathFormula {k} (omega A R x y t zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (finiteRelationPathFormula omega A R x y t zero) env ↔
      FiniteRelationPathCode (env omega) (env A) (env R) (env x) (env y) (env t) := by
  simp only [finiteRelationPathFormula, truth_exMem, Truth, truth_successorFormula,
    truth_pairMembershipFormula, FiniteRelationPathCode]
  apply exists_congr
  intro n
  apply and_congr_right
  intro _
  apply exists_congr
  intro d
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl (and_congr
    (truth_iterationTraceFormula _ _ _ _ _ _ _ _ (by exact hzero)) Iff.rfl)

def finitePathClosureEntryFormula {k} (z A R omega paths zero : Fin k) : BoundedFormula k :=
  exMem A (exMem A.succ (exMem paths.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (finiteRelationPathFormula omega.succ.succ.succ A.succ.succ.succ
        R.succ.succ.succ 2 1 0 zero.succ.succ.succ))))

theorem truth_finitePathClosureEntryFormula {k} (z A R omega paths zero : Fin k)
    (env : Fin k → ZFSet.{u}) (hzero : env zero = ∅) :
    Truth (finitePathClosureEntryFormula z A R omega paths zero) env ↔
      ∃ x ∈ env A, ∃ y ∈ env A, ∃ t ∈ env paths,
        env z = ZFSet.pair x y ∧
          FiniteRelationPathCode (env omega) (env A) (env R) x y t := by
  simp only [finitePathClosureEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply exists_congr
  intro y
  apply and_congr_right
  intro _
  apply exists_congr
  intro t
  apply and_congr_right
  intro _
  exact and_congr Iff.rfl
    (truth_finiteRelationPathFormula _ _ _ _ _ _ _ _ (by exact hzero))

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def finitePathClosure (A R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ A, ∃ t ∈ M.finiteWords A,
    z = ZFSet.pair x y ∧ FiniteRelationPathCode ZFSet.omega A R x y t) (ZFSet.prod A A)

theorem pair_mem_finitePathClosure_iff (A R x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ M.finitePathClosure A R ↔
      x ∈ A ∧ y ∈ A ∧ ∃ t ∈ M.finiteWords A, FiniteRelationPathCode ZFSet.omega A R x y t := by
  rw [finitePathClosure, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, t, ht, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, t, ht, code⟩
  · rintro ⟨hx, hy, t, ht, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, t, ht, rfl, code⟩

theorem finitePathClosure_subset (A R : ZFSet.{u}) :
    M.finitePathClosure A R ⊆ ZFSet.prod A A :=
  fun _ h => (ZFSet.mem_sep.1 h).1

theorem finitePathClosure_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) :
    M.finitePathClosure A R ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hPaths := M.finiteWords_mem pairing unions powers separation infinite hA
  have hZero := M.empty_mem ⟨A, hA⟩
  let params := extend A (extend R (extend ZFSet.omega (extend (M.finiteWords A)
    (extend ∅ Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.finitePathClosureEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hA (Fin.cases hR (Fin.cases hOmega (Fin.cases hPaths
      (Fin.cases hZero (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hA)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.finitePathClosureEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod A A) = M.finitePathClosure A R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, finitePathClosure, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_finitePathClosureEntryFormula _ _ _ _ _ _ _ rfl)
  exact equal ▸ selected

theorem pair_mem_finitePathClosure
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (hB : s.carrier ∈ M.sets) (x y : B) :
    ZFSet.pair (s.encode x) (s.encode y) ∈ M.finitePathClosure s.carrier R ↔
      Relation.ReflTransGen r x y := by
  rw [M.pair_mem_finitePathClosure_iff]
  constructor
  · rintro ⟨_, _, t, _, code⟩
    exact code.reflTransGen s r edges
  · intro path
    obtain ⟨xs, code⟩ := (reflTransGen_iff_finiteWordGraph_path s r edges x y).1 path
    exact ⟨s.encode_mem x, s.encode_mem y, finiteWordGraph s xs,
      finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs, code⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})
  (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
  (unions : Realize M.sets SetFormula.union Fin.elim0)
  (separation : SeparationSchema M.sets)
  (infinite : Realize M.sets infinity Fin.elim0)
  {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
  (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
  (hB : s.carrier ∈ M.sets)

include pairing unions separation infinite edges hB in
theorem finitePathClosure_equivalence (symmetric : ∀ ⦃left right⦄, r left right → r right left) :
    EquivalenceRelationCode s.carrier (M.finitePathClosure s.carrier R) := by
  let : Std.Symm r := ⟨fun _ _ related => symmetric related⟩
  have exactPath := M.pair_mem_finitePathClosure pairing unions separation infinite s r edges hB
  refine ⟨M.finitePathClosure_subset s.carrier R, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    exact (exactPath a a).2 .refl
  · intro x y xy
    obtain ⟨hx, hy, _⟩ := (M.pair_mem_finitePathClosure_iff s.carrier R x y).1 xy
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    exact (exactPath b a).2 (symm ((exactPath a b).1 xy))
  · intro x y z xy yz
    obtain ⟨hx, hy, _⟩ := (M.pair_mem_finitePathClosure_iff s.carrier R x y).1 xy
    have hz := ((M.pair_mem_finitePathClosure_iff s.carrier R y z).1 yz).2.1
    obtain ⟨a, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨b, rfl⟩ := (s.mem_carrier y).1 hy
    obtain ⟨c, rfl⟩ := (s.mem_carrier z).1 hz
    exact (exactPath a c).2 (((exactPath a b).1 xy).trans ((exactPath b c).1 yz))

include pairing unions separation infinite edges hB in
theorem finitePathQuotient_spec
    (powers : Realize M.sets powerSet Fin.elim0) (hR : R ∈ M.sets)
    (symmetric : ∀ ⦃left right⦄, r left right → r right left) :
    let E := M.finitePathClosure s.carrier R
    E ∈ M.sets ∧ EquivalenceRelationCode s.carrier E ∧
      equivalenceClasses s.carrier E ∈ M.sets ∧ equivalenceClassifier s.carrier E ∈ M.sets ∧
      ZFSet.IsFunc s.carrier (equivalenceClasses s.carrier E) (equivalenceClassifier s.carrier E) ∧
      (∀ C ∈ equivalenceClasses s.carrier E, ∃ x ∈ s.carrier,
        ZFSet.pair x C ∈ equivalenceClassifier s.carrier E) ∧
      (∀ x y C D, ZFSet.pair x C ∈ equivalenceClassifier s.carrier E →
        ZFSet.pair y D ∈ equivalenceClassifier s.carrier E → (C = D ↔ ZFSet.pair x y ∈ E)) := by
  dsimp only
  have ground := M.finitePathClosure_mem pairing unions powers separation infinite hB hR
  have equivalence := M.finitePathClosure_equivalence pairing unions separation infinite s r edges hB symmetric
  exact ⟨ground, equivalence,
    M.equivalenceClasses_spec pairing unions powers separation hB ground equivalence⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def relationPathLengths (A R root : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ n ∈ ZFSet.omega, ∃ y ∈ A, ∃ d ∈ ZFSet.omega, ∃ t ∈ M.finiteWords A,
    z = ZFSet.pair n y ∧ d = insert n n ∧ IterationTraceCode n d A R root t ∧ ZFSet.pair n y ∈ t)
    (ZFSet.prod ZFSet.omega A)

theorem pair_mem_relationPathLengths (A R root n y : ZFSet.{u}) :
    ZFSet.pair n y ∈ M.relationPathLengths A R root ↔ n ∈ ZFSet.omega ∧ y ∈ A ∧
      ∃ d ∈ ZFSet.omega, ∃ t ∈ M.finiteWords A,
        d = insert n n ∧ IterationTraceCode n d A R root t ∧ ZFSet.pair n y ∈ t := by
  rw [relationPathLengths, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, n', hn, y', hy, d, hd, t, ht, equal, succ, trace, entry⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hn, hy, d, hd, t, ht, succ, trace, entry⟩
  · rintro ⟨hn, hy, d, hd, t, ht, succ, trace, entry⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hn, hy⟩, n, hn, y, hy, d, hd, t, ht, rfl, succ, trace, entry⟩

theorem relationPathLengths_subset (A R root : ZFSet.{u}) :
    M.relationPathLengths A R root ⊆ ZFSet.prod ZFSet.omega A := fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem relationPathLengths_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R root : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) (hRoot : root ∈ M.sets) :
    M.relationPathLengths A R root ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have hPaths := M.finiteWords_mem pairing unions powers separation infinite hA
  have hZero := M.empty_mem ⟨A, hA⟩
  let params := extend ZFSet.omega (extend A (extend R (extend root (extend (M.finiteWords A) (extend ∅ Fin.elim0)))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6)
    params (Fin.cases hOmega (Fin.cases hA (Fin.cases hR (Fin.cases hRoot (Fin.cases hPaths
      (Fin.cases hZero (fun i => Fin.elim0 i))))))) (M.prod_mem pairing unions powers separation hOmega hA)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.iterationEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod ZFSet.omega A) = M.relationPathLengths A R root := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationPathLengths, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_iterationEntryFormula _ _ _ _ _ _ _ _ rfl)
  exact equal ▸ selected

theorem relationPathLengths_iff_steps
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {B : Type u} (s : Presentation B) (r : B → B → Prop) {R : ZFSet.{u}}
    (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ R ↔ r x y)
    (hB : s.carrier ∈ M.sets) (root y : B) (n : Nat) :
    ZFSet.pair (natSetCode n) (s.encode y) ∈ M.relationPathLengths s.carrier R (s.encode root) ↔
      RelationPathSteps r n root y := by
  rw [M.pair_mem_relationPathLengths]
  constructor
  · rintro ⟨_, _, d, _, t, _, succ, trace, out⟩
    have dcode : d = natSetCode (n + 1) := succ
    exact (dcode ▸ trace).pathSteps s r edges n (Nat.le_refl n) y out
  · intro path
    obtain ⟨xs, trace, out⟩ := path.exists_trace s r edges
    exact ⟨natSetCode_mem_omega n, s.encode_mem y, natSetCode (n + 1), natSetCode_mem_omega _,
      finiteWordGraph s xs, finiteWordGraph_mem_finiteWords s M pairing unions separation infinite hB xs,
      rfl, trace, out⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

noncomputable def shortestLengthGraph (A lengths : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ y ∈ A, ∃ n ∈ ZFSet.omega, z = ZFSet.pair y n ∧
    ZFSet.pair n y ∈ lengths ∧ ∀ k ∈ n, ZFSet.pair k y ∉ lengths) (ZFSet.prod A ZFSet.omega)

theorem pair_mem_shortestLengthGraph (A lengths y n : ZFSet.{u}) :
    ZFSet.pair y n ∈ shortestLengthGraph A lengths ↔ y ∈ A ∧ n ∈ ZFSet.omega ∧
      ZFSet.pair n y ∈ lengths ∧ ∀ k ∈ n, ZFSet.pair k y ∉ lengths := by
  rw [shortestLengthGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y', hy, n', hn, equal, entry, minimal⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hy, hn, entry, minimal⟩
  · rintro ⟨hy, hn, entry, minimal⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hy, hn⟩, y, hy, n, hn, rfl, entry, minimal⟩

namespace BoundedFormula
def shortestLengthEntryFormula {k} (z A omega lengths : Fin k) : BoundedFormula k :=
  exMem A (exMem omega.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.conj (pairMembershipFormula 0 1 lengths.succ.succ)
      (.allMem 0 (.neg (pairMembershipFormula 0 2 lengths.succ.succ.succ))))))

theorem truth_shortestLengthEntryFormula {k} (z A omega lengths : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (shortestLengthEntryFormula z A omega lengths) env ↔
      ∃ y ∈ env A, ∃ n ∈ env omega, env z = ZFSet.pair y n ∧
        ZFSet.pair n y ∈ env lengths ∧ ∀ j ∈ n, ZFSet.pair j y ∉ env lengths := by
  simp only [shortestLengthEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem shortestLengthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A lengths : ZFSet.{u}} (hA : A ∈ M.sets) (hLengths : lengths ∈ M.sets) :
    shortestLengthGraph A lengths ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend A (extend ZFSet.omega (extend lengths Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.shortestLengthEntryFormula 0 1 2 3)
    params (Fin.cases hA (Fin.cases hOmega (Fin.cases hLengths (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hA hOmega)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.shortestLengthEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod A ZFSet.omega) = shortestLengthGraph A lengths := by
    apply ZFSet.ext
    intro z
    rw [shortestLengthGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_shortestLengthEntryFormula _ _ _ _ _)
  exact equal ▸ selected

noncomputable def relationDepthGraph (A R root : ZFSet.{u}) : ZFSet.{u} :=
  shortestLengthGraph A (M.relationPathLengths A R root)

theorem relationDepthGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A R root : ZFSet.{u}} (hA : A ∈ M.sets) (hR : R ∈ M.sets) (hRoot : root ∈ M.sets) :
    M.relationDepthGraph A R root ∈ M.sets :=
  M.shortestLengthGraph_mem pairing unions powers separation infinite hA
    (M.relationPathLengths_mem pairing unions powers separation infinite hA hR hRoot)
end TransitiveGround

variable {B : Type u} (s : Presentation B) (depth : B → Nat) {lengths : ZFSet.{u}}
variable (valid : ∀ x, ZFSet.pair (natSetCode (depth x)) (s.encode x) ∈ lengths)
variable (minimal : ∀ x n, ZFSet.pair (natSetCode n) (s.encode x) ∈ lengths → depth x ≤ n)
include valid minimal

theorem shortestLengthGraph_entry (x : B) (n : Nat) :
    ZFSet.pair (s.encode x) (natSetCode n) ∈ shortestLengthGraph s.carrier lengths ↔ n = depth x := by
  rw [pair_mem_shortestLengthGraph]
  constructor
  · rintro ⟨_, _, entry, least⟩
    have lower := minimal x n entry
    have notLower : ¬ depth x < n := fun h => least _ ((natSetCode_mem_iff _ _).2 h) (valid x)
    omega
  · rintro rfl
    refine ⟨s.encode_mem x, natSetCode_mem_omega _, valid x, ?_⟩
    intro k hk entry
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode k (depth x)).1 hk
    exact Nat.not_lt_of_ge (minimal x n entry) hn

theorem shortestLengthGraph_eq_graph :
    shortestLengthGraph s.carrier lengths = s.graph natPresentation (fun x => ⟨depth x⟩) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro entry
    obtain ⟨x, hx, n, hn, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 entry).1
    obtain ⟨x, rfl⟩ := (s.mem_carrier x).1 hx
    obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    have equal := (shortestLengthGraph_entry s depth valid minimal x n).1 entry
    exact (s.pair_mem_graph natPresentation (fun x => ⟨depth x⟩) x ⟨n⟩).2 (congrArg ULift.up equal.symm)
  · intro entry
    obtain ⟨x, rfl⟩ := (s.mem_graph natPresentation (fun x => ⟨depth x⟩) z).1 entry
    exact (shortestLengthGraph_entry s depth valid minimal x (depth x)).2 rfl

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def LowerDepthEdgeCode (omega depths adjacency p v : ZFSet.{u}) : Prop :=
  ZFSet.pair p v ∈ adjacency ∧ ∃ n ∈ omega, ∃ m ∈ omega,
    ZFSet.pair v n ∈ depths ∧ ZFSet.pair p m ∈ depths ∧ n = insert m m

noncomputable def treeParentGraph (V depths adjacency root : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ p ∈ V, z = ZFSet.pair v p ∧
    ((v = root ∧ p = root) ∨ LowerDepthEdgeCode ZFSet.omega depths adjacency p v)) (ZFSet.prod V V)

theorem pair_mem_treeParentGraph (V depths adjacency root v p : ZFSet.{u}) :
    ZFSet.pair v p ∈ treeParentGraph V depths adjacency root ↔ v ∈ V ∧ p ∈ V ∧
      ((v = root ∧ p = root) ∨ LowerDepthEdgeCode ZFSet.omega depths adjacency p v) := by
  rw [treeParentGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, p', hp, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, hp, body⟩
  · rintro ⟨hv, hp, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, hp⟩, v, hv, p, hp, rfl, body⟩

namespace BoundedFormula
def lowerDepthEdgeFormula {k} (omega depths adjacency p v : Fin k) : BoundedFormula k :=
  .conj (pairMembershipFormula p v adjacency) (exMem omega (exMem omega.succ
    (.conj (pairMembershipFormula v.succ.succ 1 depths.succ.succ)
      (.conj (pairMembershipFormula p.succ.succ 0 depths.succ.succ) (successorFormula 1 0)))))

theorem truth_lowerDepthEdgeFormula {k} (omega depths adjacency p v : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (lowerDepthEdgeFormula omega depths adjacency p v) env ↔
      LowerDepthEdgeCode (env omega) (env depths) (env adjacency) (env p) (env v) := by
  simp only [lowerDepthEdgeFormula, Truth, truth_pairMembershipFormula, truth_exMem, truth_successorFormula]
  rfl

def treeParentEntryFormula {k} (z V omega depths adjacency root : Fin k) : BoundedFormula k :=
  exMem V (exMem V.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (disj (.conj (.equal 1 root.succ.succ) (.equal 0 root.succ.succ))
      (lowerDepthEdgeFormula omega.succ.succ depths.succ.succ adjacency.succ.succ 0 1))))

theorem truth_treeParentEntryFormula {k} (z V omega depths adjacency root : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (treeParentEntryFormula z V omega depths adjacency root) env ↔
      ∃ v ∈ env V, ∃ p ∈ env V, env z = ZFSet.pair v p ∧
        ((v = env root ∧ p = env root) ∨ LowerDepthEdgeCode (env omega) (env depths) (env adjacency) p v) := by
  simp only [treeParentEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_disj,
    truth_lowerDepthEdgeFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
theorem treeParentGraph_mem (M : TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {V depths adjacency root : ZFSet.{u}} (hV : V ∈ M.sets) (hDepths : depths ∈ M.sets)
    (hAdjacency : adjacency ∈ M.sets) (hRoot : root ∈ M.sets) :
    treeParentGraph V depths adjacency root ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  let params := extend V (extend ZFSet.omega (extend depths (extend adjacency (extend root Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.treeParentEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hV (Fin.cases hOmega (Fin.cases hDepths (Fin.cases hAdjacency
      (Fin.cases hRoot (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hV hV)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.treeParentEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod V V) = treeParentGraph V depths adjacency root := by
    apply ZFSet.ext
    intro z
    rw [treeParentGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_treeParentEntryFormula _ _ _ _ _ _ _)
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars
open Forcing SetRealization SetFormula
universe u
variable (J S R : Type u) [Group J] (request : S → R)
local notation "adj" => fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y

theorem Follows.pathSteps {x y : Vertex J S R} {L : List (Dart J S R)}
    (path : Follows J S R request x L y) : RelationPathSteps adj L.length x y := by
  induction path with
  | nil => exact .nil _
  | cons d tail ih => exact ih.cons ⟨d, rfl, rfl⟩

theorem follows_of_pathSteps {n : Nat} {x y : Vertex J S R} (path : RelationPathSteps adj n x y) :
    ∃ L : List (Dart J S R), Follows J S R request x L y ∧ L.length = n := by
  induction path with
  | nil x => exact ⟨[], Follows.nil x, rfl⟩
  | @tail n x y z previous edge ih =>
    obtain ⟨L, followed, length⟩ := ih
    obtain ⟨d, src, tgt⟩ := edge
    have oneEdge : Follows J S R request y [d] z := by
      rw [← src, ← tgt]
      exact Follows.cons d (Follows.nil _)
    exact ⟨L ++ [d], follows_append J S R request followed oneEdge,
      by simp only [List.length_append, List.length_singleton, length]⟩

theorem depth_pathSteps (x : Vertex J S R) :
    RelationPathSteps adj (depth J S R request x) (root J S R) x :=
  (rootPath_follows J S R request x).pathSteps J S R request

theorem depth_le_steps {x : Vertex J S R} {n : Nat}
    (path : RelationPathSteps adj n (root J S R) x) : depth J S R request x ≤ n := by
  obtain ⟨L, followed, rfl⟩ := follows_of_pathSteps J S R request path
  exact rootPath_shortest J S R request followed

variable (M : Forcing.TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (s : Presentation (Vertex J S R)) {adjacency : ZFSet.{u}}
variable (edges : ∀ x y, ZFSet.pair (s.encode x) (s.encode y) ∈ adjacency ↔
  ∃ d : Dart J S R, TileStars.source J S R request d = x ∧ TileStars.target J S R request d = y)
variable (hV : s.carrier ∈ M.sets)

include pairing unions separation infinite edges hV in
theorem depthGraph_eq_graph :
    M.relationDepthGraph s.carrier adjacency (s.encode (root J S R)) =
      s.graph natPresentation (fun x => ⟨depth J S R request x⟩) := by
  change shortestLengthGraph s.carrier
    (M.relationPathLengths s.carrier adjacency (s.encode (root J S R))) = _
  apply shortestLengthGraph_eq_graph s (depth J S R request)
    (lengths := M.relationPathLengths s.carrier adjacency (s.encode (root J S R)))
  · intro x
    exact (M.relationPathLengths_iff_steps pairing unions separation infinite s
      (fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y)
      edges hV (root J S R) x (depth J S R request x)).2 (depth_pathSteps J S R request x)
  · intro x n entry
    exact depth_le_steps J S R request
      ((M.relationPathLengths_iff_steps pairing unions separation infinite s
        (fun x y => ∃ d : Dart J S R, source J S R request d = x ∧ target J S R request d = y)
        edges hV (root J S R) x n).1 entry)

include pairing unions powers separation infinite edges hV in
theorem depthGraph_spec (hAdjacency : adjacency ∈ M.sets) :
    M.relationDepthGraph s.carrier adjacency (s.encode (root J S R)) ∈ M.sets ∧
      ZFSet.IsFunc s.carrier ZFSet.omega (M.relationDepthGraph s.carrier adjacency (s.encode (root J S R))) ∧
      ∀ x n, ZFSet.pair (s.encode x) (natSetCode n) ∈
        M.relationDepthGraph s.carrier adjacency (s.encode (root J S R)) ↔ n = depth J S R request x := by
  refine ⟨M.relationDepthGraph_mem pairing unions powers separation infinite hV hAdjacency
    (M.transitive hV (s.encode_mem _)), ?_, ?_⟩
  · rw [depthGraph_eq_graph J S R request M pairing unions separation infinite s edges hV]
    exact s.graph_isFunc natPresentation _
  · intro x n
    rw [depthGraph_eq_graph J S R request M pairing unions separation infinite s edges hV]
    have entry := s.pair_mem_graph natPresentation (fun x => ⟨depth J S R request x⟩) x ⟨n⟩
    exact entry.trans ⟨fun equal => (congrArg ULift.down equal).symm,
      fun equal => congrArg ULift.up equal.symm⟩

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def treeNonrootCarrier (V root : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun v => v ≠ root) V

noncomputable def treeIncomingGraph (V D parents source target root : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ d ∈ D, z = ZFSet.pair v d ∧ v ≠ root ∧
    ZFSet.pair d v ∈ target ∧ ∃ p ∈ V, ZFSet.pair d p ∈ source ∧ ZFSet.pair v p ∈ parents)
    (ZFSet.prod V D)

theorem pair_mem_treeIncomingGraph (V D parents source target root v d : ZFSet.{u}) :
    ZFSet.pair v d ∈ treeIncomingGraph V D parents source target root ↔
      v ∈ V ∧ d ∈ D ∧ v ≠ root ∧ ZFSet.pair d v ∈ target ∧
        ∃ p ∈ V, ZFSet.pair d p ∈ source ∧ ZFSet.pair v p ∈ parents := by
  rw [treeIncomingGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, d', hd, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, hd, body⟩
  · rintro ⟨hv, hd, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, hd⟩, v, hv, d, hd, rfl, body⟩

namespace BoundedFormula
def treeIncomingEntryFormula {k} (z V D parents source target root : Fin k) : BoundedFormula k :=
  exMem V (exMem D.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.conj (.neg (.equal 1 root.succ.succ))
      (.conj (pairMembershipFormula 0 1 target.succ.succ)
        (exMem V.succ.succ (.conj (pairMembershipFormula 1 0 source.succ.succ.succ)
          (pairMembershipFormula 2 0 parents.succ.succ.succ)))))))

theorem truth_treeIncomingEntryFormula {k} (z V D parents source target root : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (treeIncomingEntryFormula z V D parents source target root) env ↔
      ∃ v ∈ env V, ∃ d ∈ env D, env z = ZFSet.pair v d ∧ v ≠ env root ∧
        ZFSet.pair d v ∈ env target ∧ ∃ p ∈ env V,
          ZFSet.pair d p ∈ env source ∧ ZFSet.pair v p ∈ env parents := by
  simp only [treeIncomingEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem treeNonrootCarrier_mem (separation : SeparationSchema M.sets)
    {V root : ZFSet.{u}} (hV : V ∈ M.sets) (hRoot : root ∈ M.sets) :
    treeNonrootCarrier V root ∈ M.sets :=
  M.bounded_separation_mem separation (.neg (.equal 0 1))
    (extend root Fin.elim0) (Fin.cases hRoot (fun i => Fin.elim0 i)) hV

theorem treeIncomingGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {V D parents source target root : ZFSet.{u}} (hV : V ∈ M.sets) (hD : D ∈ M.sets)
    (hParents : parents ∈ M.sets) (hSource : source ∈ M.sets) (hTarget : target ∈ M.sets)
    (hRoot : root ∈ M.sets) : treeIncomingGraph V D parents source target root ∈ M.sets := by
  let params := extend V (extend D (extend parents (extend source (extend target (extend root Fin.elim0)))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.treeIncomingEntryFormula 0 1 2 3 4 5 6)
    params (Fin.cases hV (Fin.cases hD (Fin.cases hParents (Fin.cases hSource (Fin.cases hTarget
      (Fin.cases hRoot (fun i => Fin.elim0 i))))))) (M.prod_mem pairing unions powers separation hV hD)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.treeIncomingEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod V D) = treeIncomingGraph V D parents source target root := by
    apply ZFSet.ext
    intro z
    rw [treeIncomingGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_treeIncomingEntryFormula _ _ _ _ _ _ _ _)
  exact equal ▸ selected
end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars
open Forcing SetRealization SetFormula
universe u
variable (J S R : Type u) [Group J] (request : S → R)
variable (s : Presentation (Vertex J S R)) (t : Presentation (Dart J S R))
variable {parents src tgt : ZFSet.{u}}
variable (parentEntries : ∀ v p, ZFSet.pair (s.encode v) (s.encode p) ∈ parents ↔ parent J S R request v = p)
variable (sourceEntries : ∀ d v, ZFSet.pair (t.encode d) (s.encode v) ∈ src ↔ TileStars.source J S R request d = v)
variable (targetEntries : ∀ d v, ZFSet.pair (t.encode d) (s.encode v) ∈ tgt ↔ TileStars.target J S R request d = v)
include parentEntries sourceEntries targetEntries

theorem incomingGraph_entry (v : Vertex J S R) (nonroot : v ≠ root J S R) (d : Dart J S R) :
    ZFSet.pair (s.encode v) (t.encode d) ∈ treeIncomingGraph s.carrier t.carrier parents src tgt (s.encode (root J S R)) ↔
      incoming J S R request v nonroot = d := by
  rw [pair_mem_treeIncomingGraph]
  constructor
  · rintro ⟨_, _, _, target, p, hp, source, parent⟩
    obtain ⟨p, rfl⟩ := (s.mem_carrier p).1 hp
    have atTarget := (targetEntries d v).1 target
    have atSource := (sourceEntries d p).1 source
    have atParent := (parentEntries v p).1 parent
    apply (incoming_iff J S R request v nonroot d).2
    refine ⟨atTarget, ?_⟩
    rw [atSource, ← atParent]
    exact parent_depth J S R request v (fun zero => nonroot ((depth_zero_iff J S R request v).1 zero))
  · rintro rfl
    refine ⟨s.encode_mem v, t.encode_mem _, fun equal => nonroot (s.injective equal),
      (targetEntries _ v).2 (incoming_target J S R request v nonroot),
      s.encode (parent J S R request v), s.encode_mem _, ?_, (parentEntries v _).2 rfl⟩
    exact (sourceEntries _ _).2 (parent_eq J S R request v nonroot).symm

theorem incomingGraph_function :
    ZFSet.IsFunc (treeNonrootCarrier s.carrier (s.encode (root J S R))) t.carrier
      (treeIncomingGraph s.carrier t.carrier parents src tgt (s.encode (root J S R))) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨v, hv, d, hd, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 hz).1
    have body := (pair_mem_treeIncomingGraph _ _ _ _ _ _ _ _).1 hz
    exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_sep.2 ⟨hv, body.2.2.1⟩, hd⟩
  · intro v hv
    obtain ⟨hv, nonroot⟩ := ZFSet.mem_sep.1 hv
    obtain ⟨v, rfl⟩ := (s.mem_carrier v).1 hv
    have ne : v ≠ root J S R := fun eq => nonroot (congrArg s.encode eq)
    refine ⟨t.encode (incoming J S R request v ne),
      (incomingGraph_entry J S R request s t parentEntries sourceEntries targetEntries v ne _).2 rfl, ?_⟩
    intro d hd
    have body := (pair_mem_treeIncomingGraph _ _ _ _ _ _ _ _).1 hd
    obtain ⟨d, rfl⟩ := (t.mem_carrier d).1 body.2.1
    exact congrArg t.encode ((incomingGraph_entry J S R request s t parentEntries sourceEntries targetEntries v ne d).1 hd).symm

theorem incomingGraph_spec (M : Forcing.TransitiveGround.{u})
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hV : s.carrier ∈ M.sets) (hD : t.carrier ∈ M.sets)
    (hParents : parents ∈ M.sets) (hSource : src ∈ M.sets) (hTarget : tgt ∈ M.sets) :
    treeNonrootCarrier s.carrier (s.encode (root J S R)) ∈ M.sets ∧
      treeIncomingGraph s.carrier t.carrier parents src tgt (s.encode (root J S R)) ∈ M.sets ∧
      ZFSet.IsFunc (treeNonrootCarrier s.carrier (s.encode (root J S R))) t.carrier
        (treeIncomingGraph s.carrier t.carrier parents src tgt (s.encode (root J S R))) := by
  have hRoot := M.transitive hV (s.encode_mem (root J S R))
  exact ⟨M.treeNonrootCarrier_mem separation hV hRoot,
    M.treeIncomingGraph_mem pairing unions powers separation hV hD hParents hSource hTarget hRoot,
    incomingGraph_function J S R request s t parentEntries sourceEntries targetEntries⟩

end PartitionPilot.Compression.RecursiveMaps.CosetGeometry.TileStars

end OAI
