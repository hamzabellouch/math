import OAI.SetTheory.PartitionPrinciple.Forcing.AtomicTruth
import OAI.SetTheory.PartitionPrinciple.Model
import OAI.SetTheory.PartitionPrinciple.Transfinite.CountableCoding

namespace OAI


namespace PartitionPilot.Forcing


namespace SetFormula

universe u v

theorem map_extend {A : Type u} {B : Type v} {n : Nat}
    (f : A → B) (x : A) (env : Fin n → A) :
    (fun i => f (extend x env i)) = extend (f x) (fun i => f (env i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

theorem realize_ex (U : Set ZFSet.{u}) {n : Nat} (φ : SetFormula (n + 1))
    (env : Fin n → ZFSet.{u}) :
    Realize U (ex φ) env ↔ ∃ x ∈ U, Realize U φ (extend x env) := by
  classical
  simp only [ex, Realize, not_forall, not_not, exists_prop]

theorem realize_disj (U : Set ZFSet.{u}) {n : Nat} (φ ψ : SetFormula n)
    (env : Fin n → ZFSet.{u}) :
    Realize U (disj φ ψ) env ↔ Realize U φ env ∨ Realize U ψ env := by
  classical
  simp only [disj, Realize, not_and_or, not_not]

theorem realize_imp (U : Set ZFSet.{u}) {n : Nat} (φ ψ : SetFormula n)
    (env : Fin n → ZFSet.{u}) :
    Realize U (imp φ ψ) env ↔ (Realize U φ env → Realize U ψ env) := by
  classical
  simp only [imp, Realize, not_and, not_not]

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

abbrev Assignment (D : Name.NameDomain s) (n : Nat) := Fin n → D.names

def Forces (D : Name.NameDomain s) : {n : Nat} → SetFormula n → Assignment D n → P → Prop
  | _, .equal i j, env, p => Name.ForcesEq p (env i).val (env j).val
  | _, .mem i j, env, p => Name.ForcesMem p (env i).val (env j).val
  | _, .neg φ, env, p => ∀ q, q ≤ p → ¬ Forces D φ env q
  | _, .conj φ ψ, env, p => Forces D φ env p ∧ Forces D ψ env p
  | _, .all φ, env, p => ∀ τ : D.names, Forces D φ (extend τ env) p

theorem forces_mono (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p q : P} (h : Forces D φ env p) (qp : q ≤ p) :
    Forces D φ env q := by
  induction φ generalizing p q with
  | equal i j => exact Name.forcesEq_mono h qp
  | mem i j => exact Name.forcesMem_mono h qp
  | neg φ _ => exact fun r rq => h r (rq.trans qp)
  | conj φ ψ ihφ ihψ => exact ⟨ihφ env h.1 qp, ihψ env h.2 qp⟩
  | all φ ih => exact fun τ => ih (extend τ env) (h τ) qp

theorem forces_of_dense (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (dense : DenseBelow p {q | Forces D φ env q}) :
    Forces D φ env p := by
  induction φ generalizing p with
  | equal i j => exact Name.forcesEq_of_dense dense
  | mem i j => exact Name.forcesMem_of_dense dense
  | neg φ _ =>
    intro q qp hq
    obtain ⟨r, rq, hr⟩ := dense q qp
    exact hr r le_rfl (forces_mono D φ env hq rq)
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ env (denseBelow_mono dense (fun _ h => h.1)),
      ihψ env (denseBelow_mono dense (fun _ h => h.2))⟩
  | all φ ih =>
    exact fun τ => ih (extend τ env) (denseBelow_mono dense (fun _ h => h τ))

theorem not_forces_refine_neg (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (bad : ¬ Forces D φ env p) :
    ∃ q, q ≤ p ∧ Forces D (.neg φ) env q := by
  classical
  have missing : ¬ DenseBelow p {q | Forces D φ env q} := fun h => bad (forces_of_dense D φ env h)
  change ¬ ∀ q, q ≤ p → ∃ r, r ≤ q ∧ Forces D φ env r at missing
  push Not at missing
  exact missing

theorem forces_ex_iff (D : Name.NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) (p : P) :
    Forces D (ex φ) env p ↔ DenseBelow p {q | ∃ τ : D.names, Forces D φ (extend τ env) q} := by
  classical
  change (∀ q, q ≤ p → ¬ ∀ τ : D.names, ∀ r, r ≤ q → ¬ Forces D φ (extend τ env) r) ↔ _
  constructor
  · intro h q qp
    have witness := h q qp
    push Not at witness
    obtain ⟨τ, r, rq, hφ⟩ := witness
    exact ⟨r, rq, τ, hφ⟩
  · intro dense q qp allNeg
    obtain ⟨r, rq, τ, hφ⟩ := dense q qp
    exact allNeg τ r rq hφ

noncomputable def evalAssignment (H : Set P) {D : Name.NameDomain s} {n : Nat}
    (env : Assignment D n) : Fin n → ZFSet.{u} := fun i => Name.eval H (env i).val

omit [Preorder P] in
theorem evalAssignment_extend (H : Set P) {D : Name.NameDomain s} {n : Nat}
    (τ : D.names) (env : Assignment D n) :
    evalAssignment H (extend τ env) = extend (Name.eval H τ.val) (evalAssignment H env) :=
  map_extend (fun τ : D.names => Name.eval H τ.val) τ env

end SetFormula



namespace SetFormula

universe u

def liftIndex {n m : Nat} (f : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 (fun i => (f i).succ)

theorem extend_liftIndex {n m : Nat} {A : Type u} (f : Fin n → Fin m)
    (x : A) (env : Fin m → A) :
    (fun i => extend x env (liftIndex f i)) = extend x (fun i => env (f i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

def reindex : {n m : Nat} → (Fin n → Fin m) → SetFormula n → SetFormula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .neg φ => .neg (reindex f φ)
  | _, _, f, .conj φ ψ => .conj (reindex f φ) (reindex f ψ)
  | _, _, f, .all φ => .all (reindex (liftIndex f) φ)

theorem realize_reindex (U : Set ZFSet.{u}) {n m : Nat} (f : Fin n → Fin m)
    (φ : SetFormula n) (env : Fin m → ZFSet.{u}) :
    Realize U (reindex f φ) env ↔ Realize U φ (fun i => env (f i)) := by
  induction φ generalizing m with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih f env)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f env) (ihψ f env)
  | all φ ih =>
    change (∀ x ∈ U, Realize U (reindex (liftIndex f) φ) (extend x env)) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    rw [ih, extend_liftIndex]

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

def DecisionWitness (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) : Set P := {p | Forces D φ env p ∨ Forces D (.neg φ) env p}

theorem decisionWitness_dense (D : Name.NameDomain s) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) : Dense (DecisionWitness D φ env) := by
  classical
  intro p
  by_cases possible : ∃ q, q ≤ p ∧ Forces D φ env q
  · obtain ⟨q, qp, hq⟩ := possible
    exact ⟨q, qp, Or.inl hq⟩
  · exact ⟨p, le_rfl, Or.inr (fun q qp hq => possible ⟨q, qp, hq⟩)⟩

def AllDecisionWitness (D : Name.NameDomain s) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) : Set P :=
  {p | Forces D (.all φ) env p ∨ ∃ τ : D.names, Forces D (.neg φ) (extend τ env) p}

theorem allDecisionWitness_dense (D : Name.NameDomain s) {n : Nat}
    (φ : SetFormula (n + 1)) (env : Assignment D n) : Dense (AllDecisionWitness D φ env) := by
  classical
  intro p
  by_cases h : Forces D (.all φ) env p
  · exact ⟨p, le_rfl, Or.inl h⟩
  · change ¬ ∀ τ : D.names, Forces D φ (extend τ env) p at h
    push Not at h
    obtain ⟨τ, bad⟩ := h
    obtain ⟨q, qp, neg⟩ := not_forces_refine_neg D φ (extend τ env) bad
    exact ⟨q, qp, Or.inr ⟨τ, neg⟩⟩

def formulaFamily (D : Name.NameDomain s) : Set (Set P) :=
  Name.atomicFamily D ∪ {E |
    (∃ (n : Nat) (φ : SetFormula n) (env : Assignment D n), E = DecisionWitness D φ env) ∨
    ∃ (n : Nat) (φ : SetFormula (n + 1)) (env : Assignment D n), E = AllDecisionWitness D φ env}

end SetFormula



namespace SetFormula

universe u v

def extendMany {n : Nat} {A : Type v} : (k : Nat) →
    (Fin k → A) → (Fin n → A) → Fin (n + k) → A
  | 0, _, env => env
  | k + 1, fields, env => extend (fields 0) (extendMany k (fun j => fields j.succ) env)

def prefixIndex (n : Nat) : (k : Nat) → Fin k → Fin (n + k)
  | 0, i => Fin.elim0 i
  | k + 1, i => Fin.cases 0 (fun j => (prefixIndex n k j).succ) i

def suffixIndex (n : Nat) : (k : Nat) → Fin n → Fin (n + k)
  | 0, i => i
  | k + 1, i => (suffixIndex n k i).succ

theorem extendMany_prefix {n : Nat} {A : Type v} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A) (i : Fin k) :
    extendMany k fields env (prefixIndex n k i) = fields i := by
  induction k with
  | zero => exact Fin.elim0 i
  | succ k ih =>
    exact Fin.cases rfl (fun j => ih (fun a => fields a.succ) j) i

theorem extendMany_suffix {n : Nat} {A : Type v} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A) (i : Fin n) :
    extendMany k fields env (suffixIndex n k i) = env i := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun a => fields a.succ)

theorem extendMany_members {n : Nat} {A : Type v} {U : Set A} (k : Nat)
    (fields : Fin k → A) (env : Fin n → A)
    (fieldMembers : ∀ i, fields i ∈ U) (envMembers : ∀ i, env i ∈ U) :
    ∀ i, extendMany k fields env i ∈ U := by
  induction k with
  | zero => exact envMembers
  | succ k ih =>
    intro i
    exact Fin.cases (fieldMembers 0)
      (ih (fun i => fields i.succ) (fun i => fieldMembers i.succ)) i

def exBlock {n : Nat} : (k : Nat) → SetFormula (n + k) → SetFormula n
  | 0, body => body
  | k + 1, body => exBlock k (ex body)

theorem realize_exBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (body : SetFormula (n + k)) (env : Fin n → ZFSet.{u}) :
    Realize U (exBlock k body) env ↔
      ∃ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ U) ∧
        Realize U body (extendMany k fields env) := by
  induction k with
  | zero =>
    constructor
    · intro value
      exact ⟨Fin.elim0, fun i => Fin.elim0 i, value⟩
    · rintro ⟨_, _, value⟩
      exact value
  | succ k ih =>
    rw [exBlock, ih]
    constructor
    · rintro ⟨fields, members, rest⟩
      obtain ⟨first, hfirst, value⟩ := (realize_ex U _ _).1 rest
      let combined : Fin (k + 1) → ZFSet.{u} := Fin.cases first fields
      refine ⟨combined, ?_, ?_⟩
      · intro i
        exact Fin.cases hfirst members i
      · exact value
    · rintro ⟨fields, members, value⟩
      refine ⟨fun i => fields i.succ, fun i => members i.succ, ?_⟩
      exact (realize_ex U _ _).2 ⟨fields 0, members 0, value⟩

def conjBlock {n : Nat} : (k : Nat) → (Fin k → SetFormula n) → SetFormula n
  | 0, _ => .all (.equal 0 0)
  | k + 1, clauses => .conj (clauses 0) (conjBlock k (fun i => clauses i.succ))

theorem realize_conjBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (clauses : Fin k → SetFormula n) (env : Fin n → ZFSet.{u}) :
    Realize U (conjBlock k clauses) env ↔ ∀ i, Realize U (clauses i) env := by
  induction k with
  | zero =>
    exact ⟨fun _ i => Fin.elim0 i, fun _ _ _ => rfl⟩
  | succ k ih =>
    change (Realize U (clauses 0) env ∧ Realize U (conjBlock k (fun i => clauses i.succ)) env) ↔ _
    rw [ih]
    exact ⟨fun h => Fin.cases h.1 h.2, fun h => ⟨h 0, fun i => h i.succ⟩⟩

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] {s : Presentation P}

theorem forcing_truth (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) :
    Realize (D.values {p | H.mem p}) φ (evalAssignment {p | H.mem p} env) ↔
      ∃ p, H.mem p ∧ Forces D φ env p := by
  have atoms : H.GenericFor (Name.atomicFamily D) := fun E hE dense => generic E (Or.inl hE) dense
  induction φ with
  | equal i j => exact Name.eval_eq_iff_forcesEq D H atoms (env i).property (env j).property
  | mem i j => exact Name.eval_mem_iff_forcesMem D H atoms (env i).property (env j).property
  | neg φ ih =>
    constructor
    · intro notTrue
      obtain ⟨p, hp, good | bad⟩ := generic (DecisionWitness D φ env)
        (Or.inr (Or.inl ⟨_, φ, env, rfl⟩)) (decisionWitness_dense D φ env)
      · exact False.elim (notTrue ((ih env).2 ⟨p, hp, good⟩))
      · exact ⟨p, hp, bad⟩
    · rintro ⟨p, hp, neg⟩ truth
      obtain ⟨q, hq, hφ⟩ := (ih env).1 truth
      obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
      exact neg r rp (forces_mono D φ env hφ rq)
  | conj φ ψ ihφ ihψ =>
    constructor
    · rintro ⟨hφ, hψ⟩
      obtain ⟨p, hp, fp⟩ := (ihφ env).1 hφ
      obtain ⟨q, hq, fq⟩ := (ihψ env).1 hψ
      obtain ⟨r, hr, rp, rq⟩ := H.directed hp hq
      exact ⟨r, hr, forces_mono D φ env fp rp, forces_mono D ψ env fq rq⟩
    · rintro ⟨p, hp, hφ, hψ⟩
      exact ⟨(ihφ env).2 ⟨p, hp, hφ⟩, (ihψ env).2 ⟨p, hp, hψ⟩⟩
  | all φ ih =>
    constructor
    · intro allTrue
      obtain ⟨p, hp, good | bad⟩ := generic (AllDecisionWitness D φ env)
        (Or.inr (Or.inr ⟨_, φ, env, rfl⟩)) (allDecisionWitness_dense D φ env)
      · exact ⟨p, hp, good⟩
      · obtain ⟨τ, neg⟩ := bad
        have truth := allTrue (Name.eval {q | H.mem q} τ.val) ⟨τ, rfl⟩
        rw [← evalAssignment_extend] at truth
        obtain ⟨q, hq, hφ⟩ := (ih (extend τ env)).1 truth
        obtain ⟨r, _, rp, rq⟩ := H.directed hp hq
        exact False.elim (neg r rp (forces_mono D φ (extend τ env) hφ rq))
    · rintro ⟨p, hp, allForced⟩ x hx
      obtain ⟨τ, rfl⟩ := hx
      have truth := (ih (extend τ env)).2 ⟨p, hp, allForced τ⟩
      rw [evalAssignment_extend] at truth
      exact truth

theorem forces_sound (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula n)
    (env : Assignment D n) {p : P} (hp : H.mem p) (h : Forces D φ env p) :
    Realize (D.values {q | H.mem q}) φ (evalAssignment {q | H.mem q} env) :=
  (forcing_truth D H generic φ env).2 ⟨p, hp, h⟩

theorem ex_witness_in_filter (D : Name.NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D)) {n : Nat} (φ : SetFormula (n + 1))
    (env : Assignment D n) {p : P} (hp : H.mem p) (h : Forces D (ex φ) env p) :
    ∃ τ : D.names, ∃ q, H.mem q ∧ q ≤ p ∧ Forces D φ (extend τ env) q := by
  have truth := forces_sound D H generic (ex φ) env hp h
  obtain ⟨x, hx, hxφ⟩ := (realize_ex _ φ _).1 truth
  obtain ⟨τ, rfl⟩ := hx
  rw [← evalAssignment_extend] at hxφ
  obtain ⟨q, hq, hφ⟩ := (forcing_truth D H generic φ (extend τ env)).1 hxφ
  obtain ⟨r, hr, rp, rq⟩ := H.directed hp hq
  exact ⟨τ, r, hr, rp, forces_mono D φ (extend τ env) hφ rq⟩

end SetFormula



namespace SetFormula
universe u

def allBlock {n : Nat} : (k : Nat) → SetFormula (n + k) → SetFormula n
  | 0, body => body
  | k + 1, body => allBlock k (.all body)

theorem realize_allBlock (U : Set ZFSet.{u}) {n : Nat} (k : Nat)
    (body : SetFormula (n + k)) (env : Fin n → ZFSet.{u}) :
    Realize U (allBlock k body) env ↔
      ∀ fields : Fin k → ZFSet.{u}, (∀ i, fields i ∈ U) →
        Realize U body (extendMany k fields env) := by
  induction k with
  | zero =>
    exact ⟨fun h _ _ => h, fun h => h Fin.elim0 (fun i => Fin.elim0 i)⟩
  | succ k ih =>
    rw [allBlock, ih]
    constructor
    · intro h fields ground
      exact h (fun i => fields i.succ) (fun i => ground i.succ) (fields 0) (ground 0)
    · intro h fields ground x hx
      exact h (Fin.cases x fields) (Fin.cases hx ground)

end SetFormula



namespace SetFormula

open SetRealization
universe u
variable {P : Type u} {s : Presentation P}

theorem realize_extensionality (D : Name.NameDomain s) (H : Set P) :
    Realize (D.values H) extensionality Fin.elim0 := by
  classical
  simp only [extensionality, Realize, imp, extend, Fin.cases_zero,
    not_and, not_not]
  intro x hx y hy agree
  apply D.values_extensionality H hx hy
  intro z hz
  exact ⟨(agree z hz).1, (agree z hz).2⟩

theorem realize_foundation (D : Name.NameDomain s) (H : Set P) :
    Realize (D.values H) foundation Fin.elim0 := by
  classical
  simp only [foundation, Realize, imp, ex, extend, Fin.cases_zero,
    not_and, not_not, not_forall, exists_prop]
  intro x hx inhabited
  obtain ⟨w, _, wx⟩ := inhabited
  have nonempty : x ≠ ∅ := by
    intro eq
    rw [eq] at wx
    exact ZFSet.notMem_empty w wx
  obtain ⟨y, hy, yx, disjoint⟩ := D.values_foundation H hx nonempty
  refine ⟨y, hy, yx, ?_⟩
  rintro ⟨z, _, zx, zy⟩
  have member : z ∈ x ∩ y := ZFSet.mem_inter.2 ⟨zx, zy⟩
  rw [disjoint] at member
  exact ZFSet.notMem_empty z member

theorem basic_axioms_in_generic [Preorder P] (D : Name.NameDomain s)
    (H : ConditionFilter P) (generic : H.GenericFor (formulaFamily D)) :
    ∃ p, H.mem p ∧ Forces D (.conj extensionality foundation) Fin.elim0 p := by
  apply (forcing_truth D H generic (.conj extensionality foundation) Fin.elim0).1
  have env : evalAssignment {p | H.mem p} (Fin.elim0 : Assignment D 0) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [env]
  exact ⟨realize_extensionality D _, realize_foundation D _⟩

end SetFormula



namespace SetFormula

open Compression.RecursiveMaps

def natCode : {n : Nat} → SetFormula n → Nat
  | _, .equal i j => natPair 0 (natPair i.val j.val)
  | _, .mem i j => natPair 1 (natPair i.val j.val)
  | _, .neg φ => natPair 2 (natCode φ)
  | _, .conj φ ψ => natPair 3 (natPair (natCode φ) (natCode ψ))
  | _, .all φ => natPair 4 (natCode φ)

theorem natCode_injective {n : Nat} : Function.Injective (@natCode n) := by
  intro φ
  induction φ with
  | equal i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.equal (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | mem i j =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.mem (Fin.ext parts.1) (Fin.ext parts.2)
    all_goals have bad := (natPair_injective eq).1; omega
  | neg φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.neg (ih (natPair_injective eq).2)
    all_goals have bad := (natPair_injective eq).1; omega
  | conj φ χ ihφ ihχ =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have parts := natPair_injective (natPair_injective eq).2
      exact congrArg₂ SetFormula.conj (ihφ parts.1) (ihχ parts.2)
    · have bad := (natPair_injective eq).1; omega
  | all φ ih =>
    intro ψ eq
    cases ψ <;> simp only [natCode] at eq
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · have bad := (natPair_injective eq).1; omega
    · exact congrArg SetFormula.all (ih (natPair_injective eq).2)

instance countable (n : Nat) : Countable (SetFormula n) := natCode_injective.countable

end SetFormula

end PartitionPilot.Forcing

end OAI
