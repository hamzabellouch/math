import OAI.SetTheory.PartitionPrinciple.Forcing.ConditionQuantifiers
import OAI.SetTheory.PartitionPrinciple.Geometry.AtomicEqualitySteps

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

def atomicApplication {k m : Nat} (E : SetFormula (k + 3))
    (params : Fin k → Fin m) (p x y : Fin m) : SetFormula m :=
  reindex (extend p (extend x (extend y params))) E

theorem realize_atomicApplication (U : Set ZFSet.{u}) {k m : Nat} (E : SetFormula (k + 3))
    (params : Fin k → Fin m) (p x y : Fin m) (env : Fin m → ZFSet.{u}) :
    Realize U (atomicApplication E params p x y) env ↔
      Realize U E (extend (env p) (extend (env x) (extend (env y) (fun i => env (params i))))) := by
  rw [atomicApplication, realize_reindex, map_extend, map_extend, map_extend]

def membershipFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  allConditions (params c) <|
    imp (pairMembershipFormula 0 p.succ (params o).succ) <|
    exConditions (params c).succ <| ex <|
    exConditions (params c).succ.succ.succ <|
    .conj (pairMembershipFormula 1 0 τ.succ.succ.succ.succ) <|
    .conj (pairMembershipFormula 2 3 (params o).succ.succ.succ.succ) <|
    .conj (pairMembershipFormula 2 0 (params o).succ.succ.succ.succ) <|
    atomicApplication E (fun j => (params j).succ.succ.succ.succ) 2 σ.succ.succ.succ.succ 1

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_conditionLE (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {m : Nat} (i j o : Fin m) (env : Fin m → ZFSet.{u}) (p q : P)
    (hi : env i = s.encode p) (hj : env j = s.encode q) (ho : env o = s.conditionOrder) :
    Realize M.sets (pairMembershipFormula i j o) env ↔ p ≤ q := by
  have hp : env i ∈ M.sets := hi ▸ M.transitive carrier (s.encode_mem p)
  have hq : env j ∈ M.sets := hj ▸ M.transitive carrier (s.encode_mem q)
  have horder : env o ∈ M.sets := ho ▸ order
  rw [M.realize_pairMembershipFormula pairing i j o env hp hq horder, hi, hj, ho,
    s.pair_mem_conditionOrder]

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def RelationMeaning (D : Name.NameDomain s) (R : P → Name s → Name s → Prop) {k : Nat} (E : SetFormula (k + 3))
    (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ (p : P) (σ τ : D.names),
    Realize M.sets E (extend (s.encode p) (extend σ.val.val (extend τ.val.val constants))) ↔
      R p σ.val τ.val

theorem realize_relationMembership (D : Name.NameDomain s)
    (R : P → Name s → Name s → Prop)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RelationMeaning s D R E (fun j => env (params j)))
    (p : P) (σ τ : D.names) (hp : env pi = s.encode p)
    (hσ : env si = σ.val.val) (hτ : env ti = τ.val.val) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      Name.RelationMembership R p σ.val τ.val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔
    ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ ν r,
      Name.Entry ν τ.val r ∧ t ≤ r ∧ R t σ.val ν
  apply forall_congr'
  intro q
  rw [realize_imp, M.realize_conditionLE s pairing carrier order 0 pi.succ (params o).succ
    (extend (s.encode q) env) q p rfl hp ho]
  apply forall_congr'
  intro _
  rw [M.realize_exConditions s (params c).succ _ (extend (s.encode q) env) carrier hc]
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨v, hv, rest⟩ := (realize_ex M.sets _ _).1 ht
    obtain ⟨r, entry, tq, tr, eq⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have raw := (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
      hv (M.transitive carrier (s.encode_mem r)) hτM).1 entry
    change ZFSet.pair v (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let ν : Name s := ⟨v, Name.isName_of_pair_mem τ.val v r raw⟩
    have hν : ν ∈ D.names := D.children τ.property raw
    have forced := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 eq
    change Realize M.sets E (extend (s.encode t) (extend (env si)
      (extend v (fun j => env (params j))))) at forced
    rw [hσ] at forced
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      ν, r, raw, (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (meaning t σ ⟨ν, hν⟩).1 forced⟩
  · rintro ⟨t, tq, ν, r, entry, tr, forced⟩
    have hν : ν ∈ D.names := D.children τ.property entry
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨ν.val, ground ν hν, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend ν.val (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend ν.val (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · apply (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        (ground ν hν) (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair ν.val (s.encode r) ∈ env ti
      rw [hτ]
      exact entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · apply (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
      change Realize M.sets E (extend (s.encode t) (extend (env si)
        (extend ν.val (fun j => env (params j)))))
      rw [hσ]
      exact (meaning t σ ⟨ν, hν⟩).2 forced

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.SetFormula

def swapEquality {k : Nat} (E : SetFormula (k + 3)) : SetFormula (k + 3) :=
  atomicApplication E (fun j => j.succ.succ.succ) 0 2 1

def matchingDirectionFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  .all <| allConditions (params c).succ <|
    imp (pairMembershipFormula 1 0 σ.succ.succ) <|
    allConditions (params c).succ.succ <|
    imp (.conj (pairMembershipFormula 0 p.succ.succ.succ (params o).succ.succ.succ)
      (pairMembershipFormula 0 1 (params o).succ.succ.succ)) <|
    membershipFormula E c o (fun j => (params j).succ.succ.succ) 0 2 τ.succ.succ.succ

def equalityStepFormula {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k)
    (params : Fin k → Fin m) (p σ τ : Fin m) : SetFormula m :=
  .conj (matchingDirectionFormula E c o params p σ τ)
    (matchingDirectionFormula (swapEquality E) c o params p τ σ)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} (s : Presentation P)

theorem relationMeaning_swap (D : Name.NameDomain s) (R : P → Name s → Name s → Prop)
    {k : Nat} (E : SetFormula (k + 3)) (constants : Fin k → ZFSet.{u})
    (meaning : M.RelationMeaning s D R E constants) :
    M.RelationMeaning s D (fun p σ τ => R p τ σ) (swapEquality E) constants := by
  intro p σ τ
  rw [swapEquality, realize_atomicApplication]
  exact meaning p τ σ

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
