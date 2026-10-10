import OAI.SetTheory.PartitionPrinciple.Definability.CodedEqualityRelations

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

def RawRelationMeaning {k : Nat} (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (E : SetFormula (k + 3)) (constants : Fin k → ZFSet.{u}) : Prop :=
  ∀ p x, x ∈ M.sets → ∀ y, y ∈ M.sets →
    (Realize M.sets E (extend (s.encode p) (extend x (extend y constants))) ↔ R p x y)

def RawMembership (R : P → ZFSet.{u} → ZFSet.{u} → Prop) (p : P) (x y : ZFSet.{u}) : Prop :=
  ∀ q, q ≤ p → ∃ t, t ≤ q ∧ ∃ v ∈ M.sets, ∃ r,
    ZFSet.pair v (s.encode r) ∈ y ∧ t ≤ r ∧ R t x v

def RawMatching (R : P → ZFSet.{u} → ZFSet.{u} → Prop) (p : P) (x y : ZFSet.{u}) : Prop :=
  ∀ v ∈ M.sets, ∀ r, ZFSet.pair v (s.encode r) ∈ x →
    ∀ q, q ≤ p → q ≤ r → M.RawMembership s R q v y

def RawEqualityStep (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (p : P) (x y : ZFSet.{u}) : Prop :=
  M.RawMatching s R p x y ∧ M.RawMatching s (fun t v w => R t w v) p y x

theorem rawEqualityStep_mono {R S : P → ZFSet.{u} → ZFSet.{u} → Prop}
    (mono : ∀ p x y, R p x y → S p x y) {p : P} {x y : ZFSet.{u}}
    (h : M.RawEqualityStep s R p x y) : M.RawEqualityStep s S p x y := by
  constructor
  · intro v hv r entry q qp qr t tq
    obtain ⟨a, hat, w, hw, b, eb, ab, rel⟩ := h.1 v hv r entry q qp qr t tq
    exact ⟨a, hat, w, hw, b, eb, ab, mono a v w rel⟩
  · intro v hv r entry q qp qr t tq
    obtain ⟨a, hat, w, hw, b, eb, ab, rel⟩ := h.2 v hv r entry q qp qr t tq
    exact ⟨a, hat, w, hw, b, eb, ab, mono a w v rel⟩

theorem realize_rawMembership (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (membershipFormula E c o params pi si ti) env ↔
      M.RawMembership s R p (env si) (env ti) := by
  rw [membershipFormula, M.realize_allConditions s _ _ env carrier hc]
  change (∀ q : P, Realize M.sets _ (extend (s.encode q) env)) ↔ _
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
    obtain ⟨r, entry, tq, tr, rel⟩ := (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).1 rest
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    have lookup := (realize_atomicApplication M.sets E
      (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).1 rel
    exact ⟨t, (M.realize_conditionLE s pairing carrier order 2 3
      (params o).succ.succ.succ.succ e t q rfl rfl ho).1 tq,
      v, hv, r,
      (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        hv (M.transitive carrier (s.encode_mem r)) hτ).1 entry,
      (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).1 tr,
      (meaning t (env si) hσ v hv).1 lookup⟩
  · rintro ⟨t, tq, v, hv, r, entry, tr, rel⟩
    refine ⟨t, ?_⟩
    rw [realize_ex]
    refine ⟨v, hv, ?_⟩
    apply (M.realize_exConditions s (params c).succ.succ.succ _
      (extend v (extend (s.encode t) (extend (s.encode q) env))) carrier hc).2
    let e := extend (s.encode r) (extend v (extend (s.encode t) (extend (s.encode q) env)))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_pairMembershipFormula pairing 1 0 ti.succ.succ.succ.succ e
        hv (M.transitive carrier (s.encode_mem r)) hτ).2 entry
    · exact (M.realize_conditionLE s pairing carrier order 2 3
        (params o).succ.succ.succ.succ e t q rfl rfl ho).2 tq
    · exact (M.realize_conditionLE s pairing carrier order 2 0
        (params o).succ.succ.succ.succ e t r rfl rfl ho).2 tr
    · exact (realize_atomicApplication M.sets E
        (fun j => (params j).succ.succ.succ.succ) 2 si.succ.succ.succ.succ 1 e).2
        ((meaning t (env si) hσ v hv).2 rel)

theorem realize_rawMatching (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (matchingDirectionFormula E c o params pi si ti) env ↔
      M.RawMatching s R p (env si) (env ti) := by
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  apply forall_congr'
  intro v
  apply forall_congr'
  intro hv
  rw [M.realize_allConditions s (params c).succ _ (extend v env) carrier hc]
  apply forall_congr'
  intro r
  rw [realize_imp, M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
    (extend (s.encode r) (extend v env)) hv (M.transitive carrier (s.encode_mem r)) hσ]
  apply forall_congr'
  intro _
  rw [M.realize_allConditions s (params c).succ.succ _
    (extend (s.encode r) (extend v env)) carrier hc]
  apply forall_congr'
  intro q
  let e := extend (s.encode q) (extend (s.encode r) (extend v env))
  rw [realize_imp]
  change (Realize M.sets _ e ∧ Realize M.sets _ e → Realize M.sets _ e) ↔ _
  rw [M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
    (params o).succ.succ.succ e q p rfl hp ho,
    M.realize_conditionLE s pairing carrier order 0 1 (params o).succ.succ.succ e q r rfl rfl ho,
    M.realize_rawMembership s R pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning q rfl hv hτ]
  exact and_imp

theorem realize_rawEqualityStep (R : P → ZFSet.{u} → ZFSet.{u} → Prop)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k m : Nat} (E : SetFormula (k + 3)) (c o : Fin k) (params : Fin k → Fin m)
    (pi si ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params c) = s.carrier) (ho : env (params o) = s.conditionOrder)
    (meaning : M.RawRelationMeaning s R E (fun j => env (params j)))
    (p : P) (hp : env pi = s.encode p) (hσ : env si ∈ M.sets) (hτ : env ti ∈ M.sets) :
    Realize M.sets (equalityStepFormula E c o params pi si ti) env ↔
      M.RawEqualityStep s R p (env si) (env ti) := by
  have swapped : M.RawRelationMeaning s (fun t x y => R t y x) (swapEquality E)
      (fun j => env (params j)) := by
    intro t x hx y hy
    rw [swapEquality, realize_atomicApplication]
    exact meaning t y hy x hx
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_rawMatching s R pairing carrier order E c o params pi si ti
    env hc ho meaning p hp hσ hτ,
    M.realize_rawMatching s (fun t x y => R t y x) pairing carrier order
      (swapEquality E) c o params pi ti si env hc ho swapped p hp hτ hσ]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
