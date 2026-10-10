import OAI.SetTheory.PartitionPrinciple.Definability.EqualityStepSyntax

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_matchingDirection (D : Name.NameDomain s)
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
    Realize M.sets (matchingDirectionFormula E c o params pi si ti) env ↔
      ∀ ρ r, Name.Entry ρ σ.val r → ∀ q, q ≤ p → q ≤ r →
        Name.RelationMembership R q ρ τ.val := by
  have hσM : env si ∈ M.sets := hσ ▸ ground σ.val σ.property
  change (∀ v ∈ M.sets, Realize M.sets _ (extend v env)) ↔ _
  constructor
  · intro h ρ r entry q qp qr
    have hρ := D.children σ.property entry
    have first := (M.realize_allConditions s (params c).succ _
      (extend ρ.val env) carrier hc).1 (h ρ.val (ground ρ hρ)) r
    have raw : ZFSet.pair ρ.val (s.encode r) ∈ env si := hσ ▸ entry
    have guard := (M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
      (extend (s.encode r) (extend ρ.val env))
      (ground ρ hρ) (M.transitive carrier (s.encode_mem r)) hσM).2 raw
    have second := (realize_imp M.sets _ _ _).1 first guard
    have third := (M.realize_allConditions s (params c).succ.succ _
      (extend (s.encode r) (extend ρ.val env)) carrier hc).1 second q
    let e := extend (s.encode q) (extend (s.encode r) (extend ρ.val env))
    have body := (realize_imp M.sets _ _ e).1 third
      ⟨(M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
        (params o).succ.succ.succ e q p rfl hp ho).2 qp,
       (M.realize_conditionLE s pairing carrier order 0 1
        (params o).succ.succ.succ e q r rfl rfl ho).2 qr⟩
    exact (M.realize_relationMembership s D R ground pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning
      q ⟨ρ, hρ⟩ τ rfl rfl hτ).1 body
  · intro h v hv
    apply (M.realize_allConditions s (params c).succ _ (extend v env) carrier hc).2
    intro r
    apply (realize_imp M.sets _ _ _).2
    intro guard
    have raw := (M.realize_pairMembershipFormula pairing 1 0 si.succ.succ
      (extend (s.encode r) (extend v env)) hv (M.transitive carrier (s.encode_mem r)) hσM).1 guard
    change ZFSet.pair v (s.encode r) ∈ env si at raw
    rw [hσ] at raw
    let ρ : Name s := ⟨v, Name.isName_of_pair_mem σ.val v r raw⟩
    have hρ : ρ ∈ D.names := D.children σ.property raw
    apply (M.realize_allConditions s (params c).succ.succ _
      (extend (s.encode r) (extend v env)) carrier hc).2
    intro q
    let e := extend (s.encode q) (extend (s.encode r) (extend v env))
    apply (realize_imp M.sets _ _ e).2
    rintro ⟨qp, qr⟩
    apply (M.realize_relationMembership s D R ground pairing carrier order E c o
      (fun j => (params j).succ.succ.succ) 0 2 ti.succ.succ.succ e hc ho meaning
      q ⟨ρ, hρ⟩ τ rfl rfl hτ).2
    exact h ρ r raw q
      ((M.realize_conditionLE s pairing carrier order 0 pi.succ.succ.succ
        (params o).succ.succ.succ e q p rfl hp ho).1 qp)
      ((M.realize_conditionLE s pairing carrier order 0 1
        (params o).succ.succ.succ e q r rfl rfl ho).1 qr)

theorem realize_equalityStep (D : Name.NameDomain s)
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
    Realize M.sets (equalityStepFormula E c o params pi si ti) env ↔
      Name.EqualityStep R p σ.val τ.val := by
  change (Realize M.sets _ env ∧ Realize M.sets _ env) ↔ _
  rw [M.realize_matchingDirection s D R ground pairing carrier order E c o params pi si ti
    env hc ho meaning p σ τ hp hσ hτ,
    M.realize_matchingDirection s D (fun t ρ ν => R t ν ρ) ground pairing carrier order
      (swapEquality E) c o params pi ti si env hc ho
      (M.relationMeaning_swap s D R E _ meaning) p τ σ hp hτ hσ]
  exact (Name.equalityStep_dense R p σ.val τ.val).symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
