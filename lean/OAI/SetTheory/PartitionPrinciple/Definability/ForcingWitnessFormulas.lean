import OAI.SetTheory.PartitionPrinciple.Geometry.GroundDefinableSelections

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def forcingWitnessFormula {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 2))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (z y : Fin m) : SetFormula m :=
  ex (exConditions (params A.carrier).succ
    (.conj (orderedPairFormula z.succ.succ 1 0)
      (.conj (domainApplication A.domain (fun j => (params j).succ.succ) 1)
        (.conj (domainApplication A.domain (fun j => (params j).succ.succ) y.succ.succ)
          (forcingTranslation A φ (fun j => (params j).succ.succ) 0
            (extend 1 (extend y.succ.succ (fun j => (names j).succ.succ))))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_forcingWitnessFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 2))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (zi yi : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params A.carrier) = s.carrier) (ho : env (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => env (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => env (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, env (names i) = (nameEnv i).val.val)
    (hz : env zi ∈ M.sets) (hy : env yi ∈ M.sets) :
    Realize M.sets (forcingWitnessFormula A φ params names zi yi) env ↔
      ∃ σ : D.names, ∃ p, env zi = ZFSet.pair σ.val.val (s.encode p) ∧
        ∃ ρ : D.names, ρ.val.val = env yi ∧ Forces D φ (extend σ (extend ρ nameEnv)) p := by
  rw [forcingWitnessFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, body⟩
    obtain ⟨p, shape, source, target, forced⟩ := (M.realize_exConditions s (params A.carrier).succ _
      (extend x env) carrier hc).1 body
    rw [realize_domainApplication] at source target
    obtain ⟨σ, eq⟩ := (domain x hx).1 source
    obtain ⟨ρ, eqρ⟩ := (domain (env yi) hy).1 target
    let e := extend (s.encode p) (extend x env)
    have raw := (M.realize_orderedPairFormula pairing zi.succ.succ 1 0 e hz hx
      (M.transitive carrier (s.encode_mem p))).1 shape
    refine ⟨σ, p, raw.trans (congrArg (fun z => ZFSet.pair z (s.encode p)) eq.symm), ρ, eqρ, ?_⟩
    exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ) 0 (extend 1 (extend yi.succ.succ (fun j => (names j).succ.succ)))
      e hc ho atomic domain p (extend σ (extend ρ nameEnv)) rfl
      (Fin.cases eq.symm (Fin.cases eqρ.symm hnames))).1 forced
  · rintro ⟨σ, p, shape, ρ, eqρ, forced⟩
    refine ⟨σ.val.val, ground σ.val σ.property, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ _ (extend σ.val.val env) carrier hc).2
    let e := extend (s.encode p) (extend σ.val.val env)
    refine ⟨p, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing zi.succ.succ 1 0 e hz (ground σ.val σ.property)
        (M.transitive carrier (s.encode_mem p))).2 shape
    · rw [realize_domainApplication]
      exact (domain σ.val.val (ground σ.val σ.property)).2 ⟨σ, rfl⟩
    · rw [realize_domainApplication]
      exact (domain (env yi) hy).2 ⟨ρ, eqρ⟩
    · exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ.succ) 0 (extend 1 (extend yi.succ.succ (fun j => (names j).succ.succ)))
        e hc ho atomic domain p (extend σ (extend ρ nameEnv)) rfl
        (Fin.cases rfl (Fin.cases eqρ.symm hnames))).2 forced

end PartitionPilot.Forcing.TransitiveGround

end OAI
