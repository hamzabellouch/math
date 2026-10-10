import OAI.SetTheory.PartitionPrinciple.Forcing.SymmetricGroundForcing

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

def separationEntryFormula {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (z τ : Fin m) : SetFormula m :=
  ex (exConditions (params A.carrier).succ (exConditions (params A.carrier).succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 2 0 τ.succ.succ.succ)
        (.conj (pairMembershipFormula 1 0 (params A.order).succ.succ.succ)
          (forcingTranslation A φ (fun j => (params j).succ.succ.succ) 1
            (extend 2 (fun i => (names i).succ.succ.succ))))))))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] (s : Presentation P)

theorem realize_separationEntryFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    {k n m : Nat} (A : ForcingPrimitives k) (φ : SetFormula (n + 1))
    (params : Fin k → Fin m) (names : Fin n → Fin m) (zi ti : Fin m) (env : Fin m → ZFSet.{u})
    (hc : env (params A.carrier) = s.carrier) (ho : env (params A.order) = s.conditionOrder)
    (atomic : M.EqualityMeaning s D A.equality (fun j => env (params j)))
    (domain : M.DomainMeaning s D A.domain (fun j => env (params j)))
    (nameEnv : Assignment D n) (hnames : ∀ i, env (names i) = (nameEnv i).val.val)
    (τ : D.names) (hτ : env ti = τ.val.val) (hz : env zi ∈ M.sets) :
    Realize M.sets (separationEntryFormula A φ params names zi ti) env ↔
      env zi ∈ (Name.separationName D φ nameEnv τ.val).val := by
  have hτM : env ti ∈ M.sets := hτ ▸ ground τ.val τ.property
  rw [separationEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, rest⟩
    obtain ⟨p, rest⟩ := (M.realize_exConditions s (params A.carrier).succ _ (extend x env) carrier hc).1 rest
    obtain ⟨r, shape, old, pr, forced⟩ := (M.realize_exConditions s (params A.carrier).succ.succ _
      (extend (s.encode p) (extend x env)) carrier hc).1 rest
    let e := extend (s.encode r) (extend (s.encode p) (extend x env))
    have raw := (M.realize_pairMembershipFormula pairing 2 0 ti.succ.succ.succ e hx
      (M.transitive carrier (s.encode_mem r)) hτM).1 old
    change ZFSet.pair x (s.encode r) ∈ env ti at raw
    rw [hτ] at raw
    let σ : Name s := ⟨x, Name.isName_of_pair_mem τ.val x r raw⟩
    have hσ : σ ∈ D.names := D.children τ.property raw
    have eq := (M.realize_orderedPairFormula pairing zi.succ.succ.succ 2 1 e hz hx
      (M.transitive carrier (s.encode_mem p))).1 shape
    have forcing := (M.realize_forcingTranslation s D ground pairing carrier order A φ
      (fun j => (params j).succ.succ.succ) 1 (extend 2 (fun i => (names i).succ.succ.succ))
      e hc ho atomic domain p (extend ⟨σ, hσ⟩ nameEnv) rfl
      (fun i => Fin.cases rfl (fun j => hnames j) i)).1 forced
    change env zi = ZFSet.pair x (s.encode p) at eq
    rw [eq]
    exact (Name.entry_separationName D φ nameEnv τ.val σ p).2
      ⟨r, raw, (M.realize_conditionLE s pairing carrier order 1 0 (params A.order).succ.succ.succ
        e p r rfl rfl ho).1 pr, hσ, forcing⟩
  · intro member
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (Name.separationName D φ nameEnv τ.val) member
    have entry : Name.Entry σ (Name.separationName D φ nameEnv τ.val) p := by
      change ZFSet.pair σ.val (s.encode p) ∈ (Name.separationName D φ nameEnv τ.val).val
      rw [← eq]
      exact member
    obtain ⟨r, old, pr, hσ, forced⟩ := (Name.entry_separationName D φ nameEnv τ.val σ p).1 entry
    refine ⟨σ.val, ground σ hσ, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ _ (extend σ.val env) carrier hc).2
    refine ⟨p, ?_⟩
    apply (M.realize_exConditions s (params A.carrier).succ.succ _
      (extend (s.encode p) (extend σ.val env)) carrier hc).2
    let e := extend (s.encode r) (extend (s.encode p) (extend σ.val env))
    refine ⟨r, ?_, ?_, ?_, ?_⟩
    · exact (M.realize_orderedPairFormula pairing zi.succ.succ.succ 2 1 e hz (ground σ hσ)
        (M.transitive carrier (s.encode_mem p))).2 eq
    · apply (M.realize_pairMembershipFormula pairing 2 0 ti.succ.succ.succ e (ground σ hσ)
        (M.transitive carrier (s.encode_mem r)) hτM).2
      change ZFSet.pair σ.val (s.encode r) ∈ env ti
      rw [hτ]
      exact old
    · exact (M.realize_conditionLE s pairing carrier order 1 0 (params A.order).succ.succ.succ
        e p r rfl rfl ho).2 pr
    · exact (M.realize_forcingTranslation s D ground pairing carrier order A φ
        (fun j => (params j).succ.succ.succ) 1 (extend 2 (fun i => (names i).succ.succ.succ))
        e hc ho atomic domain p (extend ⟨σ, hσ⟩ nameEnv) rfl
        (fun i => Fin.cases rfl (fun j => hnames j) i)).2 forced

end PartitionPilot.Forcing.TransitiveGround

end OAI
