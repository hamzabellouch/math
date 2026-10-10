import OAI.SetTheory.PartitionPrinciple.Forcing.GroundGraphValueDescendantWitnesses

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

def codedPowerEntryFormula {k m : Nat} (N : SetFormula (k + 1))
    (params : Fin k → Fin m) (z W top : Fin m) : SetFormula m :=
  ex (.conj (.mem 0 W.succ) (.conj (domainApplication N (fun j => (params j).succ) 0)
    (orderedPairFormula z.succ 0 top.succ)))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u} [Preorder P] [OrderTop P] (s : Presentation P)

theorem realize_codedPowerEntryFormula (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {k m : Nat} (N : SetFormula (k + 1)) (params : Fin k → Fin m) (zi wi ti : Fin m)
    (env : Fin m → ZFSet.{u})
    (domain : M.DomainMeaning s D N (fun j => env (params j)))
    (top : env ti = s.encode ⊤) (htop : env ti ∈ M.sets) (hz : env zi ∈ M.sets) :
    Realize M.sets (codedPowerEntryFormula N params zi wi ti) env ↔
      env zi ∈ (Name.codedPower D (env wi)).val := by
  rw [codedPowerEntryFormula, realize_ex]
  constructor
  · rintro ⟨x, hx, hW, name, shape⟩
    rw [realize_domainApplication] at name
    obtain ⟨σ, rfl⟩ := (domain x hx).1 name
    have eq := (M.realize_orderedPairFormula pairing zi.succ 0 ti.succ
      (extend σ.val.val env) hz hx htop).1 shape
    change env zi = ZFSet.pair σ.val.val (env ti) at eq
    rw [eq, top]
    exact (Name.entry_codedPower D (env wi) σ.val ⊤).2 ⟨σ.property, hW, rfl⟩
  · intro member
    obtain ⟨σ, p, eq⟩ := Name.entries_cover (Name.codedPower D (env wi)) member
    have entry : Name.Entry σ (Name.codedPower D (env wi)) p := by
      change ZFSet.pair σ.val (s.encode p) ∈ (Name.codedPower D (env wi)).val
      rwa [← eq]
    obtain ⟨hσ, hW, rfl⟩ := (Name.entry_codedPower D (env wi) σ p).1 entry
    refine ⟨σ.val, ground σ hσ, hW, ?_, ?_⟩
    · rw [realize_domainApplication]
      exact (domain σ.val (ground σ hσ)).2 ⟨⟨σ, hσ⟩, rfl⟩
    · apply (M.realize_orderedPairFormula pairing zi.succ 0 ti.succ
        (extend σ.val env) hz (ground σ hσ) htop).2
      change env zi = ZFSet.pair σ.val (env ti)
      rwa [top]

theorem codedPower_mem (D : Name.NameDomain s)
    (ground : ∀ τ ∈ D.names, τ.val ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    {k : Nat} (N : SetFormula (k + 1)) (params : Fin k → ZFSet.{u})
    (members : ∀ j, params j ∈ M.sets) (domain : M.DomainMeaning s D N params)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) : (Name.codedPower D W).val ∈ M.sets := by
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers hW carrier
  have bound : (Name.codedPower D W).val ⊆ B := by
    intro z hz
    obtain ⟨σ, p, rfl⟩ := Name.entries_cover (Name.codedPower D W) hz
    obtain ⟨_, hσ, _⟩ := (Name.entry_codedPower D W σ p).1 hz
    exact pairBound σ.val hσ (s.encode p) (s.encode_mem p)
  let formula := codedPowerEntryFormula N (fun j => j.succ.succ.succ) 0 1 2
  let context := extend W (extend (s.encode ⊤) params)
  have htop := M.transitive carrier (s.encode_mem ⊤)
  have correct : ∀ z ∈ M.sets, Realize M.sets formula (extend z context) ↔
      z ∈ (Name.codedPower D W).val := by
    intro z hz
    exact M.realize_codedPowerEntryFormula s D ground pairing N (fun j => j.succ.succ.succ)
      0 1 2 (extend z context) domain rfl htop hz
  have selected := M.separation_mem separation formula context
    (Fin.cases hW (Fin.cases htop members)) hB
  have eq : ZFSet.sep (fun z => Realize M.sets formula (extend z context)) B =
      (Name.codedPower D W).val := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hB hz)).1 rel
    · intro hz
      exact ⟨bound hz, (correct z (M.transitive hB (bound hz))).2 hz⟩
  exact eq ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricEnvelope_mem (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) : (Name.envelope τ.val).val ∈ M.sets := by
  rw [← Name.separationName_true _ τ.property]
  exact M.symmetricSeparationName_mem a s t b F K basis pairing unions powers separation collection
    carrier order group indices supports maps (.equal 0 0) Fin.elim0 τ

theorem symmetricCodedPower_mem [OrderTop P] (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (W : ZFSet.{u}) (hW : W ∈ M.sets) :
    (Name.codedPower (a.symmetricDomain s (M.nameDomain s) F) W).val ∈ M.sets := by
  apply M.codedPower_mem s (a.symmetricDomain s (M.nameDomain s) F) (fun _ h => h.1)
    pairing unions powers separation carrier (liftedHereditaryFormula 0 1 2 3 4)
    (symmetryParameters a s t b K) _ _ W hW
  · exact Fin.cases carrier (Fin.cases group (Fin.cases indices
      (Fin.cases supports (Fin.cases maps (fun i => Fin.elim0 i)))))
  · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
      carrier group indices supports maps 0 1 2 3 4 _ rfl rfl rfl rfl rfl

theorem symmetric_powerSet [OrderTop P] (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F))) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) powerSet Fin.elim0 := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  have closed : ∀ g τ, τ ∈ (M.nameDomain s).names → a.act s g τ ∈ (M.nameDomain s).names :=
    fun g τ hτ => M.act_mem s a t pairing unions powers separation collection carrier maps g τ hτ
  have moved : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names :=
    fun g _ hτ => a.symmetricDomain_translated s (M.nameDomain s) F closed g hτ
  have separated : ∀ {n} (φ : SetFormula (n + 1)) (env : Assignment D n) τ,
      τ ∈ D.names → Name.separationName D φ env τ ∈ D.names := by
    intro n φ env τ hτ
    exact ⟨M.symmetricSeparationName_mem a s t b F K basis pairing unions powers separation collection
      carrier order group indices supports maps φ env ⟨τ, hτ⟩,
      a.separationName_hs s D moved F φ env hτ.2 (fun i => (env i).property.2)⟩
  apply realize_powerSet_of_witnesses (D.values {p | H.mem p})
    (fun _ hx _ hz => D.values_transitive _ hx hz)
  intro x hx
  obtain ⟨τ, hτ, rfl⟩ := (Name.NameDomain.mem_values D _ x).1 hx
  have envelopeM := M.symmetricEnvelope_mem a s t b F K basis pairing unions powers separation collection
    carrier order group indices supports maps ⟨τ, hτ⟩
  obtain ⟨W, hW, subsets⟩ := M.power_witness powers envelopeM
  have bounded : ∀ σ ∈ D.names, σ.val ∈ W ↔ σ.val ⊆ (Name.envelope τ).val :=
    fun σ hσ => subsets σ.val hσ.1
  have powerM := M.symmetricCodedPower_mem a s t b F K basis pairing unions powers separation collection
    carrier group indices supports maps W hW
  have powerHS := a.codedPower_hs s (M.nameDomain s) F closed W (Name.envelope τ)
    (a.envelope_hs s F hτ.2) bounded
  refine ⟨Name.eval {p | H.mem p} (Name.codedPower D W),
    (Name.NameDomain.mem_values D _ _).2 ⟨Name.codedPower D W, ⟨powerM, powerHS⟩, rfl⟩, ?_⟩
  intro z hz
  exact Name.mem_eval_codedPower_iff D H generic separated ⟨τ, hτ⟩ W bounded z hz

end PartitionPilot.Forcing.TransitiveGround

end OAI
