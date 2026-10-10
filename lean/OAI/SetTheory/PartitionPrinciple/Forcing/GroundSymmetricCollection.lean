import OAI.SetTheory.PartitionPrinciple.Definability.ForcingWitnessFormulas
import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMixtureTermBounds

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetricForcingWitnessBound (F : NormalSubgroupFamily G) (K : I → Subgroup G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {n : Nat} (φ : SetFormula (n + 2))
    (nameEnv : Assignment (a.symmetricDomain s (M.nameDomain s) F) n)
    (τ : (a.symmetricDomain s (M.nameDomain s) F).names) :
    ∃ W ∈ M.sets, ∀ σ : (a.symmetricDomain s (M.nameDomain s) F).names, ∀ p,
      (∃ r, Name.Entry σ.val τ.val r) →
      (∃ ρ : (a.symmetricDomain s (M.nameDomain s) F).names,
        Forces (a.symmetricDomain s (M.nameDomain s) F) φ (extend σ (extend ρ nameEnv)) p) →
      ∃ ρ : (a.symmetricDomain s (M.nameDomain s) F).names, ρ.val.val ∈ W ∧
        Forces (a.symmetricDomain s (M.nameDomain s) F) φ (extend σ (extend ρ nameEnv)) p := by
  let D := a.symmetricDomain s (M.nameDomain s) F
  let context := extend s.carrier (extend s.conditionOrder (extend t.carrier (extend b.carrier
    (extend (supportBasisCode b t K) (extend (a.conditionMapFamily s t) (fun i => (nameEnv i).val.val))))))
  let params : Fin 6 → Fin (n + 6) := extend 0 (extend 1 (extend 2 (extend 3 (extend 4 (extend 5 Fin.elim0)))))
  have members : ∀ i, context i ∈ M.sets :=
    Fin.cases carrier (Fin.cases order (Fin.cases group (Fin.cases indices (Fin.cases supports
      (Fin.cases maps (fun i => (nameEnv i).property.1))))))
  let selected := forcingWitnessFormula symmetricGroundPrimitives φ (fun j => (params j).succ.succ)
    (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ) 0 1
  have correct : ∀ z ∈ M.sets, ∀ y ∈ M.sets,
      Realize M.sets selected (extend z (extend y context)) ↔
        ∃ σ : D.names, ∃ p, z = ZFSet.pair σ.val.val (s.encode p) ∧
          ∃ ρ : D.names, ρ.val.val = y ∧ Forces D φ (extend σ (extend ρ nameEnv)) p := by
    intro z hz y hy
    apply M.realize_forcingWitnessFormula s D (fun _ h => h.1) pairing carrier order symmetricGroundPrimitives φ
      (fun j => (params j).succ.succ) (fun i => i.succ.succ.succ.succ.succ.succ.succ.succ)
      0 1 (extend z (extend y context)) rfl rfl _ _ nameEnv (fun _ => rfl) hz hy
    · exact M.equalityMeaning_lifted s D (fun _ h => h.1) pairing unions powers separation collection
        carrier order 0 1 _ rfl rfl
    · exact M.domainMeaning_liftedHereditary a s t b F K basis pairing unions powers separation collection
        carrier group indices supports maps 0 2 3 4 5 _ rfl rfl rfl rfl rfl
  obtain ⟨B, hB, pairBound⟩ := M.exists_pair_bound pairing unions powers
    (M.union_mem unions (M.union_mem unions τ.property.1)) carrier
  obtain ⟨W, hW, witnesses⟩ := M.partialCollection_witness collection selected context members hB
  refine ⟨W, hW, ?_⟩
  intro σ p entry possible
  obtain ⟨r, entry⟩ := entry
  have hb := pairBound σ.val.val (Name.child_mem_doubleUnion entry) (s.encode p) (s.encode_mem p)
  have hz := M.transitive hB hb
  have existsRaw : ∃ y ∈ M.sets, Realize M.sets selected
      (extend (ZFSet.pair σ.val.val (s.encode p)) (extend y context)) := by
    obtain ⟨ρ, forced⟩ := possible
    exact ⟨ρ.val.val, ρ.property.1, (correct _ hz _ ρ.property.1).2 ⟨σ, p, rfl, ρ, rfl, forced⟩⟩
  obtain ⟨y, hy, rel⟩ := witnesses _ hb existsRaw
  obtain ⟨ν, q, shape, ρ, eqρ, forced⟩ := (correct _ hz y (M.transitive hW hy)).1 rel
  have parts := ZFSet.pair_inj.1 shape
  have names : σ = ν := Subtype.ext (Subtype.ext parts.1)
  have conditions : p = q := s.injective parts.2
  refine ⟨ρ, eqρ.symm ▸ hy, ?_⟩
  rwa [← names, ← conditions] at forced

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_collection (F : NormalSubgroupFamily G) (K : I → Subgroup G)
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
    CollectionSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) := by
  classical
  let D := a.symmetricDomain s (M.nameDomain s) F
  intro n φ params members X hX total
  have reps := fun i => (D.mem_values _ (params i)).1 (members i)
  choose names inDomain values using reps
  let env : Assignment D n := fun i => ⟨names i, inDomain i⟩
  have evals : evalAssignment {p | H.mem p} env = params := funext values
  obtain ⟨τ, hτ, rfl⟩ := (D.mem_values _ X).1 hX
  obtain ⟨W, hW, bounds⟩ := M.symmetricForcingWitnessBound a s t b F K basis
    pairing unions powers separation collection carrier order group indices supports maps φ env ⟨τ, hτ⟩
  have orbitM := M.orbitCodes_mem a s t pairing unions powers separation collection carrier group maps W hW
  let C := Name.codedPower D (a.orbitCodes s (M.nameDomain s) W)
  have groundC := M.symmetricCodedPower_mem a s t b F K basis pairing unions powers separation collection
    carrier group indices supports maps _ orbitM
  have symC := a.orbitCodedPower_hs s (M.nameDomain s) F
    (fun g σ hσ => M.act_mem s a t pairing unions powers separation collection carrier maps g σ hσ) W
  have hC : C ∈ D.names := ⟨groundC, symC⟩
  refine ⟨Name.eval {p | H.mem p} C, (D.mem_values _ _).2 ⟨C, hC, rfl⟩, ?_⟩
  intro x hx member
  obtain ⟨σ, r, entry, _, value⟩ := (Name.mem_eval _ τ x).1 member
  have hσ := D.children hτ entry
  obtain ⟨y, hy, rel⟩ := total x hx member
  obtain ⟨ρ, hρ, valueρ⟩ := (D.mem_values _ y).1 hy
  have truth : Realize (D.values {p | H.mem p}) φ
      (evalAssignment {p | H.mem p} (extend ⟨σ, hσ⟩ (extend ⟨ρ, hρ⟩ env))) := by
    rw [evalAssignment_extend, evalAssignment_extend, value, valueρ, evals]
    exact rel
  obtain ⟨p, hp, forced⟩ := (forcing_truth D H generic φ (extend ⟨σ, hσ⟩ (extend ⟨ρ, hρ⟩ env))).1 truth
  obtain ⟨ν, νW, forcedν⟩ := bounds ⟨σ, hσ⟩ p ⟨r, entry⟩ ⟨⟨ρ, hρ⟩, forced⟩
  have orbitν := a.mem_orbitCodes_of_mem s (M.nameDomain s) ν.property.1 νW
  have νC : Name.eval {p | H.mem p} ν.val ∈ Name.eval {p | H.mem p} C :=
    (Name.mem_eval_codedPower D _ H _).2 ⟨ν.val, ν.property, orbitν, rfl⟩
  have truthν := forces_sound D H generic φ (extend ⟨σ, hσ⟩ (extend ν env)) hp forcedν
  rw [evalAssignment_extend, evalAssignment_extend, value, evals] at truthν
  exact ⟨Name.eval {p | H.mem p} ν.val, (D.mem_values _ _).2 ⟨ν.val, ν.property, rfl⟩, νC, truthν⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
