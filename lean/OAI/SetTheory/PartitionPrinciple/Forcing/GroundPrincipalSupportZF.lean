import OAI.SetTheory.PartitionPrinciple.Definability.PrincipalSupportFormulas
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundFlatSuccessorFullActionGraph
import OAI.SetTheory.PartitionPrinciple.Geometry.RowAtomicDescent

namespace OAI

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G : Type u} [Group G]
variable (t : Presentation G) (b : Presentation I) (K : I → Subgroup G)

theorem supportBasis_fiber_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (separation : SeparationSchema M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (i : I) :
    t.subset (fun g => g ∈ K i) ∈ M.sets := by
  have hi := M.transitive indices (b.encode_mem i)
  let params := extend (b.encode i) (extend (supportBasisCode b t K) Fin.elim0)
  have selected := M.separation_mem separation (pairMembershipFormula 1 0 2) params
    (Fin.cases hi (Fin.cases supports (fun j => Fin.elim0 j))) group
  have eq : ZFSet.sep (fun y => Realize M.sets (pairMembershipFormula 1 0 2) (extend y params)) t.carrier =
      t.subset (fun g => g ∈ K i) := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hy, rel⟩
      obtain ⟨g, rfl⟩ := (t.mem_carrier y).1 hy
      apply (t.encode_mem_subset (fun g => g ∈ K i) g).2
      exact (pair_mem_supportBasisCode b t K i g).1
        ((M.realize_pairMembershipFormula pairing 1 0 2 (extend (t.encode g) params)
          hi (M.transitive group hy) supports).1 rel)
    · intro hy
      obtain ⟨g, hg, rfl⟩ := (t.mem_subset (fun g => g ∈ K i) y).1 hy
      exact ⟨t.encode_mem g, (M.realize_pairMembershipFormula pairing 1 0 2
        (extend (t.encode g) params) hi (M.transitive group (t.encode_mem g)) supports).2
        ((pair_mem_supportBasisCode b t K i g).2 hg)⟩
  exact eq ▸ selected

variable {P : Type u} [PartialOrder P] (a : PosetAction G P) (s : Presentation P)

theorem basis_mix_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (p : P) (τ : Name s) (hτ : τ.val ∈ M.sets) : (a.mix s (K i) p τ).val ∈ M.sets :=
  M.mix_mem a s t pairing unions powers separation collection carrier order group maps (K i)
    (M.supportBasis_fiber_mem t b K pairing separation group indices supports i) p τ hτ

theorem basis_symmetric_mix (F : NormalSubgroupFamily G)
    (basis : ∀ H, F.mem H ↔ ∃ i, K i ≤ H)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t K ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    (i : I) (p : P) (τ : Name s) (hτ : τ ∈ (a.symmetricDomain s (M.nameDomain s) F).names) :
    a.mix s (K i) p τ ∈ (a.symmetricDomain s (M.nameDomain s) F).names :=
  ⟨M.basis_mix_mem t b K a s pairing unions powers separation collection carrier order group indices supports maps i p τ hτ.1,
    a.mix_hs s F (K i) ((basis (K i)).2 ⟨i, le_rfl⟩) p hτ.2⟩

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {G I : Type u} [Group G] [PartialOrder I]
variable (d : PosetAction G I) (b : Presentation I) (t : Presentation G)

theorem realize_principalSupportEntry (z : ZFSet.{u}) (hz : z ∈ M.sets)
    (nodes : b.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (order : b.conditionOrder ∈ M.sets) (graph : d.actionGraph b t ∈ M.sets) :
    Realize M.sets (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula
      (extend z (extend b.carrier (extend t.carrier
        (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0))))) ↔
      z ∈ supportBasisCode b t d.principalFix :=
  (BoundedFormula.realize_toFormula M _ _ (Fin.cases hz (Fin.cases nodes (Fin.cases group
    (Fin.cases order (Fin.cases graph (fun j => Fin.elim0 j))))))).trans
      (BoundedFormula.principalSupportEntry_correct d b t z)

theorem principalSupportBasis_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (order : b.conditionOrder ∈ M.sets) (graph : d.actionGraph b t ∈ M.sets) :
    supportBasisCode b t d.principalFix ∈ M.sets := by
  obtain ⟨B, hB, bounds⟩ := M.exists_pair_bound pairing unions powers nodes group
  let params := extend b.carrier (extend t.carrier
    (extend b.conditionOrder (extend (d.actionGraph b t) Fin.elim0)))
  have selected := M.separation_mem separation (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula
    params (Fin.cases nodes (Fin.cases group (Fin.cases order (Fin.cases graph (fun j => Fin.elim0 j))))) hB
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.principalSupportEntryFormula 0 1 2 3 4).toFormula (extend z params)) B =
        supportBasisCode b t d.principalFix := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (M.realize_principalSupportEntry d b t z (M.transitive hB hz) nodes group order graph).1 rel
    · intro hz
      have hzB : z ∈ B := by
        obtain ⟨⟨C, g⟩, _, eq⟩ := ((b.product t).mem_subset (fun z => z.2 ∈ d.principalFix z.1) z).1 hz
        exact eq ▸ bounds _ (b.encode_mem C) _ (t.encode_mem g)
      exact ⟨hzB, (M.realize_principalSupportEntry d b t z (M.transitive hB hzB) nodes group order graph).2 hz⟩
  exact eq ▸ selected

theorem principalFix_code_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) (group : t.carrier ∈ M.sets)
    (order : b.conditionOrder ∈ M.sets) (graph : d.actionGraph b t ∈ M.sets) (C : I) :
    t.subset (fun g => g ∈ d.principalFix C) ∈ M.sets :=
  M.supportBasis_fiber_mem t b d.principalFix pairing separation group nodes
    (M.principalSupportBasis_mem d b t pairing unions powers separation nodes group order graph) C

end PartitionPilot.Forcing.TransitiveGround

namespace PartitionPilot.Forcing.Rows

open SetRealization SetFormula Compression.RecursiveMaps
open Compression.RecursiveMaps.CountableColumns Compression.RecursiveMaps.MainStage.OrdinalRun

theorem ground_row_common_support (M : TransitiveGround.{1})
    (t : Presentation (FinalActor Column)) (b : Presentation (FinalPoint Column))
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (carrier : namePresentation.carrier ∈ M.sets) (order : namePresentation.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (indices : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t (fun W => (finalAction Column).fixSubgroup W) ∈ M.sets)
    (maps : posetAction.conditionMapFamily namePresentation t ∈ M.sets)
    (H : ConditionFilter RowForcing) (generic : H.GenericFor (rowAtomicFamily (M.nameDomain namePresentation)))
    (C B : FinalPoint Column) (x y : Name namePresentation)
    (hx : x.val ∈ M.sets) (hy : y.val ∈ M.sets)
    (sx : (finalAction Column).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (finalAction Column).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (hs : HereditarilySymmetric posetAction namePresentation (supportFamily Column) x)
    (values : Name.eval {q | H.mem q} x = Name.eval {q | H.mem q} y) :
    ∃ z : Name namePresentation, z.val ∈ M.sets ∧
      HereditarilySymmetric posetAction namePresentation (supportFamily Column) z ∧
      (finalAction Column).fixSubgroup ((finalOrder Column).meet C B) ≤ posetAction.stabilizer namePresentation z ∧
      Name.nameRank z ≤ Name.nameRank x ∧ Name.eval {q | H.mem q} z = Name.eval {q | H.mem q} x := by
  exact row_common_support_of_eval_eq (M.nameDomain namePresentation)
    (fun g τ hτ => M.act_mem namePresentation posetAction t pairing unions powers separation collection carrier maps g τ hτ)
    (fun W p τ hτ => M.basis_mix_mem t b (fun W => (finalAction Column).fixSubgroup W)
      posetAction namePresentation pairing unions powers separation collection carrier order group indices supports maps W p τ hτ)
    H generic C B x y hx hy sx sy hs values

end PartitionPilot.Forcing.Rows

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u}
variable [Group G] [PartialOrder I] [PartialOrder P] [OrderTop P]
variable (d : PosetAction G I) (a : PosetAction G P)
variable (b : Presentation I) (s : Presentation P) (t : Presentation G)

theorem exists_ZF_from_principalSupports (C : I)
    (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (support_order : b.conditionOrder ∈ M.sets) (support_action : d.actionGraph b t ∈ M.sets)
    (forcing_action : a.actionGraph s t ∈ M.sets) (p : P) :
    let F := d.principalSupportFamily C directed
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      M.sets ⊆ (a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q} ∧
      ZFRealization ((a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q}) :=
  M.exists_ZF_interpretation_from_actionGraph a s t b (d.principalSupportFamily C directed) d.principalFix
    (d.principalSupportFamily_basis C directed) small pairing unions powers separation collection infinite
    carrier order group nodes
    (M.principalSupportBasis_mem d b t pairing unions powers separation nodes group support_order support_action)
    forcing_action p

end PartitionPilot.Forcing.TransitiveGround

end OAI
