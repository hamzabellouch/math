import OAI.SetTheory.PartitionPrinciple.Forcing.GroundSymmetricCollection
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundOrdinalOrderCodes

namespace OAI

section

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_relationImage (U : Set ZFSet.{u}) {n : Nat} (φ : SetFormula (n + 2))
    (params : Fin n → ZFSet.{u}) (A y : ZFSet.{u}) :
    Realize U (relationImageFormula φ) (extend y (extend A params)) ↔
      ∃ x ∈ U, x ∈ A ∧ Realize U φ (extend x (extend y params)) := by
  simp only [relationImageFormula, realize_ex, Realize, realize_binaryApplication]
  rfl

theorem replacement_of_collection_separation (U : Set ZFSet.{u})
    (collection : CollectionSchema U) (separation : SeparationSchema U) : ReplacementSchema U := by
  intro n φ params members A hA total
  have existsWitness : ∀ x ∈ U, x ∈ A → ∃ y ∈ U, Realize U φ (extend x (extend y params)) := by
    intro x hx xA
    obtain ⟨y, hy, rel, _⟩ := total x hx xA
    exact ⟨y, hy, rel⟩
  obtain ⟨B, hB, bounds⟩ := collection φ params members A hA existsWitness
  obtain ⟨C, hC, selected⟩ := separation (relationImageFormula φ) (extend A params) (Fin.cases hA members) B hB
  refine ⟨C, hC, ?_⟩
  intro y hy
  rw [selected y hy, realize_relationImage]
  constructor
  · exact And.right
  · intro image
    obtain ⟨x, hx, xA, rel⟩ := image
    obtain ⟨z, hz, zB, relz⟩ := bounds x hx xA
    obtain ⟨w, _, _, unique⟩ := total x hx xA
    have eq : y = z := (unique y hy rel).trans (unique z hz relz).symm
    exact ⟨eq.symm ▸ zB, x, hx, xA, rel⟩

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u
variable (M : TransitiveGround.{u}) {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G) (b : Presentation I)

theorem symmetric_replacement (F : NormalSubgroupFamily G) (K : I → Subgroup G)
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
    ReplacementSchema ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p}) :=
  replacement_of_collection_separation _
    (M.symmetric_collection a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic)
    (M.symmetric_separation a s t b F K basis pairing unions powers separation collection carrier order
      group indices supports maps H generic)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.SetFormula

def representedOrdinalRelationFormula : SetFormula 2 :=
  ex (reindex (extend 1 (extend 0 (extend 2 Fin.elim0))) ordinalImageWitnessFormula)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem realize_representedOrdinalRelationFormula {r N : ZFSet.{u}}
    (hr : r ∈ M.sets) (hN : N ∈ M.sets) :
    Realize M.sets representedOrdinalRelationFormula (extend r (extend N Fin.elim0)) ↔
      ∃ A ∈ M.sets, ordinalSetProperty A ∧
        ∃ f ∈ M.sets, InjectionCode A N f ∧ r = ordinalImageOrder A N f := by
  have swapped (A : ZFSet.{u}) :
      (fun i => extend A (extend r (extend N Fin.elim0))
        (extend (1 : Fin 3) (extend 0 (extend 2 Fin.elim0)) i)) =
      extend r (extend A (extend N Fin.elim0)) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => Fin.elim0 j))) i
  rw [representedOrdinalRelationFormula, realize_ex]
  constructor
  · rintro ⟨A, hA, rel⟩
    have witness := (realize_reindex M.sets _ ordinalImageWitnessFormula _).1 rel
    rw [swapped A] at witness
    exact ⟨A, hA, (M.realize_ordinalImageWitnessFormula hr hA hN).1 witness⟩
  · rintro ⟨A, hA, witness⟩
    have rel := (M.realize_ordinalImageWitnessFormula hr hA hN).2 witness
    rw [← swapped A] at rel
    exact ⟨A, hA, (realize_reindex M.sets _ ordinalImageWitnessFormula _).2 rel⟩

theorem exists_groundHartogs
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    {N : ZFSet.{u}} (hN : N ∈ M.sets) :
    ∃ C ∈ M.sets, ordinalSetProperty C ∧
      (∀ A : ZFSet.{u}, A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧ M.groundEmbeddable A N) ∧
      ¬ M.groundEmbeddable C N := by
  let params := extend N Fin.elim0
  let D := ZFSet.sep (fun r => Realize M.sets representedOrdinalRelationFormula
    (extend r params)) (M.groundRelations N N)
  have hD : D ∈ M.sets := M.separation_mem separation representedOrdinalRelationFormula params
    (Fin.cases hN (fun i => Fin.elim0 i))
    (M.groundRelations_mem pairing unions powers separation hN hN)
  have total : ∀ r ∈ M.sets, r ∈ D → ∃ A ∈ M.sets,
      Realize M.sets ordinalImageWitnessFormula (extend r (extend A params)) ∧
      ∀ B ∈ M.sets, Realize M.sets ordinalImageWitnessFormula (extend r (extend B params)) → B = A := by
    intro r hr rD
    obtain ⟨A, hA, ordA, f, hf, injF, eqF⟩ :=
      (M.realize_representedOrdinalRelationFormula hr hN).1 (ZFSet.mem_sep.1 rD).2
    refine ⟨A, hA, (M.realize_ordinalImageWitnessFormula hr hA hN).2 ⟨ordA, f, hf, injF, eqF⟩, ?_⟩
    intro B hB relB
    obtain ⟨ordB, g, _, injG, eqG⟩ := (M.realize_ordinalImageWitnessFormula hr hB hN).1 relB
    exact ordinalImageOrder_domain_unique ordB ordA injG injF (eqG.symm.trans eqF)
  obtain ⟨C, hC, represented⟩ := replacement_of_collection_separation M.sets collection separation
    ordinalImageWitnessFormula params (Fin.cases hN (fun i => Fin.elim0 i)) D hD total
  have exactMembers (A : ZFSet.{u}) :
      A ∈ C ↔ A ∈ M.sets ∧ ordinalSetProperty A ∧ M.groundEmbeddable A N := by
    constructor
    · intro hAC
      have hA := M.transitive hC hAC
      obtain ⟨r, hr, _, rel⟩ := (represented A hA).1 hAC
      obtain ⟨ordA, f, hf, inj, _⟩ := (M.realize_ordinalImageWitnessFormula hr hA hN).1 rel
      exact ⟨hA, ordA, f, hf, inj⟩
    · rintro ⟨hA, ordA, f, hf, inj⟩
      let r := ordinalImageOrder A N f
      have hr : r ∈ M.sets := M.ordinalImageOrder_mem pairing unions powers separation hA hN hf
      have witness := (M.realize_ordinalImageWitnessFormula hr hA hN).2 ⟨ordA, f, hf, inj, rfl⟩
      have rD : r ∈ D := ZFSet.mem_sep.2
        ⟨(M.mem_groundRelations N N r).2 ⟨hr, ordinalImageOrder_subset A N f⟩,
          (M.realize_representedOrdinalRelationFormula hr hN).2 ⟨A, hA, ordA, f, hf, inj, rfl⟩⟩
      exact (represented A hA).2 ⟨r, hr, rD, witness⟩
  have ordinal : ordinalSetProperty C := by
    refine ⟨?_, fun A hA => ((exactMembers A).1 hA).2.1.1⟩
    intro A hAC B hBA
    obtain ⟨hA, ordA, smallA⟩ := (exactMembers A).1 hAC
    have hB := M.transitive hA hBA
    exact (exactMembers B).2 ⟨hB, ordinalSetProperty_member ordA hBA,
      M.groundEmbeddable_restrict separation hB hN (fun z hz => ordA.1 B hBA z hz) smallA⟩
  exact ⟨C, hC, ordinal, exactMembers,
    fun small => ZFSet.mem_irrefl C ((exactMembers C).2 ⟨hC, ordinal, small⟩)⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
