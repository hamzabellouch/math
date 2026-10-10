import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs
import OAI.SetTheory.PartitionConsistency.Logic.SetLanguage
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingQuotient
import OAI.SetTheory.PartitionConsistency.Logic.CountableModels
import OAI.SetTheory.PartitionConsistency.Logic.Completeness
import OAI.SetTheory.PartitionConsistency.Algebra.DiagramOrder
import OAI.SetTheory.PartitionConsistency.Algebra.Placements
import OAI.SetTheory.PartitionConsistency.Forcing.Diagrams
import OAI.SetTheory.PartitionConsistency.Forcing.CohenForcing
import OAI.SetTheory.PartitionConsistency.Forcing.SupportFilter
import OAI.SetTheory.PartitionConsistency.Forcing.ProductForcing
import OAI.SetTheory.PartitionConsistency.Algebra.PlacementExtensions
import OAI.SetTheory.PartitionConsistency.Algebra.MergerWords
import OAI.SetTheory.PartitionConsistency.Algebra.MergerCones
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeWords
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeGates
import OAI.SetTheory.PartitionConsistency.Algebra.ProbeMargins
import OAI.SetTheory.PartitionConsistency.Algebra.ConservativeExtensions
import OAI.SetTheory.PartitionConsistency.Algebra.ProbePresentations
import OAI.SetTheory.PartitionConsistency.Algebra.PersistentProfiles
import OAI.SetTheory.PartitionConsistency.Algebra.DirectLimits
import OAI.SetTheory.PartitionConsistency.Algebra.GateTowers
import OAI.SetTheory.PartitionConsistency.Logic.GroundModels
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingNames
import OAI.SetTheory.PartitionConsistency.Forcing.NameActions
import OAI.SetTheory.PartitionConsistency.Forcing.AtomicForcing
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingTruth
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricNames
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricSets
import OAI.SetTheory.PartitionConsistency.Forcing.SymmetricChoice
import OAI.SetTheory.PartitionConsistency.Forcing.EquivariantMixing
import OAI.SetTheory.PartitionConsistency.Forcing.ProductNames
import OAI.SetTheory.PartitionConsistency.Forcing.ChoiceFailure
import OAI.SetTheory.PartitionConsistency.Construction.MonoidBase
import OAI.SetTheory.PartitionConsistency.Construction.MonoidTowers
import OAI.SetTheory.PartitionConsistency.Construction.MonoidRounds
import OAI.SetTheory.PartitionConsistency.Construction.CompleteRounds
import OAI.SetTheory.PartitionConsistency.Construction.SaturatedMonoids
import OAI.SetTheory.PartitionConsistency.Construction.DiagramPlacements
import OAI.SetTheory.PartitionConsistency.Models.OrbitNames
import OAI.SetTheory.PartitionConsistency.Models.LocalQuotients
import OAI.SetTheory.PartitionConsistency.Models.LocalRecords
import OAI.SetTheory.PartitionConsistency.Models.AvailableRecords
import OAI.SetTheory.PartitionConsistency.Models.ComponentGluing
import OAI.SetTheory.PartitionConsistency.Models.ConcreteSystem
import OAI.SetTheory.PartitionConsistency.Models.QuotientTransport
import OAI.SetTheory.PartitionConsistency.Models.TailGraphs
import OAI.SetTheory.PartitionConsistency.Models.GraphFusion
import OAI.SetTheory.PartitionConsistency.Models.PersistentCodes
import OAI.SetTheory.PartitionConsistency.Models.OrdinalCodes
import OAI.SetTheory.PartitionConsistency.Models.CodeLinks
import OAI.SetTheory.PartitionConsistency.Models.UniformNames
import OAI.SetTheory.PartitionConsistency.Models.OrdinalPresentation
import OAI.SetTheory.PartitionConsistency.Models.ClassFibers
import OAI.SetTheory.PartitionConsistency.Models.OrdinalChoice
import OAI.SetTheory.PartitionConsistency.Models.QuotientActions
import OAI.SetTheory.PartitionConsistency.Models.GermSelectors
import OAI.SetTheory.PartitionConsistency.Models.StableSelectors
import OAI.SetTheory.PartitionConsistency.Models.OrbitAssignments
import OAI.SetTheory.PartitionConsistency.Models.AssignedGraphs
import OAI.SetTheory.PartitionConsistency.Models.CodeCardinals
import OAI.SetTheory.PartitionConsistency.Construction.MergerPushouts
import OAI.SetTheory.PartitionConsistency.Construction.ConservativeHulls
import OAI.SetTheory.PartitionConsistency.Construction.ConservativeCells
import OAI.SetTheory.PartitionConsistency.Construction.CellTowers
import OAI.SetTheory.PartitionConsistency.Construction.CellCuts
import OAI.SetTheory.PartitionConsistency.Construction.CellReorder
import OAI.SetTheory.PartitionConsistency.Construction.BlockTowers
import OAI.SetTheory.PartitionConsistency.Models.ConcreteQuotients
import OAI.SetTheory.PartitionConsistency.Forcing.RelationCalculus
import OAI.SetTheory.PartitionConsistency.Models.UniformImages
import OAI.SetTheory.PartitionConsistency.Models.OrderedSections
import OAI.SetTheory.PartitionConsistency.Models.SliceGeometry
import OAI.SetTheory.PartitionConsistency.Models.SliceAssembly

namespace OAI

/-! ## PartitionPrinciple -/

namespace PartitionConsistency.SetForcingNames.SymmetricSystem
universe u v w
noncomputable section
variable {P : Type w} [PartialOrder P] [OrderTop P] {Γ : Type v} [Group Γ]
variable (S : SymmetricSystem.{u} P Γ)

omit [OrderTop P] in
/-- Purely logical conversion of reverse-injection witnesses to the full
Partition Principle sentence. Its quantifiers range over all HS names. -/
theorem forces_PP_of_dense
    (h : ∀ (p : P) (f X Y : S.Name),
      S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2) →
      ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,Y,X] q (SetLanguage.injection 0 1 2))
    (p : P) : S.Forces Fin.elim0 p SetLanguage.PP := by
  change S.atomic.ForceFormula Fin.elim0 p SetLanguage.PP
  rw [SetLanguage.PP,S.atomic.forceFormula_all S.atomic_regular]
  intro X
  have hX : Fin.snoc (Fin.elim0 : Fin 0 → S.Name) X = ![X] := by
    ext k
    fin_cases k; rfl
  rw [hX,S.atomic.forceFormula_all S.atomic_regular]
  intro Y
  have hY : Fin.snoc ![X] Y = ![X,Y] := by
    ext k
    fin_cases k <;> rfl
  rw [hY,S.atomic.forceFormula_imp S.atomic_regular]
  intro q hqp hf r hrq
  obtain ⟨s,hsr,f,hf⟩ := hf r hrq
  have hv : Fin.snoc ![X,Y] f = ![X,Y,f] := by
    ext k
    fin_cases k <;> rfl
  rw [hv] at hf
  have hf' : S.Forces ![f,X,Y] s (SetLanguage.surjection 0 1 2) :=
    (S.forces_surjection _ s 0 1 2).mpr ((S.forces_surjection _ s 2 0 1).mp hf)
  obtain ⟨t,hts,j,hj⟩ := h s f X Y hf'
  refine ⟨t,hts.trans hsr,j,?_⟩
  have hvj : Fin.snoc ![X,Y] j = ![X,Y,j] := by
    ext k
    fin_cases k <;> rfl
  rw [hvj]
  exact (S.forces_injection _ t 2 1 0).mpr ((S.forces_injection _ t 0 1 2).mp hj)

end
end PartitionConsistency.SetForcingNames.SymmetricSystem

namespace PartitionConsistency.ConcreteSystem
open MonoidConstruction CardinalParameters DiagramForcing SetForcingNames
open ProductForcing SetForcingNames.SymmetricSystem
noncomputable section

/-- All-set reduction for the constructed system, including the empty-set
case. The presentation and subsequent choices are made at arbitrary ranks. -/
theorem reverse_injection_dense (f X Y : S.Name) (p : P)
    (hf : S.Forces ![f,X,Y] p (SetLanguage.surjection 0 1 2)) :
    ∃ q, q ≤ p ∧ ∃ j : S.Name, S.Forces ![j,Y,X] q (SetLanguage.injection 0 1 2) := by
  by_cases hne : ∃ q, q ≤ p ∧ ∃ x : S.Name, S.atomic.MemF q x X
  · obtain ⟨q,hqp,x,hx⟩ := hne
    obtain ⟨η,s,hs⟩ := ordinal_presentation aleph0_le_μ cardinal_T size_lt T.e complement_cardinal
      (posetCode κ) (posetCode_injective κ) X x q hx
    let D : SliceData S := ⟨s,f,A,X,Y,η.toZFSet⟩
    obtain ⟨r,hrq,j,hj⟩ := presentation_reverse_injection D rfl q hs (S.atomic.forceFormula_mono hqp hf)
    exact ⟨r,hrq.trans hqp,j,hj⟩
  · have he : ∀ y q, q ≤ p → ¬ S.atomic.MemF q y Y := by
      intro y q hqp hy
      obtain ⟨r,hrq,x,hx,_⟩ := S.surjection_onto hf hqp hy q le_rfl
      exact hne ⟨r,hrq.trans hqp,x,hx⟩
    obtain ⟨j,hj⟩ := S.empty_domain_injection Y X p he
    exact ⟨p,le_rfl,j,hj⟩

/-- The Partition Principle for arbitrary internal sets and surjections. -/
theorem forces_PP (p : P) : S.Forces Fin.elim0 p SetLanguage.PP :=
  S.forces_PP_of_dense (fun p f X Y => reverse_injection_dense f X Y p) p

/-- The actual symmetric forcing interpretation supplies every axiom of the
full target theory, with no inaccessible-cardinal or model-existence premise. -/
theorem forces_target (p : P) : ∀ φ ∈ SetLanguage.targetTheory, S.Forces Fin.elim0 p φ := by
  intro φ hφ
  rcases hφ with hφ | hφ
  · exact forces_ZF p φ hφ
  · rcases hφ with rfl | rfl | rfl | hfalse
    · exact forces_PP p
    · exact forces_ACwo p
    · exact forces_not_AC p

/-- Soundness of the nontrivial regular forcing interpretation rules out an
ordinary finite first-order proof of contradiction from the target theory. -/
theorem consistent_target : Consistent SetLanguage.targetTheory :=
  S.consistent_of_forces (⊤ : P) (forces_target ⊤)

end
end PartitionConsistency.ConcreteSystem

namespace PartitionConsistency
/-- Relative consistency for pure first-order set theories, with syntactic
consistency and no transitive-ground or inaccessible-cardinal hypothesis. -/





theorem main_consistency :
    Consistent SetLanguage.ZF → Consistent SetLanguage.targetTheory := by
  intro _
  exact ConcreteSystem.consistent_target
end PartitionConsistency

end OAI
