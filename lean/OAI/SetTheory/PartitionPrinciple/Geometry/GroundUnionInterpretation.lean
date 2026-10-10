import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCompleteProjectionGenericity

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] (s : Presentation P)
variable {G : Type v} [Group G] (a : PosetAction G P) (F : NormalSubgroupFamily G)

def basicFragment : SetFormula 0 :=
  .conj extensionality (.conj foundation (.conj emptySet pairing))

theorem symmetric_values_countable (small : M.sets.Countable) (H : Set P) :
    ((a.symmetricDomain s (M.nameDomain s) F).values H).Countable := by
  let : Countable (a.symmetricDomain s (M.nameDomain s) F).names :=
    M.symmetric_names_countable s a F small
  exact Set.countable_range (fun τ : (a.symmetricDomain s (M.nameDomain s) F).names =>
    Name.eval H τ.val)

theorem exists_basic_interpretation [OrderTop P]
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      Realize ((a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q})
        basicFragment Fin.elim0 := by
  obtain ⟨H, hp, ground, ordinary, symmetric⟩ := M.exists_joint_generic s a F small carrier p
  refine ⟨H, hp, ground, ordinary, symmetric, ?_⟩
  have nonempty := a.symmetricDomain_nonempty s (M.nameDomain s) F
    (M.nameDomain_nonempty s ⟨s.carrier, carrier⟩)
  exact ⟨realize_extensionality _ _, realize_foundation _ _,
    realize_emptySet _ nonempty _, M.symmetric_pairing s a F pairing carrier H⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u}) {P : Type u} [PartialOrder P] [OrderTop P]
variable (s : Presentation P) {G : Type v} [Group G]
variable (a : PosetAction G P) (F : NormalSubgroupFamily G)

theorem exists_union_interpretation
    (small : M.sets.Countable) (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (M.codedFamily s) ∧
      H.GenericFor (formulaFamily (M.nameDomain s)) ∧
      H.GenericFor (formulaFamily (a.symmetricDomain s (M.nameDomain s) F)) ∧
      Realize ((a.symmetricDomain s (M.nameDomain s) F).values {q | H.mem q})
        (.conj basicFragment SetFormula.union) Fin.elim0 := by
  obtain ⟨H, hp, ground, ordinary, symmetric, basic⟩ :=
    M.exists_basic_interpretation s a F small carrier pairing p
  exact ⟨H, hp, ground, ordinary, symmetric, basic,
    M.symmetric_union s a F pairing unions powers separation carrier order H⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
