import OAI.SetTheory.PartitionPrinciple.Definability.CountableSetFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.Name

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem atomicFamily_countable (D : NameDomain s) (small : D.names.Countable) :
    (atomicFamily D).Countable := by
  let : Countable D.names := small
  let memSet (z : P × D.names × D.names) := Localized z.1 (MemWitness z.2.1.val z.2.2.val)
  let eqSet (z : D.names × D.names) := EqDecisionWitness z.1.val z.2.val
  apply ((Set.countable_range memSet).union (Set.countable_range eqSet)).mono
  intro E hE
  rcases hE with ⟨p, σ, τ, hσ, hτ, rfl⟩ | ⟨σ, τ, hσ, hτ, rfl⟩
  · exact Or.inl ⟨(p, ⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩
  · exact Or.inr ⟨(⟨σ, hσ⟩, ⟨τ, hτ⟩), rfl⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

open SetRealization
universe u
variable {P : Type u} [Preorder P] [Countable P] {s : Presentation P}

theorem formulaFamily_countable (D : Name.NameDomain s) (small : D.names.Countable) :
    (formulaFamily D).Countable := by
  let : Countable D.names := small
  let decisions (z : Σ n, SetFormula n × Assignment D n) := DecisionWitness D z.2.1 z.2.2
  let universals (z : Σ n, SetFormula (n + 1) × Assignment D n) := AllDecisionWitness D z.2.1 z.2.2
  apply ((Name.atomicFamily_countable D small).union
    ((Set.countable_range decisions).union (Set.countable_range universals))).mono
  intro E hE
  rcases hE with atomic | (⟨n, φ, env, rfl⟩ | ⟨n, φ, env, rfl⟩)
  · exact Or.inl atomic
  · exact Or.inr (Or.inl ⟨⟨n, φ, env⟩, rfl⟩)
  · exact Or.inr (Or.inr ⟨⟨n, φ, env⟩, rfl⟩)

theorem exists_generic_formulaFamily (D : Name.NameDomain s) (small : D.names.Countable) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧ H.GenericFor (formulaFamily D) :=
  exists_generic_for_countable_family p _ (formulaFamily_countable D small)

theorem exists_interpretation_truth (D : Name.NameDomain s) (small : D.names.Countable) (p : P) :
    ∃ H : ConditionFilter P, H.mem p ∧
      ∀ {n} (φ : SetFormula n) (env : Assignment D n),
        Realize (D.values {q | H.mem q}) φ (evalAssignment {q | H.mem q} env) ↔
          ∃ q, H.mem q ∧ Forces D φ env q := by
  obtain ⟨H, hp, generic⟩ := exists_generic_formulaFamily D small p
  exact ⟨H, hp, fun φ env => forcing_truth D H generic φ env⟩

end PartitionPilot.Forcing.SetFormula

end

end OAI
