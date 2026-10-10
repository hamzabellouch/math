import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowGenerics

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

theorem mem_two_iff (x : ZFSet.{u}) :
    x ∈ natSetCode 2 ↔ x = natSetCode 0 ∨ x = natSetCode 1 := by
  rw [mem_natSetCode]
  constructor
  · rintro ⟨n, hn, rfl⟩
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨0, by omega, rfl⟩
    · exact ⟨1, by omega, rfl⟩

theorem two_distinct_values :
    ∃ a ∈ natSetCode 2, ∃ b ∈ natSetCode 2, a ≠ (b : ZFSet.{u}) := by
  refine ⟨natSetCode 0, (mem_two_iff _).2 (Or.inl rfl),
    natSetCode 1, (mem_two_iff _).2 (Or.inr rfl), ?_⟩
  intro eq
  have impossible := natSetCode_injective eq
  omega

namespace TransitiveGround

open SetRealization SetFormula
variable (M : TransitiveGround.{u})

noncomputable def binaryGenericRow (I C : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ConditionFilter (SetMembers (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)) →
      ZFSet.{u} → ZFSet.{u} := by
  letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  exact fun H i => ZFSet.sep (fun c => ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈
    M.countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H) C

theorem mem_binaryGenericRow (I C : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) (i c : ZFSet.{u}),
      c ∈ M.binaryGenericRow I C H i ↔ c ∈ C ∧
        ZFSet.pair (ZFSet.pair i c) (natSetCode 1) ∈
          M.countableGenericGraph (ZFSet.prod I C) (natSetCode 2) H := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H i c
  exact ZFSet.mem_sep

theorem binaryGenericRow_subset (I C : ZFSet.{u}) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ (H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) (i : ZFSet.{u}),
      M.binaryGenericRow I C H i ⊆ C := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H i c hc
  exact ((M.mem_binaryGenericRow I C H i c).1 hc).1

theorem binaryGenericRow_ne
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C i j : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (hi : i ∈ I) (hj : j ∈ I) (distinct : i ≠ j)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) →
      M.binaryGenericRow I C H i ≠ M.binaryGenericRow I C H j := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H generic same
  obtain ⟨c, hc, a, ha, b, hb, ne, first, second, absent⟩ :=
    M.countableGenericGraph_rows_separated pairing unions powers separation infinite choice
      hI hC (M.natSetCode_mem separation infinite 2) hi hj distinct
      two_distinct_values uncountable H generic
  rcases (mem_two_iff a).1 ha with rfl | rfl
  · rcases (mem_two_iff b).1 hb with rfl | rfl
    · exact ne rfl
    · have right := (M.mem_binaryGenericRow I C H j c).2 ⟨hc, second⟩
      have left := (M.mem_binaryGenericRow I C H i c).1 (same ▸ right)
      have impossible := natSetCode_injective
        ((M.countableGenericGraph_partial (ZFSet.prod I C) (natSetCode 2) H).unique
          (ZFSet.pair i c) (natSetCode 1) (natSetCode 0) left.2 first)
      omega
  · have left := (M.mem_binaryGenericRow I C H i c).2 ⟨hc, first⟩
    exact absent ((M.mem_binaryGenericRow I C H j c).1 (same ▸ left)).2

theorem binaryGenericRows_injective
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {I C : ZFSet.{u}} (hI : I ∈ M.sets) (hC : C ∈ M.sets)
    (uncountable : ¬ M.groundEmbeddable C ZFSet.omega) :
    letI := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
    ∀ H : ConditionFilter (SetMembers
      (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega)),
      H.GenericFor (M.codedFamily (SetMembers.presentation
        (M.smallPartialFunctions (ZFSet.prod I C) (natSetCode 2) ZFSet.omega))) →
      Function.Injective (fun i : SetMembers I => M.binaryGenericRow I C H (SetMembers.raw i)) := by
  let := M.smallFunctionOrder (ZFSet.prod I C) (natSetCode 2) ZFSet.omega
  intro H generic i j same
  apply SetMembers.raw_injective I
  by_contra distinct
  exact M.binaryGenericRow_ne pairing unions powers separation infinite choice hI hC
    (SetMembers.raw_mem i) (SetMembers.raw_mem j) distinct uncountable H generic same

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
