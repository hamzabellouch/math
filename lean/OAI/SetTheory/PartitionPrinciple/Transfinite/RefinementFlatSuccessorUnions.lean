import OAI.SetTheory.PartitionPrinciple.Geometry.GroundRefinementRawTestMonotonicity

namespace OAI

section

namespace PartitionPilot.Forcing
universe u
variable {P : Type u} [PartialOrder P]

structure FlatSuccessorUnionLaws (tests : ZFSet.{u} → P → Prop) : Prop where
  tests_union : ∀ (family : Nat → ZFSet.{u}) (rows : Nat → P) (p : P),
    (∀ n m, n ≤ m → family n ⊆ family m) →
    (∀ n, p ≤ rows n) → (∀ n, tests (family n) (rows n)) →
    tests (stageOneAssignmentUnion family) p

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {P : Type u}
variable [PartialOrder P] [OrderTop P] (s : Presentation P)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable {G L : Type u} [Group G] [PartialOrder L]
variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)
variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)
variable (system : NiceNameSystem M a s b d base directed T valid)

theorem refinementLevelFlatSuccessorUnionLaws (level T2 : ZFSet.{u}) :
    FlatSuccessorUnionLaws
      (M.refinementLevelTests s pairing unions powers separation collection carrier order hT valid
        a b d base directed system level T2) :=
  ⟨M.refinementLevelTests_union s pairing unions powers separation collection carrier order hT valid
    a b d base directed system level T2⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
