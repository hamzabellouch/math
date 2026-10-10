import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRowTermSetNames

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {L G : Type u}
variable [PartialOrder L] [OrderBot L] [Group G]
variable (a : PosetAction G L) (s : Presentation L) (b : Presentation G) (C : ZFSet.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hL : s.carrier ∈ M.sets) (hC : C ∈ M.sets) (hG : b.carrier ∈ M.sets)
variable (graph : a.actionGraph s b ∈ M.sets)

theorem liftedRowTuple_supported {mu : ZFSet.{u}} (hmu : mu ∈ M.sets)
    (ordinal : ordinalSetProperty mu) :
    letI := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    letI := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
      ⟨s.carrier, hL⟩
    let act := M.internalRowAction a s b C pairing unions powers separation infinite hL hC hG graph
    let c := SetMembers.presentation (M.smallPartialFunctions
      (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega)
    let rows := M.binaryRowNameGraph s.nonbottom.carrier C ⊤
    let S := M.rowPositionSequences s.carrier s.conditionOrder s.nonbottom.carrier mu
    let T := rowTupleTerms (c.encode ⊤) mu s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S
    ∀ (valid : ∀ z ∈ T, IsName c z) (f : ZFSet.{u}) (τ : Name c.pairEmpty) (D : L),
      ZFSet.pair f τ.val ∈ liftedRowTupleFamily c (c.encode ⊤) mu s.nonbottom.carrier
        (⋃₀ ⋃₀ rows) rows S valid →
      (∀ i x, ZFSet.pair i x ∈ f → ZFSet.pair x (s.encode D) ∈ s.conditionOrder) →
      a.principalFix D ≤ act.stabilizer c.pairEmpty τ := by
  let := M.smallFunctionOrder (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
  let := M.smallFunctionTop (ZFSet.prod s.nonbottom.carrier C) (natSetCode 2) ZFSet.omega
    ⟨s.carrier, hL⟩
  intro act c rows S T valid f τ D entry bounded
  obtain ⟨hf, σ, source, lifted⟩ := (pair_mem_liftedRowTupleFamily c (c.encode ⊤) mu
    s.nonbottom.carrier (⋃₀ ⋃₀ rows) rows S valid f τ.val).1 entry
  obtain ⟨_, δ, _, _, subset, function, positions, _, values, _⟩ :=
    M.rowPositionSequence_decode s hL hmu ordinal hf
  have bound (i : δ.toSet) : (positions i).val ≤ D := by
    have positionOrder := bounded i.val (function.value i) (function.value_entry i)
    rw [values i] at positionOrder
    exact (s.pair_mem_conditionOrder (positions i).val D).1 positionOrder
  have same : σ = M.internalRowTupleName s C hL δ positions :=
    Subtype.ext (source.trans (M.internalRowTupleCode_eq s C hL function subset positions values))
  have sameLift : τ = Name.presentationEquiv c c.pairEmpty
      (M.internalRowTupleName s C hL δ positions) := by
    apply Subtype.ext
    change τ.val = (Name.rename c.pairEmpty id (M.internalRowTupleName s C hL δ positions)).val
    rw [lifted, same]
  rw [sameLift, act.stabilizer_presentationEquiv]
  exact M.internalRowTupleName_supported a s b C pairing unions powers separation infinite
    hL hC hG graph δ positions D bound

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
