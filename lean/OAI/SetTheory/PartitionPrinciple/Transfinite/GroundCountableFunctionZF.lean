import OAI.SetTheory.PartitionPrinciple.Forcing.GroundOutsideRowNames
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPrincipalSupportZF

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula
universe u
variable (M : TransitiveGround.{u}) {X Y I G : Type u}
variable [Group G] [PartialOrder X] [PartialOrder I]

theorem exists_countableFunction_ZF
    (a : PosetAction G X) (d : PosetAction G I)
    (s : Presentation X) (t : Presentation Y) (b : Presentation G) (k : Presentation I)
    (C : I) (directed : ∀ C D : I, ∃ E, C ≤ E ∧ D ≤ E)
    (small : M.sets.Countable)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) (collection : CollectionSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hX : s.carrier ∈ M.sets) (hY : t.carrier ∈ M.sets) (values : t.carrier.Nonempty)
    (hG : b.carrier ∈ M.sets) (hI : k.carrier ∈ M.sets)
    (coordinate_graph : a.actionGraph s b ∈ M.sets)
    (support_order : k.conditionOrder ∈ M.sets) (support_graph : d.actionGraph k b ∈ M.sets)
    (p : SetMembers (M.smallPartialFunctions s.carrier t.carrier ZFSet.omega)) :
    letI := M.smallFunctionOrder s.carrier t.carrier ZFSet.omega
    let act := M.smallFunctionAction a s t b pairing unions powers separation hX hY hG
      (M.omega_mem separation infinite) coordinate_graph
    let c := SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier ZFSet.omega)
    let F := d.principalSupportFamily C directed
    ∃ H : ConditionFilter (SetMembers (M.smallPartialFunctions s.carrier t.carrier ZFSet.omega)),
      H.mem p ∧ H.GenericFor (M.codedFamily c) ∧
      H.GenericFor (formulaFamily (M.nameDomain c)) ∧
      H.GenericFor (formulaFamily (act.symmetricDomain c (M.nameDomain c) F)) ∧
      M.sets ⊆ (act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q} ∧
      ZFRealization ((act.symmetricDomain c (M.nameDomain c) F).values {q | H.mem q}) ∧
      ZFSet.IsFunc s.carrier t.carrier (M.countableGenericGraph s.carrier t.carrier H) := by
  let := M.smallFunctionOrder s.carrier t.carrier ZFSet.omega
  let := M.smallFunctionTop s.carrier t.carrier ZFSet.omega ⟨s.carrier, hX⟩
  let act := M.smallFunctionAction a s t b pairing unions powers separation hX hY hG
    (M.omega_mem separation infinite) coordinate_graph
  let c := SetMembers.presentation (M.smallPartialFunctions s.carrier t.carrier ZFSet.omega)
  obtain ⟨H, hp, ground, ordinary, symmetric, includes, zf⟩ :=
    M.exists_ZF_from_principalSupports d act k c b C directed small pairing unions powers separation collection infinite
      (M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY)
      (M.countableFunctionOrder_mem pairing unions powers separation infinite hX hY)
      hG hI support_order support_graph
      (M.smallFunctionActionGraph_mem a s t b pairing unions powers separation hX hY hG
        (M.omega_mem separation infinite) coordinate_graph) p
  exact ⟨H, hp, ground, ordinary, symmetric, includes, zf,
    M.countableGenericGraph_isFunc pairing unions powers separation infinite hX hY values H ground⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
