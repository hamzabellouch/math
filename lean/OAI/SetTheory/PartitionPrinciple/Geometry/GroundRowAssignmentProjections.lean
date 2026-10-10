import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def rowAssignmentRows (Q C B : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction Q (productFirst C B)

noncomputable def rowAssignmentData (Q C B : ZFSet.{u}) : ZFSet.{u} :=
  graphRestriction Q (productSecond C B)

theorem rowAssignmentRows_entry (Q C B p A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p A) x ∈ rowAssignmentRows Q C B ↔
      ZFSet.pair p A ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ x = p := by
  rw [rowAssignmentRows, pair_mem_graphRestriction, mem_productFirst]
  constructor
  · rintro ⟨⟨q,hq,D,hD,equal⟩,member⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    exact ⟨member,hq,hD,right⟩
  · rintro ⟨member,hp,hA,equal⟩
    subst x
    exact ⟨⟨p,hp,A,hA,rfl⟩,member⟩

theorem rowAssignmentData_entry (Q C B p A x : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair p A) x ∈ rowAssignmentData Q C B ↔
      ZFSet.pair p A ∈ Q ∧ p ∈ C ∧ A ∈ B ∧ x = A := by
  rw [rowAssignmentData, pair_mem_graphRestriction, mem_productSecond]
  constructor
  · rintro ⟨⟨q,hq,D,hD,equal⟩,member⟩
    obtain ⟨left,right⟩ := ZFSet.pair_injective equal
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_injective left
    exact ⟨member,hq,hD,right⟩
  · rintro ⟨member,hp,hA,equal⟩
    subst x
    exact ⟨⟨p,hp,A,hA,rfl⟩,member⟩

private theorem restrict_function {Q A B f : ZFSet.{u}}
    (function : ZFSet.IsFunc A B f) (subset : Q ⊆ A) :
    ZFSet.IsFunc Q B (graphRestriction Q f) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨x,hx,y,rfl,entry⟩ := mem_graphRestriction.1 hz
    exact ZFSet.pair_mem_prod.2 ⟨hx,(ZFSet.pair_mem_prod.1 (function.1 entry)).2⟩
  · intro x hx
    obtain ⟨y,entry,unique⟩ := function.2 x (subset hx)
    exact ⟨y,pair_mem_graphRestriction.2 ⟨entry,hx⟩,
      fun z hz => unique z (pair_mem_graphRestriction.1 hz).1⟩

theorem rowAssignmentRows_function {Q C B : ZFSet.{u}} (subset : Q ⊆ ZFSet.prod C B) :
    ZFSet.IsFunc Q C (rowAssignmentRows Q C B) :=
  restrict_function (productFirst_function C B) subset

theorem rowAssignmentData_function {Q C B : ZFSet.{u}} (subset : Q ⊆ ZFSet.prod C B) :
    ZFSet.IsFunc Q B (rowAssignmentData Q C B) :=
  restrict_function (productSecond_function C B) subset

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem rowAssignmentRows_mem {Q C B : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) :
    rowAssignmentRows Q C B ∈ M.sets :=
  M.graphRestriction_mem unions separation hQ (M.productFirst_mem pairing unions powers separation hC hB)

theorem rowAssignmentData_mem {Q C B : ZFSet.{u}}
    (hQ : Q ∈ M.sets) (hC : C ∈ M.sets) (hB : B ∈ M.sets) :
    rowAssignmentData Q C B ∈ M.sets :=
  M.graphRestriction_mem unions separation hQ (M.productSecond_mem pairing unions powers separation hC hB)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
