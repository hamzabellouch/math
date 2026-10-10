import OAI.SetTheory.PartitionPrinciple.Definability.GroundRegularFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

def GroundInaccessibleConditions (M : TransitiveGround.{u}) (K : ZFSet.{u}) : Prop :=
  ordinalSetProperty K ∧ ZFSet.omega ∈ K ∧ GroundRegular M K ∧ GroundStrongLimit M K

namespace SetFormula

def groundInaccessibleConditionsFormula {n} (k omega : Fin n) : SetFormula n :=
  .conj (BoundedFormula.ordinalFormula k).toFormula
    (.conj (.mem omega k) (.conj (groundRegularFormula k) (groundStrongLimitFormula k)))

def existsGroundInaccessibleConditionsFormula {n} (omega : Fin n) : SetFormula n :=
  ex (groundInaccessibleConditionsFormula 0 omega.succ)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundInaccessibleConditionsFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (k omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (groundInaccessibleConditionsFormula k omega) env ↔
      GroundInaccessibleConditions M (env k) := by
  change (Realize M.sets (BoundedFormula.ordinalFormula k).toFormula env ∧
    env omega ∈ env k ∧ Realize M.sets (groundRegularFormula k) env ∧
      Realize M.sets (groundStrongLimitFormula k) env) ↔
    (ordinalSetProperty (env k) ∧ ZFSet.omega ∈ env k ∧ GroundRegular M (env k) ∧ GroundStrongLimit M (env k))
  rw [actualOmega]
  exact and_congr ((BoundedFormula.realize_ordinalFormula M k env members).trans
    (ordinalSetProperty_iff (env k)).symm)
    (and_congr Iff.rfl (and_congr (M.realize_groundRegularFormula k env members)
      (M.realize_groundStrongLimitFormula powers k env members)))

theorem realize_existsGroundInaccessibleConditionsFormula
    (powers : Realize M.sets powerSet Fin.elim0)
    {n} (omega : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) (actualOmega : env omega = ZFSet.omega) :
    Realize M.sets (existsGroundInaccessibleConditionsFormula omega) env ↔
      ∃ K ∈ M.sets, GroundInaccessibleConditions M K := by
  rw [existsGroundInaccessibleConditionsFormula, realize_ex]
  exact exists_congr (fun K => and_congr_right (fun hK =>
    M.realize_groundInaccessibleConditionsFormula powers 0 omega.succ
      (extend K env) (Fin.cases hK members) actualOmega))

end TransitiveGround

namespace GroundRegular
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}

theorem no_surjection (regular : GroundRegular M K) {α f : ZFSet.{u}}
    (hα : α ∈ K) (hf : f ∈ M.sets) (function : ZFSet.IsFunc α K f)
    (onto : ∀ y ∈ K, ∃ x ∈ α, ZFSet.pair x y ∈ f) : False := by
  obtain ⟨δ, hδ, bounded⟩ := regular α hα f hf function
  obtain ⟨x, _, entry⟩ := onto δ hδ
  exact ZFSet.mem_irrefl δ (bounded x δ entry)

theorem not_embeddable_to_member (regular : GroundRegular M K)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hK : K ∈ M.sets) {α : ZFSet.{u}} (hα : α ∈ K) : ¬ M.groundEmbeddable K α := by
  intro small
  obtain ⟨f, hf, function, onto⟩ := M.groundEmbeddable_enumeration pairing unions powers separation
    hK (M.transitive hK hα) ⟨α, hα⟩ small
  exact regular.no_surjection hα hf function onto

end GroundRegular

namespace GroundInaccessibleConditions
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (conditions : GroundInaccessibleConditions M K)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (hK : K ∈ M.sets)
include conditions pairing unions powers separation hK

theorem internal_cardinal :
    ordinalSetProperty K ∧ ∀ α ∈ K, ¬ M.groundEmbeddable K α :=
  ⟨conditions.1, fun _ hα => conditions.2.2.1.not_embeddable_to_member
    pairing unions powers separation hK hα⟩

theorem not_countable : ¬ M.groundEmbeddable K ZFSet.omega :=
  conditions.2.2.1.not_embeddable_to_member pairing unions powers separation hK conditions.2.1

end GroundInaccessibleConditions

end PartitionPilot.Forcing

end

end OAI
