import OAI.RingTheory.DirectFiniteness.PartitionMerging

namespace OAI

universe u_1

noncomputable section
open scoped Classical
open scoped BigOperators
open Equiv Equiv.Perm
namespace KaplanskyCounterexample.Planar
open Equiv Equiv.Perm
variable {α : Type u_1} [Fintype α]

lemma quotient_card_antitone {s t : Setoid α} (h : s ≤ t) :
    Nat.card (Quotient t) ≤ Nat.card (Quotient s) := by
  exact Nat.card_le_card_of_surjective (Quotient.map id (fun _ _ hxy => h hxy))
    (Quotient.map_surjective _ Function.surjective_id)

/-- Connected components of a bipartite rotation system, including edge
components consisting of a single edge. Isolated vertices are not encoded. -/
def Ribbon.components (R : Ribbon α) : Setoid α :=
  SameCycle.setoid R.black ⊔ SameCycle.setoid R.white

omit [Fintype α] in
lemma cycles_inv_card (p : Perm α) : Nat.card (Cycles p⁻¹) = Nat.card (Cycles p) := by
  have h : SameCycle.setoid p⁻¹ = SameCycle.setoid p := by
    ext a b
    exact sameCycle_inv
  unfold Cycles
  rw [h]

/-- The elementary genus inequality for an arbitrary finite ribbon system.
This supplies the topological constraint needed when components are discarded
in the planar minimality argument; it is not assumed as an extra hypothesis. -/
theorem Ribbon.euler_le (R : Ribbon α) :
    Nat.card (Cycles R.black) + Nat.card (Cycles R.white) + Nat.card (Cycles R.face) ≤
      Fintype.card α + 2 * Nat.card (Quotient R.components) := by
  obtain ⟨lb, hb, hblen, _⟩ := exists_cycle_factorization R.black
  obtain ⟨lw, hw, hwlen, _⟩ := exists_cycle_factorization R.white
  obtain ⟨lf, hf, hflen, _⟩ := exists_cycle_factorization R.face⁻¹
  rw [cycles_inv_card] at hflen
  let l := lw ++ lb ++ lf
  have hl : (l.map fun ab => swap ab.1 ab.2).prod = 1 := by
    simp only [l, List.map_append, List.prod_append, hb, hw, hf]
    change R.face * R.face⁻¹ = 1
    exact mul_inv_cancel _
  have hbl : edgePartition lb ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hwl : edgePartition lw ≤ edgePartition l := by
    apply edgePartition_le
    intro ab hab
    apply edgePartition_pair
    simp [l, hab]
  have hcomp : R.components ≤ edgePartition l := by
    apply sup_le
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.black _ hxy
      intro x
      rw [← hb]
      exact hbl (edgePartition_prod lb x)
    · intro x y hxy
      apply setoid_sameCycle_of_step (edgePartition l) R.white _ hxy
      intro x
      rw [← hw]
      exact hwl (edgePartition_prod lw x)
  have hc := quotient_card_antitone hcomp
  have hbound := transposition_euler_bound l
  rw [hl, cycles_one_card] at hbound
  have hlen : l.length = lw.length + lb.length + lf.length := by simp [l, Nat.add_assoc]
  omega

end KaplanskyCounterexample.Planar

end

end OAI
