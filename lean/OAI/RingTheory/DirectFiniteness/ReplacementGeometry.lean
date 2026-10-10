import OAI.RingTheory.DirectFiniteness.CandidateCounting

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype Q] [Fintype A]
namespace DirectionFrame
variable (F : DirectionFrame Q A R E) (S O : Finset A)

def replacementRegion (r : R) : Finset A := O.biUnion (fun o => cosetPoints (F.W r) o)

omit [Fintype Q] in
@[simp] lemma mem_replacementRegion (r : R) (x : A) :
    x ∈ F.replacementRegion O r ↔ ∃ o ∈ O, x-o ∈ F.W r := by
  simp [replacementRegion]

lemma generic_region_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) (C : AffineCoset (F.U j)) (r : R) :
    (C.val ∩ F.replacementRegion O r).card ≤ 100 * Fintype.card Q := by
  obtain ⟨x,hx⟩ := C.property
  let H := O.filter (fun o => o-x ∈ F.U j ⊔ F.W r)
  have hsub : C.val ∩ F.replacementRegion O r ⊆
      H.biUnion (fun o => C.val ∩ cosetPoints (F.W r) o) := by
    intro y hy
    obtain ⟨hyC,hyT⟩ := Finset.mem_inter.mp hy
    obtain ⟨o,ho,hyo⟩ := (F.mem_replacementRegion O r y).mp hyT
    have hyx : y-x ∈ F.U j := by
      rw [hx] at hyC
      exact (mem_cosetPoints _ _ _).mp hyC
    have hox : o-x ∈ F.U j ⊔ F.W r := by
      convert (F.U j ⊔ F.W r).sub_mem
        ((show F.U j ≤ F.U j ⊔ F.W r from le_sup_left) hyx)
        ((show F.W r ≤ F.U j ⊔ F.W r from le_sup_right) hyo) using 1; abel
    exact Finset.mem_biUnion.mpr ⟨o,Finset.mem_filter.mpr ⟨ho,hox⟩,
      Finset.mem_inter.mpr ⟨hyC,(mem_cosetPoints _ _ _).mpr hyo⟩⟩
  have hi (o : A) : (C.val ∩ cosetPoints (F.W r) o).card ≤ Fintype.card Q := by
    rw [hx]
    by_cases hr : j.1 = r
    · have hh := intersection_cosets_card_le (F.U j) (F.W r) x o
      rw [← hr,F.U_inf_W_same,F.card_D] at hh
      simpa only [hr] using hh
    · exact (intersection_cosets_card_le_one _ _ (F.U_W_disjoint hr) _ _).trans
        (Fintype.card_pos)
  calc
    _ ≤ (H.biUnion (fun o => C.val ∩ cosetPoints (F.W r) o)).card := Finset.card_le_card hsub
    _ ≤ ∑ o ∈ H, (C.val ∩ cosetPoints (F.W r) o).card := Finset.card_biUnion_le
    _ ≤ ∑ _o ∈ H, Fintype.card Q := Finset.sum_le_sum (fun o _ => hi o)
    _ = H.card * Fintype.card Q := by simp
    _ ≤ 100 * Fintype.card Q := Nat.mul_le_mul_right _ (hO.occupancy j r x)

omit [Fintype Q] in
lemma holes_in_coset_card (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) (C : AffineCoset (F.U j)) : (O ∩ C.val).card ≤ 100 := by
  obtain ⟨x,hx⟩ := C.property
  have hs : O ∩ C.val ⊆ O.filter (fun o => o-x ∈ F.U j ⊔ F.W j.1) := by
    intro o ho
    obtain ⟨hoO,hoC⟩ := Finset.mem_inter.mp ho
    have hmember : o-x ∈ F.U j := by
      rw [hx] at hoC
      exact (mem_cosetPoints _ _ _).mp hoC
    exact Finset.mem_filter.mpr ⟨hoO,(show F.U j ≤ F.U j ⊔ F.W j.1 from le_sup_left)
      hmember⟩
  exact (Finset.card_le_card hs).trans (hO.occupancy j j.1 x)

omit [Fintype Q] [Fintype A] in
lemma different_holes_nonzero_component (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (j : R × Q) {x y : A} (hx : x ∈ O) (hy : y ∈ O) (hne : y ≠ x)
    (v : Q × E) (hv : F.u j v = y-x) : v.2 ≠ 0 := by
  intro hz
  have hm : y-x ∈ F.W j.1 := by
    rw [← hv,F.u_apply,hz,map_zero,add_zero]
    exact ⟨(v.1,v.1*j.2),rfl⟩
  exact hne (hO.collision j.1 x hx y hy hm)

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
