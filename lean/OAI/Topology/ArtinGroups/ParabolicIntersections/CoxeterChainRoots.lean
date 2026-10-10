import OAI.Topology.ArtinGroups.ParabolicIntersections.NormalParabolic
import OAI.Topology.ArtinGroups.Geometry.CartanOffNonpos

namespace OAI

/-! Positive roots carried along a simple path in the noncommutation graph. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
open scoped _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

lemma reflection_nonneg_of_zero (a : S) (x : S → ℝ) (hx : ∀ i, 0≤x i) (ha : x a=0) :
    ∀ i, 0 ≤ simpleReflection M a x i := by
  have hr : (cartan M *ᵥ x) a≤0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hj : a=j
    · subst j
      rw [ha,mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (cartan_off_nonpos M a j hj) (hx j)
  intro i
  rw [simpleReflection_apply]
  by_cases hi : i=a
  · subst i
    simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one,ha,zero_sub]
      using neg_nonneg.mpr hr
  · simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_of_ne hi,mul_zero,sub_zero]
      using hx i

lemma reflection_pos_of_neighbor (a b : S) (hab : a≠b) (hm : M a b≠2)
    (x : S → ℝ) (hx : ∀ i, 0≤x i) (ha : x a=0) (hb : 0<x b) :
    0 < simpleReflection M a x a := by
  have hc : cartan M a b<0 :=
    lt_of_le_of_ne (cartan_off_nonpos M a b hab) (cartan_ne_zero_of_not_commuting M a b hab hm)
  have hrow : (cartan M *ᵥ x) a<0 := by
    change (∑ j, cartan M a j*x j)<0
    have hsum := Finset.sum_lt_sum (s := (Finset.univ : Finset S))
      (f := fun j => cartan M a j*x j) (g := fun _ => (0 : ℝ))
      (by
        intro j _
        by_cases hj : a=j
        · subst j
          rw [ha,mul_zero]
        · exact mul_nonpos_of_nonpos_of_nonneg (cartan_off_nonpos M a j hj) (hx j))
      ⟨b,Finset.mem_univ _,mul_neg_of_neg_of_pos hc hb⟩
    simpa only [Finset.sum_const_zero] using hsum
  rw [simpleReflection_apply]
  simpa only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,mul_one,ha,zero_sub]
    using neg_pos.mpr hrow

/-- A word of distinct vertices along a noncommutation path carries the
last simple root to a nonnegative root positive at every vertex of the path. -/
theorem root_along_chain (u : List S) (s : S) (hN : (u++[s]).Nodup)
    (hC : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2)) :
    let x := representation M.toCoxeterSystem (M.toCoxeterSystem.wordProd u) (Pi.single s 1)
    (∀ i, 0 ≤ x i) ∧ (∀ i∈u++[s], 0 < x i) ∧ (∀ i, i∉u++[s] → x i=0) := by
  induction u with
  | nil =>
    simp only [List.nil_append,CoxeterSystem.wordProd_nil,map_one]
    change (∀ i, 0 ≤ (Pi.single s (1 : ℝ) : S → ℝ) i) ∧
      (∀ i∈[s], 0 < (Pi.single s (1 : ℝ) : S → ℝ) i) ∧
      (∀ i, i∉[s] → (Pi.single s (1 : ℝ) : S → ℝ) i=0)
    refine ⟨?_,?_,?_⟩
    · intro i
      by_cases hi : i=s <;> simp [hi]
    · intro i hi
      have hi' : i=s := List.mem_singleton.mp hi
      subst i
      simpa only [Pi.single_eq_same] using (zero_lt_one : (0 : ℝ)<1)
    · intro i hi
      exact Pi.single_eq_of_ne (by simpa only [List.mem_singleton] using hi) 1
  | cons a u ih =>
    obtain ⟨hna,hn⟩ := List.nodup_cons.mp hN
    have hc : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2) := hC.tail
    obtain ⟨hx,hpos,hzero⟩ := ih hn hc
    let x := representation M.toCoxeterSystem (M.toCoxeterSystem.wordProd u) (Pi.single s 1)
    have hxa : x a=0 := hzero a hna
    obtain ⟨b,hb,hab,hm⟩ : ∃ b∈u++[s], a≠b ∧ M a b≠2 := by
      cases u with
      | nil => exact ⟨s,by simp,(List.isChain_cons_cons.mp hC).1⟩
      | cons b u => exact ⟨b,by simp,(List.isChain_cons_cons.mp hC).1⟩
    have hpa := reflection_pos_of_neighbor M a b hab hm x hx hxa (hpos b hb)
    simp only [List.cons_append,CoxeterSystem.wordProd_cons,map_mul,LinearEquiv.mul_apply,
      representation_simple]
    change (∀ i,0 ≤ simpleReflection M a x i) ∧
      (∀ i∈a::(u++[s]),0 < simpleReflection M a x i) ∧
      (∀ i,i∉a::(u++[s]) → simpleReflection M a x i=0)
    refine ⟨reflection_nonneg_of_zero M a x hx hxa,?_,?_⟩
    · intro i hi
      rcases List.mem_cons.mp hi with rfl|hi
      · exact hpa
      · have hia : i≠a := fun he => hna (he ▸ hi)
        simpa only [simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
          Pi.single_eq_of_ne hia,mul_zero,sub_zero] using hpos i hi
    · intro i hi
      have hia : i≠a := fun he => hi (List.mem_cons.mpr (Or.inl he))
      have hiu : i∉u++[s] := fun hm => hi (List.mem_cons_of_mem a hm)
      simpa only [simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
        Pi.single_eq_of_ne hia,mul_zero,sub_zero] using hzero i hiu

end HarmonicArtin.ParabolicIntersections

end OAI
