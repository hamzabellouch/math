import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma root_nonpos_iff_descent (w : W) (s : S) :
    (∀ k,representation cs w (Pi.single s 1) k≤0) ↔
      cs.length (w*cs.simple s)+1=cs.length w := by
  constructor
  · intro hn
    rcases cs.length_mul_simple w s with ha | hd
    · have hp := root_nonneg_of_ascent cs w s ha
      exact (geometric_root_ne_zero cs w s (funext (fun k => le_antisymm (hn k) (hp k)))).elim
    · exact hd
  · exact root_nonpos_of_descent cs w s

lemma vector_eq_sum_simple (x : S → ℝ) : x=∑ i,x i • Pi.single i 1 := by
  ext k
  simp [Finset.sum_apply,Pi.single_apply]

lemma representation_nonpos_of_columns (z : W)
    (hz : ∀ i k,representation cs z (Pi.single i 1) k≤0)
    (x : S → ℝ) (hx : ∀ i,0 ≤ x i) : ∀ k,representation cs z x k≤0 := by
  intro k
  rw [vector_eq_sum_simple x,map_sum,Finset.sum_apply]
  apply Finset.sum_nonpos
  intro i _
  rw [map_smul]
  exact mul_nonpos_of_nonneg_of_nonpos (hx i) (hz i k)

theorem length_mul_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) (w : W) :
    cs.length (z*w)+cs.length w=cs.length z := by
  have hcols : ∀ i k,representation cs z (Pi.single i 1) k≤0 :=
    fun i => root_nonpos_of_descent cs z i (hz i)
  have H : ∀ u : List S,cs.IsReduced u → cs.length (z*cs.wordProd u)+u.length=cs.length z := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u i ih =>
      intro hr
      have hru : cs.IsReduced u := by simpa only [List.take_left] using hr.take u.length
      have hp := ih hru
      have has : cs.length (cs.wordProd u*cs.simple i)=cs.length (cs.wordProd u)+1 := by
        simpa only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,
          List.length_singleton,hru.eq] using hr.eq
      have hroot := root_nonneg_of_ascent cs (cs.wordProd u) i has
      have hneg : ∀ k,representation cs (z*cs.wordProd u) (Pi.single i 1) k≤0 := by
        rw [map_mul]
        exact representation_nonpos_of_columns cs z hcols _ hroot
      have hstep := (root_nonpos_iff_descent cs (z*cs.wordProd u) i).mp hneg
      simp only [cs.wordProd_append,cs.wordProd_singleton,List.length_append,List.length_singleton]
      rw [← mul_assoc]
      omega
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
  simpa only [← hu.eq,← he] using H u hu

lemma length_le_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) (w : W) :
    cs.length w≤cs.length z := by
  have := length_mul_of_all_descents cs z hz w
  omega

theorem finite_of_all_descents (z : W)
    (hz : ∀ i,cs.length (z*cs.simple i)+1=cs.length z) : Finite W := by
  apply Set.finite_univ_iff.mp
  apply ((List.finite_length_le S (cs.length z)).image cs.wordProd).subset
  intro w _
  obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
  refine ⟨u,?_,he.symm⟩
  change u.length≤cs.length z
  rw [← hu.eq,← he]
  exact length_le_of_all_descents cs z hz w

omit [Fintype S] [DecidableEq S] in
lemma exists_longest [Finite W] : ∃ z : W,∀ w : W,cs.length w≤cs.length z := by
  let : Fintype W := Fintype.ofFinite W
  obtain ⟨z,_,hz⟩ := Finset.exists_max_image (Finset.univ : Finset W) cs.length Finset.univ_nonempty
  exact ⟨z,fun w => hz w (Finset.mem_univ _)⟩

omit [Fintype S] [DecidableEq S] in
lemma all_descents_of_longest (z : W) (hz : ∀ w,cs.length w≤cs.length z) (i : S) :
    cs.length (z*cs.simple i)+1=cs.length z := by
  have h := hz (z*cs.simple i)
  rcases cs.length_mul_simple z i with ha | hd <;> omega

omit [Fintype S] [DecidableEq S] in
lemma all_left_descents_of_longest (z : W) (hz : ∀ w,cs.length w≤cs.length z) (i : S) :
    cs.length (cs.simple i*z)+1=cs.length z := by
  have h := hz (cs.simple i*z)
  rcases cs.length_simple_mul z i with ha | hd <;> omega

end HarmonicArtin.Geometric

end OAI
