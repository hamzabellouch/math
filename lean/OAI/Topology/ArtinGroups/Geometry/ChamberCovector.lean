import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootPair

namespace OAI

namespace HarmonicArtin.Geometric
open CoxeterExchange Matrix
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

noncomputable def chamberCovector (a : S → ℝ) : (S → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, a i • LinearMap.proj i

omit [DecidableEq S] in
lemma chamberCovector_apply (a x : S → ℝ) : chamberCovector a x = ∑ i, a i * x i := by
  simp [chamberCovector]

lemma chamberCovector_single (a : S → ℝ) (i : S) :
    chamberCovector a (Pi.single i 1) = a i := by
  simp [chamberCovector_apply, Pi.single_apply]

lemma nonnegative_covector_root (a : S → ℝ) (ha : ∀ i, 0 ≤ a i) (w : W) (s : S)
    (hw : cs.length (w * cs.simple s) = cs.length w + 1) :
    0 ≤ chamberCovector a (representation cs w (Pi.single s 1)) := by
  rw [chamberCovector_apply]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (root_nonneg_of_ascent cs w s hw i))

lemma orbit_dominant_bound (p : S → ℝ) (hp : cartan M *ᵥ p = 1)
    (a : S → ℝ) (ha : ∀ i, 0 ≤ a i) (w : W) :
    chamberCovector a (representation cs w p) ≤ chamberCovector a p := by
  have H : ∀ u : List S, cs.IsReduced u →
      chamberCovector a (representation cs (cs.wordProd u) p) ≤ chamberCovector a p := by
    intro u
    induction u using List.reverseRecOn with
    | nil => simp
    | append_singleton u s ih =>
      intro hr
      have hu : cs.IsReduced u := by simpa only [List.take_left] using hr.take u.length
      have has : cs.length (cs.wordProd u * cs.simple s) = cs.length (cs.wordProd u) + 1 := by
        simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
          List.length_singleton, hu.eq] using hr.eq
      have hn := nonnegative_covector_root cs a ha _ s has
      have hsp : simpleReflection M s p = p - Pi.single s 1 := by
        rw [simpleReflection_apply,hp]
        simp
      simpa only [cs.wordProd_append,cs.wordProd_singleton,map_mul,LinearEquiv.mul_apply,
        representation_simple,hsp,map_sub] using sub_le_iff_le_add.mpr
          ((ih hu).trans (le_add_of_nonneg_right hn))
  obtain ⟨u,hu,rfl⟩ := cs.exists_isReduced w
  exact H u hu

lemma chamberCovector_parabolic_invariant (a : S → ℝ) (w : W)
    (hw : w ∈ parabolic cs {i | a i = 0}) (x : S → ℝ) :
    chamberCovector a (representation cs w x) = chamberCovector a x := by
  obtain ⟨u,hu,hr,rfl⟩ := (mem_parabolic_iff_reduced_word cs _ w).mp hw
  clear hw hr
  induction u with
  | nil => simp
  | cons s u ih =>
    have hs : a s = 0 := hu s (by simp)
    have hu' : ∀ i ∈ u, i ∈ {i | a i = 0} := fun i hi => hu i (by simp [hi])
    simp only [cs.wordProd_cons,map_mul,LinearEquiv.mul_apply,representation_simple,
      simpleReflection_apply,map_sub,map_smul,chamberCovector_single,hs,smul_zero,sub_zero]
    exact ih hu'

theorem orbit_dominant_equality (p : S → ℝ) (hp : cartan M *ᵥ p = 1)
    (a : S → ℝ) (ha : ∀ i, 0 ≤ a i) (w : W) :
    chamberCovector a (representation cs w p) = chamberCovector a p ↔
      w ∈ parabolic cs {i | a i = 0} := by
  constructor
  · have H : ∀ u : List S, cs.IsReduced u →
        chamberCovector a (representation cs (cs.wordProd u) p) = chamberCovector a p →
        cs.wordProd u ∈ parabolic cs {i | a i = 0} := by
      intro u
      induction u using List.reverseRecOn with
      | nil => intro _ _; simp
      | append_singleton u s ih =>
        intro hr he
        have hu : cs.IsReduced u := by simpa only [List.take_left] using hr.take u.length
        have has : cs.length (cs.wordProd u * cs.simple s) = cs.length (cs.wordProd u) + 1 := by
          simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
            List.length_singleton, hu.eq] using hr.eq
        have hn := nonnegative_covector_root cs a ha _ s has
        have hb := orbit_dominant_bound cs p hp a ha (cs.wordProd u)
        have hsp : simpleReflection M s p = p - Pi.single s 1 := by
          rw [simpleReflection_apply,hp]; simp
        simp only [cs.wordProd_append,cs.wordProd_singleton,map_mul,LinearEquiv.mul_apply,
          representation_simple,hsp,map_sub] at he
        have he' : chamberCovector a (representation cs (cs.wordProd u) p) = chamberCovector a p := by
          linarith
        have hm := ih hu he'
        have hz : a s = 0 := by
          have hi := chamberCovector_parabolic_invariant cs a _ hm (Pi.single s 1)
          rw [chamberCovector_single] at hi
          linarith
        rw [cs.wordProd_append,cs.wordProd_singleton]
        exact (parabolic cs {i | a i = 0}).mul_mem hm (simple_mem_parabolic cs _ hz)
    obtain ⟨u,hu,rfl⟩ := cs.exists_isReduced w
    exact H u hu
  · intro hw
    exact chamberCovector_parabolic_invariant cs a w hw p

lemma orbitPoint_injective (p : S → ℝ) (hp : cartan M *ᵥ p = 1) :
    Function.Injective (fun w : W => representation cs w p) := by
  intro v w he
  dsimp only at he
  have hh : representation cs (w⁻¹*v) p = p := by
    rw [map_mul,LinearEquiv.mul_apply,he,←LinearEquiv.mul_apply,←map_mul,inv_mul_cancel,map_one]
    rfl
  have h := chamber_stabilizer cs p (fun i => by change 0 < (cartan M *ᵥ p) i; rw [hp]; norm_num) _ hh
  exact (inv_mul_eq_one.mp h).symm

end HarmonicArtin.Geometric

end OAI
