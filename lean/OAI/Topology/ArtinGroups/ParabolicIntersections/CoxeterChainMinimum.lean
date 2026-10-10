import OAI.Topology.ArtinGroups.ParabolicIntersections.CoxeterChainRoots
import OAI.Topology.ArtinGroups.ParabolicIntersections.ParabolicMinimumStep

namespace OAI

/-! A noncommutation path starting outside a parabolic gives a minimal
Coxeter coset representative. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma conjugate_simple_not_parabolic (X : Set S) (w : M.Group) (s t : S) (ht : t∉X)
    (hr : representation cs w (Pi.single s 1) t≠0) :
    w*(cs).simple s*w⁻¹∉parabolic cs X := by
  intro hm
  let x := representation cs w (Pi.single s 1)
  have hn : simpleReflection M s (Pi.single s 1)=-(Pi.single s 1) := by
    simp only [simpleReflection_apply,Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,
      MulOpposite.op_one,one_smul,cartan_diag]
    module
  have he : representation cs (w*(cs).simple s*w⁻¹) x=-x := by
    calc
      representation cs (w*(cs).simple s*w⁻¹) x =
          representation cs ((w*(cs).simple s*w⁻¹)*w) (Pi.single s 1) := by
        exact (DFunLike.congr_fun (map_mul (representation cs)
          (w*(cs).simple s*w⁻¹) w) (Pi.single s 1)).symm
      _ = representation cs (w*(cs).simple s) (Pi.single s 1) := by
        congr 2
        group
      _ = representation cs w (simpleReflection M s (Pi.single s 1)) := by
        rw [map_mul,LinearEquiv.mul_apply,representation_simple]
      _ = -x := by rw [hn,map_neg]
  have hx := parabolic_exterior M X ⟨_,hm⟩ x t ht
  change representation cs (w*(cs).simple s*w⁻¹) x t=x t at hx
  rw [he] at hx
  change -x t=x t at hx
  exact hr (by change x t=0; linarith)

lemma minimum_append_chain (X : Set S) (u : List S) (s t : S)
    (hmin : IsParabolicMinimum cs X ((cs).wordProd u))
    (hN : (u++[s]).Nodup)
    (hC : (u++[s]).IsChain (fun a b => a≠b ∧ M a b≠2))
    (ht : t∈u++[s]) (htX : t∉X) :
    IsParabolicMinimum cs X ((cs).wordProd (u++[s])) := by
  rw [(cs).wordProd_append,(cs).wordProd_singleton]
  rcases parabolic_minimum_step cs X _ hmin s with h|⟨j,hj,he⟩
  · exact h
  · have hr := (root_along_chain M u s hN hC).2.1 t ht
    apply False.elim
    apply conjugate_simple_not_parabolic M X ((cs).wordProd u) s t htX (ne_of_gt hr)
    have hh : (cs).wordProd u*(cs).simple s*((cs).wordProd u)⁻¹=(cs).simple j := by
      rw [he,mul_inv_cancel_right]
    rw [hh]
    exact simple_mem_parabolic cs X hj

/-- Every prefix of a simple noncommutation path starting outside `X` is
minimal in its left `X`-coset. -/
theorem chain_word_minimum (X : Set S) (a : S) (ha : a∉X) (u : List S)
    (hN : (a::u).Nodup) (hC : (a::u).IsChain (fun a b => a≠b ∧ M a b≠2)) :
    IsParabolicMinimum cs X ((cs).wordProd (a::u)) := by
  induction u using List.reverseRecOn with
  | nil =>
    apply minimum_append_chain M X [] a a
    · intro g _
      simp only [(cs).wordProd_nil,(cs).length_one]
      exact Nat.zero_le _
    · exact hN
    · exact hC
    · simp only [List.nil_append,List.mem_singleton]
    · exact ha
  | append_singleton u s ih =>
    have hn : ((a::u)++[s]).Nodup := hN
    have hc : ((a::u)++[s]).IsChain (fun a b => a≠b ∧ M a b≠2) := hC
    apply minimum_append_chain M X (a::u) s a
    · exact ih (List.nodup_append.mp hn).1 hc.left_of_append
    · exact hn
    · exact hc
    · exact List.mem_append_left _ List.mem_cons_self
    · exact ha

end HarmonicArtin.ParabolicIntersections

end OAI
