import OAI.Topology.ArtinGroups.ParabolicIntersections.CoxeterChainMinimum
import OAI.Topology.ArtinGroups.ParabolicIntersections.CoxeterProjectionSupport
import OAI.Topology.ArtinGroups.ParabolicIntersections.NoncommutingGraph

namespace OAI

/-! In irreducible type, two proper standard parabolics never multiply to
the whole Coxeter or Artin group. This detects proper parabolic subtrees. -/
namespace HarmonicArtin.ParabolicIntersections
open Geometric CoxeterExchange
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma coxeter_simple_not_parabolic (C : Set S) (s : S) (hs : s∉C) :
    (cs).simple s∉parabolic cs C := by
  intro hm
  have he := parabolic_exterior M C ⟨_,hm⟩ (Pi.single s 1) s hs
  change representation cs ((cs).simple s) (Pi.single s 1) s=(Pi.single s 1 : S → ℝ) s at he
  simp only [representation_simple,simpleReflection_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Pi.single_eq_same,Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,
    MulOpposite.op_one,one_smul,cartan_diag] at he
  norm_num at he

/-- A noncommutation path supplies an explicit missing double coset. -/
theorem coxeter_parabolic_product_proper (hIrred : IsIrreducible M)
    (X C : Set S) (hX : X≠Set.univ) (hC : C≠Set.univ) :
    ∃ w : M.Group, ∀ a∈parabolic cs X, ∀ b∈parabolic cs C, w≠a*b := by
  obtain ⟨s,hs⟩ := Set.nonempty_compl.mpr hX
  obtain ⟨t,ht⟩ := Set.nonempty_compl.mpr hC
  obtain ⟨p,hp⟩ := (noncommuting_reachable M hIrred s t).exists_isPath
  obtain ⟨u,d,v,he,hu,hd⟩ := list_first_outside C p.support ⟨t,p.end_mem_support,ht⟩
  have he' : p.support=(u++[d])++v := by
    rw [he,List.append_assoc]
    rfl
  have hn : (u++[d]).Nodup := (List.nodup_append.mp (he' ▸ hp.support_nodup)).1
  have hc : (u++[d]).IsChain (fun a b => a≠b ∧ M a b≠2) :=
    (show ((u++[d])++v).IsChain (noncommutingGraph M).Adj from
      he' ▸ p.isChain_adj_support).left_of_append
  have hfirst : p.support.headD s=s := by cases p <;> rfl
  have hh := congrArg (fun l : List S => l.headD s) he
  rw [hfirst] at hh
  have hhead : ∃ r, u++[d]=s::r := by
    cases u with
    | nil =>
      change s=d at hh
      subst d
      exact ⟨[],rfl⟩
    | cons a u =>
      change s=a at hh
      subst a
      exact ⟨u++[d],rfl⟩
  obtain ⟨r,hr⟩ := hhead
  have hmin : IsParabolicMinimum cs X ((cs).wordProd (u++[d])) := by
    rw [hr] at hn hc ⊢
    exact chain_word_minimum M X s hs r hn hc
  have hw : (cs).wordProd (u++[d])∉parabolic cs C := by
    intro hm
    rw [(cs).wordProd_append,(cs).wordProd_singleton] at hm
    have huC := wordProd_mem_parabolic cs C u hu
    have hdC := (parabolic cs C).mul_mem ((parabolic cs C).inv_mem huC) hm
    rw [inv_mul_cancel_left] at hdC
    exact coxeter_simple_not_parabolic M C d hd hdC
  exact ⟨_,fun a ha b hb => minimum_not_product cs X C _ hmin hw a b ha hb⟩

/-- The same proper-product statement for the actual Artin presentation. -/
theorem artin_parabolic_product_proper (hIrred : IsIrreducible M)
    (X C : Set S) (hX : X≠Set.univ) (hC : C≠Set.univ) :
    ∃ g : Artin M, ∀ a∈artinParabolic M X, ∀ b∈artinParabolic M C, g≠a*b := by
  obtain ⟨w,hw⟩ := coxeter_parabolic_product_proper M hIrred X C hX hC
  refine ⟨positiveLift M w,?_⟩
  intro a ha b hb he
  have hh := congrArg (artinCoxeter M) he
  rw [artinCoxeter_positiveLift,map_mul] at hh
  exact hw _ (artinCoxeter_mem_parabolic M ha) _ (artinCoxeter_mem_parabolic M hb) hh

end HarmonicArtin.ParabolicIntersections

end OAI
