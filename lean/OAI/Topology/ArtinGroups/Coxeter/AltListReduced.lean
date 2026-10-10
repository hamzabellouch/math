import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent

namespace OAI

namespace HarmonicArtin.CoxeterExchange
open Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

theorem altList_reduced (i j : S) (hij : i≠j) (n : ℕ) (hn : M i j=0 ∨ n≤M i j) :
    cs.IsReduced (altList i j n) := by
  induction n with
  | zero => simp [CoxeterSystem.IsReduced]
  | succ n ih =>
    have hn' : M i j=0 ∨ n≤M i j := by omega
    have hred := ih hn'
    have hroot : ∀ k,0≤representation cs (cs.wordProd (altList i j n))
        (Pi.single (altNext i j n) 1) k := by
      rw [alternating_next_root cs i j hij n]
      intro k
      exact add_nonneg
        (mul_nonneg (dihedralScalar_nonneg _ _ hn) (by simp [Pi.single_apply]; split_ifs <;> norm_num))
        (mul_nonneg (dihedralScalar_nonneg _ _ hn') (by simp [Pi.single_apply]; split_ifs <;> norm_num))
    have ha := (root_nonneg_iff_ascent cs (cs.wordProd (altList i j n)) (altNext i j n)).mp hroot
    change cs.length (cs.wordProd (altList i j (n+1)))=(altList i j (n+1)).length
    rw [altList_succ_append,cs.wordProd_append,cs.wordProd_singleton,ha,hred.eq]
    simp

omit [Fintype S] [DecidableEq S] in
lemma pair_length_bound (i j : S) (hm : 2≤M i j) (w : W)
    (hw : w∈parabolic cs ({i,j} : Set S)) : cs.length w≤M i j := by
  obtain ⟨u,hu,hr,he⟩ := (mem_parabolic_iff_reduced_word cs _ _).mp hw
  cases u with
  | nil => simp only [cs.wordProd_nil] at he; simp [← he]
  | cons k u =>
    have hk := hu k (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with hk|hk
    · subst k
      have hs := reduced_pair_cons_eq_alt cs i j u hr (fun k hk => hu k (List.mem_cons_of_mem _ hk))
      have hb := reduced_altList_le cs i j (u.length+1) hm (hs ▸ hr)
      rw [← he,hr.eq,List.length_cons]
      exact hb
    · subst k
      have hs := reduced_pair_cons_eq_alt cs j i u hr
        (fun k hk => by simpa only [Set.pair_comm] using hu k (List.mem_cons_of_mem _ hk))
      have hb := reduced_altList_le cs j i (u.length+1) (by simpa only [M.symmetric j i] using hm) (hs ▸ hr)
      rw [← he,hr.eq,List.length_cons]
      simpa only [M.symmetric j i] using hb

omit [DecidableEq S] in
lemma finite_parabolic_pair (i j : S) (hm : 2≤M i j) : Finite (parabolic cs ({i,j} : Set S)) := by
  have ht : Set.Finite {w : W | cs.length w≤M i j} := by
    apply ((List.finite_length_le S (M i j)).image cs.wordProd).subset
    intro w hw
    obtain ⟨u,hu,he⟩ := cs.exists_isReduced w
    refine ⟨u,?_,he.symm⟩
    change u.length≤M i j
    rw [← hu.eq,← he]
    exact hw
  let : Finite {w : W // cs.length w≤M i j} := ht
  apply Finite.of_injective
    (fun w : parabolic cs ({i,j} : Set S) => (⟨w,pair_length_bound cs i j hm w w.property⟩ :
      {w : W // cs.length w≤M i j}))
  intro a b h
  exact Subtype.ext (congrArg (fun w : {w : W // cs.length w≤M i j} => (w:W)) h)

end HarmonicArtin.CoxeterExchange

end OAI
