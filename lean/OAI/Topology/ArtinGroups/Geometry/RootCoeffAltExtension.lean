import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.Parabolic
import OAI.Topology.ArtinGroups.Coxeter.AlternatingNextRoot

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.propDecidable Classical.decEq
variable {S W : Type*} [Fintype S] [DecidableEq S] [Group W]
  {M : CoxeterMatrix S} (cs : CoxeterSystem M W)

lemma root_coeff_of_alt_extension (i j : S) (hij : i ≠ j) (u : List S) (s : S)
    (he : u++[s] = altList i j (u.length+1)) (hr : cs.IsReduced (u++[s])) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧
      representation cs (cs.wordProd u) (Pi.single s 1) =
        x • Pi.single i 1 + y • Pi.single j 1 := by
  have hre : cs.IsReduced (altList i j (u.length+1)) := he ▸ hr
  rw [altList_succ_append] at he
  obtain ⟨hu,hs⟩ := List.append_inj he (by simp)
  have hs' : s = altNext i j u.length := by simpa using hs
  have hb : M i j = 0 ∨ u.length+1 ≤ M i j := by
    by_cases hm : M i j=0
    · exact Or.inl hm
    · have hm2 : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
      exact Or.inr (reduced_altList_le cs i j _ hm2 hre)
  refine ⟨dihedralScalar (M i j) (u.length+1),dihedralScalar (M i j) u.length,
    dihedralScalar_nonneg _ _ hb,dihedralScalar_nonneg _ _ (by omega),?_⟩
  rw [hu,hs']
  simpa only [length_altList] using alternating_next_root cs i j hij u.length

lemma pair_ascent_root_coeff (i j : S) (hij : i ≠ j) (a : W)
    (ha : a ∈ parabolic cs ({i,j} : Set S))
    (has : cs.length (a*cs.simple i)=cs.length a+1) :
    ∃ x y : ℝ, 0 ≤ x ∧ 0 ≤ y ∧ representation cs a (Pi.single i 1) =
      x • Pi.single i 1 + y • Pi.single j 1 := by
  obtain ⟨u,hu,hr,rfl⟩ := (mem_parabolic_iff_reduced_word cs _ a).mp ha
  have hext : cs.IsReduced (u++[i]) := by
    simpa only [CoxeterSystem.IsReduced,cs.wordProd_append,cs.wordProd_singleton,
      List.length_append,List.length_singleton,hr.eq] using has
  cases u with
  | nil => exact ⟨1,0,by norm_num,by norm_num,by simp⟩
  | cons k u =>
    have hk := hu k (by simp)
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hk
    rcases hk with hki | hkj
    · subst k
      apply root_coeff_of_alt_extension cs i j hij (i::u) i _ hext
      simpa only [List.cons_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add] using
        reduced_pair_cons_eq_alt cs i j (u++[i]) hext (by
          intro k hk
          rcases List.mem_append.mp hk with hk | hk
          · exact hu k (List.mem_cons_of_mem i hk)
          · simp only [List.mem_singleton] at hk
            subst k
            simp)
    · subst k
      obtain ⟨x,y,hx,hy,he⟩ := root_coeff_of_alt_extension cs j i (Ne.symm hij) (j::u) i
        (by
          simpa only [List.cons_append,List.length_append,List.length_singleton,List.length_cons,List.length_nil,Nat.zero_add] using
            reduced_pair_cons_eq_alt cs j i (u++[i]) hext (by
              intro k hk
              rcases List.mem_append.mp hk with hk | hk
              · simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,or_comm] using
                  hu k (List.mem_cons_of_mem j hk)
              · simp only [List.mem_singleton] at hk
                subst k
                simp)) hext
      exact ⟨y,x,hy,hx,he.trans (add_comm _ _)⟩

end HarmonicArtin.Geometric

end OAI
