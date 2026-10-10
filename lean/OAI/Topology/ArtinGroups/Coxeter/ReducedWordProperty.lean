import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.AltListPairDescent

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] [Fintype B] [DecidableEq B]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

theorem reduced_word_property {N : Type*} [Monoid N] (f : B → N)
    (hbraid : ∀ i j, ((altList i j (M i j)).map f).prod =
      ((altList j i (M i j)).map f).prod)
    (u v : List B) (hu : cs.IsReduced u) (hv : cs.IsReduced v)
    (he : cs.wordProd u = cs.wordProd v) : (u.map f).prod = (v.map f).prod := by
  suffices hall : ∀ n (u v : List B), u.length=n → cs.IsReduced u → cs.IsReduced v →
      cs.wordProd u=cs.wordProd v → (u.map f).prod=(v.map f).prod by
    exact hall u.length u v rfl hu hv he
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u v hlen hu hv he
    cases u with
    | nil =>
      have hv0 : v.length=0 := by rw [← hv.eq,← he]; simp
      have hvnil := List.eq_nil_of_length_eq_zero hv0
      simp [hvnil]
    | cons i u =>
      cases v with
      | nil =>
        have hu0 : (i::u).length=0 := by rw [← hu.eq,he]; simp
        simp at hu0
      | cons j v =>
        have hur : cs.IsReduced u := by simpa only [List.drop_succ_cons,List.drop_zero] using hu.drop 1
        have hvr : cs.IsReduced v := by simpa only [List.drop_succ_cons,List.drop_zero] using hv.drop 1
        have hsmall : u.length<n := by simp only [List.length_cons] at hlen; omega
        have hvlen : v.length=u.length := by
          have hl := congrArg cs.length he
          rw [hu.eq,hv.eq] at hl
          simp only [List.length_cons] at hl
          omega
        by_cases hij : i=j
        · subst j
          have htail : cs.wordProd u=cs.wordProd v := by
            simpa only [cs.wordProd_cons,mul_left_cancel_iff] using he
          simp only [List.map_cons,List.prod_cons]
          rw [ih u.length hsmall u v rfl hur hvr htail]
        · let w := cs.wordProd (i::u)
          have hdi : cs.length (cs.simple i*w)<cs.length w := by
            change cs.length (cs.simple i*cs.wordProd (i::u)) < cs.length (cs.wordProd (i::u))
            rw [hu.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hur.eq,List.length_cons]
            omega
          have hdj : cs.length (cs.simple j*w)<cs.length w := by
            change cs.length (cs.simple j*cs.wordProd (i::u)) < cs.length (cs.wordProd (i::u))
            rw [he,hv.eq,cs.wordProd_cons,cs.simple_mul_simple_cancel_left,hvr.eq,List.length_cons]
            omega
          obtain ⟨r,hm,hl,hip,hjp⟩ := double_descent_prefix cs i j hij w hdi hdj
          obtain ⟨c,hcr,hcp⟩ := cs.exists_isReduced r
          have hpi : cs.wordProd (altList i j (M i j)++c)=w := by
            rw [cs.wordProd_append,← hcp]
            exact hip.symm
          have hpj : cs.wordProd (altList j i (M i j)++c)=w := by
            rw [cs.wordProd_append,← hcp]
            exact hjp.symm
          have hri : cs.IsReduced (altList i j (M i j)++c) := by
            change cs.length (cs.wordProd _)=_
            rw [hpi,hl,List.length_append,length_altList,← hcr.eq,← hcp]
          have hrj : cs.IsReduced (altList j i (M i j)++c) := by
            change cs.length (cs.wordProd _)=_
            rw [hpj,hl,List.length_append,length_altList,← hcr.eq,← hcp]
          obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
          have hti : cs.IsReduced (altList j i k++c) := by
            rw [hk,altList_succ,List.cons_append] at hri
            simpa only [List.drop_succ_cons,List.drop_zero] using hri.drop 1
          have htj : cs.IsReduced (altList i j k++c) := by
            rw [hk,altList_succ,List.cons_append] at hrj
            simpa only [List.drop_succ_cons,List.drop_zero] using hrj.drop 1
          have hei : cs.wordProd u=cs.wordProd (altList j i k++c) := by
            apply mul_left_cancel (a:=cs.simple i)
            simpa only [w,hk,altList_succ,List.cons_append,cs.wordProd_cons] using hpi.symm
          have hej : cs.wordProd v=cs.wordProd (altList i j k++c) := by
            apply mul_left_cancel (a:=cs.simple j)
            have hh := he.symm.trans hpj.symm
            simpa only [hk,altList_succ,List.cons_append,cs.wordProd_cons] using hh
          have hevi := ih u.length hsmall u (altList j i k++c) rfl hur hti hei
          have hevj := ih v.length (by omega) v (altList i j k++c) rfl hvr htj hej
          calc
            ((i::u).map f).prod = ((altList i j (M i j)++c).map f).prod := by
              simp only [hk,altList_succ,List.cons_append,List.map_cons,List.prod_cons,hevi]
            _ = ((altList j i (M i j)++c).map f).prod := by
              simp only [List.map_append,List.prod_append]
              rw [hbraid i j]
            _ = ((j::v).map f).prod := by
              simp only [hk,altList_succ,List.cons_append,List.map_cons,List.prod_cons,hevj]

end HarmonicArtin.CoxeterExchange

end OAI
