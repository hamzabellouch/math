import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.PositiveBraidRelations

namespace OAI

namespace HarmonicArtin
open CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma maximal_reduced_monoid_prefix (s:S) (w:List S) :
    ∃ u v:List S, M.toCoxeterSystem.IsReduced u ∧
      wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
      u.length+v.length=(s::w).length ∧ 0<u.length ∧
      ∀ u' v':List S,M.toCoxeterSystem.IsReduced u'→
        wordPositive M (s::w)=wordPositive M u'*wordPositive M v'→
        u'.length+v'.length=(s::w).length→u'.length≤u.length := by
  let P:ℕ→Prop:=fun n=>∃u v:List S,M.toCoxeterSystem.IsReduced u ∧
    wordPositive M (s::w)=wordPositive M u*wordPositive M v ∧
    u.length+v.length=(s::w).length ∧ u.length=n
  have hP:P 1 := by
    refine ⟨[s],w,?_,?_,by simp [Nat.add_comm],rfl⟩
    · change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
      exact M.toCoxeterSystem.length_simple s
    · simp [wordPositive]
  have hb:1≤(s::w).length:=by simp
  obtain ⟨u,v,hu,he,hl,hmax⟩:=Nat.findGreatest_spec hb hP
  refine ⟨u,v,hu,he,hl,?_,?_⟩
  · have hh:=Nat.le_findGreatest hb hP
    omega
  · intro u' v' hu' he' hl'
    rw [hmax]
    exact Nat.le_findGreatest (by omega) ⟨u',v',hu',he',hl',rfl⟩

lemma reduced_monoid_left_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (s::w)) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=positiveGenerator M s*wordPositive M v ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsLeftDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.simple s*cs.wordProd w)=w.length+1
    rw [cs.not_isLeftDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.simple s*cs.wordProd w)
  have hp:cs.wordProd (s::v)=cs.wordProd w := by
    rw [cs.wordProd_cons,←he,cs.simple_mul_simple_cancel_left]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isLeftDescent_iff.mp hd
  have hr:cs.IsReduced (s::v) := by
    change cs.length (cs.wordProd (s::v))=v.length+1
    rw [hp,hw.eq,hl]
  refine ⟨v,hv,?_,hl⟩
  exact wordPositive_eq_of_reduced M w (s::v) hw hr hp.symm

lemma reduced_monoid_right_factor (w:List S) (s:S) (hw:M.toCoxeterSystem.IsReduced w)
    (h:¬M.toCoxeterSystem.IsReduced (w++[s])) :
    ∃v:List S,M.toCoxeterSystem.IsReduced v ∧
      wordPositive M w=wordPositive M v*positiveGenerator M s ∧ v.length+1=w.length := by
  let cs:=M.toCoxeterSystem
  have hd:cs.IsRightDescent (cs.wordProd w) s := by
    by_contra hn
    apply h
    change cs.length (cs.wordProd (w++[s]))=(w++[s]).length
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one,List.length_append,List.length_singleton]
    rw [cs.not_isRightDescent_iff.mp hn,hw.eq]
  obtain ⟨v,hv,he⟩:=cs.exists_isReduced (cs.wordProd w*cs.simple s)
  have hp:cs.wordProd (v++[s])=cs.wordProd w := by
    simp only [cs.wordProd_append,cs.wordProd_cons,cs.wordProd_nil,mul_one]
    rw [←he,mul_assoc,cs.simple_mul_simple_self,mul_one]
  have hl:v.length+1=w.length := by
    rw [←hv.eq,←he,←hw.eq]
    exact cs.isRightDescent_iff.mp hd
  have hr:cs.IsReduced (v++[s]) := by
    change cs.length (cs.wordProd (v++[s]))=(v++[s]).length
    rw [hp,hw.eq,List.length_append,List.length_singleton,hl]
  refine ⟨v,hv,?_,hl⟩
  have heq:=wordPositive_eq_of_reduced M w (v++[s]) hw hr hp.symm
  rw [wordPositive_append] at heq
  simpa only [wordPositive,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] using heq

end HarmonicArtin

end OAI
