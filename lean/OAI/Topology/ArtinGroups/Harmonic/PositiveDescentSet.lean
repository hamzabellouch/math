import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.PositiveReverseHom
import OAI.Topology.ArtinGroups.Coxeter.ParabolicLongest

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
variable (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)

lemma positiveReverse_simpleLift (w:M.Group) :
    positiveReverse M z hz (positiveSimpleLift M w)=positiveSimpleLift M w⁻¹ := by
  rw [positiveSimpleLift,positiveReverse_word]
  have hr:=(reducedExpression_reduced M w).reverse
  have he:wordCoxeter M (reducedExpression M w).reverse=w⁻¹:=by
    change M.toCoxeterSystem.wordProd (reducedExpression M w).reverse=w⁻¹
    rw [M.toCoxeterSystem.wordProd_reverse]
    change (wordCoxeter M (reducedExpression M w))⁻¹=_
    rw [wordCoxeter_reducedExpression]
  simpa only [he] using (positiveSimpleLift_word M _ hr).symm

def PositiveDescentSet (a:PositiveArtin M) : Set S :=
  {s | PositiveSuffix M (positiveGenerator M s) a}

include z hz in
lemma positiveDescentSet_nonempty {a:PositiveArtin M} (ha:a≠1) :
    (PositiveDescentSet M a).Nonempty := by
  have hra:positiveReverse M z hz a≠1:=by
    intro he
    have h:=congrArg (positiveReverse M z hz) he
    simp only [positiveReverse_involutive,positiveReverse_one] at h
    exact ha h
  obtain ⟨s,hs⟩:=exists_positive_first M hra
  refine ⟨s,?_⟩
  apply (positiveReverse_prefix_iff M z hz _ _).mp
  simpa only [positiveReverse_generator] using hs

include z hz in

theorem positive_descent_fundamental
    (cancel:∀a b c:PositiveArtin M,a*b=a*c→b=c) (a:PositiveArtin M) :
    IsSpherical M (PositiveDescentSet M a) ∧
      ∃q:M.Group,IsParabolicLongest M (PositiveDescentSet M a) q ∧
        PositiveSuffix M (positiveSimpleLift M q) a := by
  obtain ⟨h,hha,hh⟩:=positive_greedy_head M cancel z hz (positiveReverse M z hz a)
  have hD:∀s∈PositiveDescentSet M a,
      M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*h)<M.toCoxeterSystem.length h:=by
    intro s hs
    have hs':PositivePrefix M (positiveSimpleLift M (M.toCoxeterSystem.simple s)) (positiveReverse M z hz a):=by
      have ht:=(positiveReverse_prefix_iff M z hz (positiveGenerator M s) a).mpr hs
      simpa only [positiveReverse_generator,positiveSimpleLift_simple] using ht
    have hp:=(positivePrefix_simple_iff M _ _).mp (hh _ hs')
    have hl:=(weakPrefix_simple_iff M.toCoxeterSystem s h).mp hp
    omega
  refine ⟨spherical_of_left_descents M _ h hD,?_⟩
  obtain ⟨q,hq,hpref⟩:=positive_longest_descent_prefix M _ h hD
  let Q:=restrictionHom M (PositiveDescentSet M a) q
  have hQ:IsParabolicLongest M (PositiveDescentSet M a) Q:=by
    refine ⟨Geometric.restrictionHom_mem_parabolic M _ q,?_⟩
    intro r hr
    have hm:r∈(restrictionHom M (PositiveDescentSet M a)).range:=by rw [restrictionHom_range_eq];exact hr
    obtain ⟨w,rfl⟩:=hm
    simpa only [Q,restriction_length] using hq w
  refine ⟨Q,hQ,?_⟩
  apply (positiveReverse_prefix_iff M z hz _ _).mp
  rw [positiveReverse_simpleLift,parabolic_longest_inverse M _ Q hQ]
  exact positivePrefix_trans M hpref hha

lemma type_subset_positiveDescentSet (T:Set S) (q:M.Group) (hq:IsParabolicLongest M T q)
    (a:PositiveArtin M) : T⊆PositiveDescentSet M (a*positiveSimpleLift M q) := by
  intro s hs
  have hmem: M.toCoxeterSystem.simple s∈coxeterParabolic M T:=Subgroup.subset_closure ⟨s,hs,rfl⟩
  have hl:=parabolic_longest_length_mul M T q hq (M.toCoxeterSystem.simple s) hmem
  have he:(q*M.toCoxeterSystem.simple s)*M.toCoxeterSystem.simple s=q:=by rw [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one]
  have hp:positiveSimpleLift M q=positiveSimpleLift M (q*M.toCoxeterSystem.simple s)*positiveGenerator M s:=by
    have h:=positiveSimpleLift_mul M (q*M.toCoxeterSystem.simple s) (M.toCoxeterSystem.simple s)
      (by rw [he];exact hl.symm)
    simpa only [he,positiveSimpleLift_simple] using h
  exact ⟨a*positiveSimpleLift M (q*M.toCoxeterSystem.simple s),by rw [hp,mul_assoc]⟩

end HarmonicArtin

end OAI
