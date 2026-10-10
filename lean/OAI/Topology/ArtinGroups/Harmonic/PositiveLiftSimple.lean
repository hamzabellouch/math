import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ReducedExpression
import OAI.Topology.ArtinGroups.Geometry.LongestMulSelf

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma positiveLift_simple (s:S) : positiveLift M (M.toCoxeterSystem.simple s)=generator M s := by
  have h:M.toCoxeterSystem.IsReduced [s]:=by
    change M.toCoxeterSystem.length (M.toCoxeterSystem.simple s)=1
    exact M.toCoxeterSystem.length_simple s
  simpa [wordCoxeter,wordArtin] using positiveLift_word M [s] h

lemma positiveLift_longest_conjugate (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (s t:S) (hst:z*M.toCoxeterSystem.simple s*z=M.toCoxeterSystem.simple t) :
    positiveLift M z*generator M s=generator M t*positiveLift M z := by
  have hzz:=longest_mul_self cs z hz
  have hst':M.toCoxeterSystem.simple t*z=z*M.toCoxeterSystem.simple s := by rw [← hst,mul_assoc,mul_assoc,hzz,mul_one]
  have hr:=all_descents_of_longest cs z hz s
  have hl:=all_left_descents_of_longest cs z hz t
  have hp:positiveLift M z=positiveLift M (z*M.toCoxeterSystem.simple s)*generator M s := by
    have h:=positiveLift_mul M (z*M.toCoxeterSystem.simple s) (M.toCoxeterSystem.simple s) (by
      rw [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,M.toCoxeterSystem.length_simple]; omega)
    simpa only [mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,mul_one,positiveLift_simple] using h
  have hq:positiveLift M z=generator M t*positiveLift M (M.toCoxeterSystem.simple t*z) := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple t) (M.toCoxeterSystem.simple t*z) (by
      rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  calc
    positiveLift M z*generator M s=(generator M t*positiveLift M (z*M.toCoxeterSystem.simple s))*generator M s := by rw [hq,hst']
    _ = generator M t*positiveLift M z := by rw [mul_assoc,← hp]

lemma positiveLift_longest_square_commute_generator (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    Commute (positiveLift M z^2) (generator M s) := by
  obtain ⟨t,hst⟩:=longest_conjugates_simple cs z hz s
  have hts:z*M.toCoxeterSystem.simple t*z=M.toCoxeterSystem.simple s := by
    rw [← hst]
    have hzz:=longest_mul_self cs z hz
    calc z*(z*M.toCoxeterSystem.simple s*z)*z = (z*z)*M.toCoxeterSystem.simple s*(z*z) := by group
         _ = M.toCoxeterSystem.simple s := by rw [hzz,one_mul,mul_one]
  have h₁:=positiveLift_longest_conjugate M z hz s t hst
  have h₂:=positiveLift_longest_conjugate M z hz t s hts
  show positiveLift M z^2 * generator M s=generator M s*positiveLift M z^2
  rw [pow_two,mul_assoc,h₁,← mul_assoc,h₂,mul_assoc]

lemma positiveLift_longest_square_central (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (g:Artin M) :
    Commute (positiveLift M z^2) g := by
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh : Subgroup.closure (Set.range (generator M))=⊤ := PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx => obtain ⟨s,rfl⟩:=hx; exact positiveLift_longest_square_commute_generator M z hz s
  | one => exact Commute.one_right _
  | mul a b ha hb ia ib => exact ia.mul_right ib
  | inv a ha ia => exact ia.inv_right

omit [Fintype S] in
lemma positiveLift_longest_square_positive (z:M.Group) :
    ∃ u:List S,wordArtin M u=positiveLift M z^2 := by
  refine ⟨reducedExpression M z++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two]
  rfl

lemma positiveLift_longest_square_complement (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (s:S) :
    ∃ u:List S,generator M s*wordArtin M u=positiveLift M z^2 := by
  let c:=M.toCoxeterSystem.simple s*z
  have hlen:=all_left_descents_of_longest cs z hz s
  have hp:positiveLift M z=generator M s*positiveLift M c := by
    have h:=positiveLift_mul M (M.toCoxeterSystem.simple s) c (by
      simp only [c]; rw [← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,M.toCoxeterSystem.length_simple]; omega)
    simpa only [c,← mul_assoc,M.toCoxeterSystem.simple_mul_simple_self,one_mul,positiveLift_simple] using h
  refine ⟨reducedExpression M c++reducedExpression M z,?_⟩
  rw [wordArtin_append,pow_two,← mul_assoc]
  change (generator M s*positiveLift M c)*positiveLift M z=_
  rw [← hp]

lemma positive_fraction_longest (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z)
    (g:Artin M) : ∃ n:ℕ,∃ u:List S,g=wordArtin M u*(positiveLift M z^2)^(- (n:ℤ)) := by
  let Ω:Artin M:=positiveLift M z^2
  have hg:g∈Subgroup.closure (Set.range (generator M)) := by
    have hh:Subgroup.closure (Set.range (generator M))=⊤:=PresentedGroup.closure_range_of (braidRelators M)
    rw [hh]; trivial
  change ∃ n:ℕ,∃ u:List S,g=wordArtin M u*Ω^(- (n:ℤ))
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0,[],by simp [wordArtin]⟩
  | mul_left a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    exact ⟨n,s::u,by simp only [wordArtin,List.map_cons,List.prod_cons,mul_assoc]⟩
  | inv_mul_cancel a ha y hy ih =>
    obtain ⟨s,rfl⟩:=ha
    obtain ⟨n,u,rfl⟩:=ih
    obtain ⟨v,hv⟩:=positiveLift_longest_square_complement M z hz s
    have hinv:(generator M s)⁻¹=wordArtin M v*Ω⁻¹ := by
      apply (mul_left_cancel_iff (a:=generator M s)).mp
      rw [← mul_assoc,hv,mul_inv_cancel, mul_inv_cancel]
    refine ⟨n+1,v++u,?_⟩
    rw [hinv,wordArtin_append]
    have hp:Commute Ω⁻¹ (wordArtin M u):=(positiveLift_longest_square_central M z hz _).inv_left
    calc
      wordArtin M v*Ω⁻¹*(wordArtin M u*Ω^(-(n:ℤ))) =
          wordArtin M v*(Ω⁻¹*wordArtin M u)*Ω^(-(n:ℤ)) := by group
      _ = (wordArtin M v*wordArtin M u)*(Ω⁻¹*Ω^(-(n:ℤ))) := by rw [hp.eq]; group
      _ = (wordArtin M v*wordArtin M u)*Ω^(-((n+1:ℕ):ℤ)) := by
        congr 1
        rw [← zpow_neg_one,← zpow_add]
        congr 1
        omega

omit [Fintype S] in
lemma wordArtin_positive_power (v:List S) (n:ℕ) :
    ∃ u:List S,wordArtin M u=wordArtin M v^n := by
  induction n with
  | zero => exact ⟨[],by simp [wordArtin]⟩
  | succ n ih =>
    obtain ⟨u,hu⟩:=ih
    exact ⟨u++v,by rw [wordArtin_append,hu,pow_succ]⟩

theorem finiteArtin_positive_fraction [Finite M.Group] (g:Artin M) :
    ∃ u v:List S,g=wordArtin M u*(wordArtin M v)⁻¹ := by
  obtain ⟨z,hz⟩:=exists_longest M.toCoxeterSystem
  obtain ⟨n,u,hu⟩:=positive_fraction_longest M z hz g
  obtain ⟨v,hv⟩:=positiveLift_longest_square_positive M z
  obtain ⟨v',hv'⟩:=wordArtin_positive_power M v n
  refine ⟨u,v',?_⟩
  rw [hu,hv',hv,zpow_neg,zpow_natCast]

end HarmonicArtin

end OAI
