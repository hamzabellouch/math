import Mathlib
import OAI.Topology.ArtinGroups.Realizations.CellDeligne
import OAI.Topology.ArtinGroups.Geometry.LongestMulSelf
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeHom

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)
local notation "cs" => M.toCoxeterSystem

lemma positiveSimpleLift_mul (a b:M.Group)
    (h:M.toCoxeterSystem.length (a*b)=M.toCoxeterSystem.length a+M.toCoxeterSystem.length b) :
    positiveSimpleLift M (a*b)=positiveSimpleLift M a*positiveSimpleLift M b := by
  let u:=reducedExpression M a
  let v:=reducedExpression M b
  have hu:M.toCoxeterSystem.IsReduced u:=reducedExpression_reduced M a
  have hv:M.toCoxeterSystem.IsReduced v:=reducedExpression_reduced M b
  have he:wordCoxeter M (u++v)=a*b:=by
    rw [wordCoxeter_append,wordCoxeter_reducedExpression,wordCoxeter_reducedExpression]
  have hr:M.toCoxeterSystem.IsReduced (u++v):=by
    change M.toCoxeterSystem.length (wordCoxeter M (u++v))=(u++v).length
    rw [he,h,List.length_append,←hu.eq,←hv.eq]
    change M.toCoxeterSystem.length a+M.toCoxeterSystem.length b=M.toCoxeterSystem.length (wordCoxeter M u)+M.toCoxeterSystem.length (wordCoxeter M v)
    rw [wordCoxeter_reducedExpression,wordCoxeter_reducedExpression]
  rw [←he,positiveSimpleLift_word M _ hr,wordPositive_append]
  rfl

lemma positive_simple_factors (a b:PositiveArtin M) (w:M.Group)
    (h:a*b=positiveSimpleLift M w) :
    a=positiveSimpleLift M (positiveToCoxeter M a) ∧
      b=positiveSimpleLift M (positiveToCoxeter M b) := by
  have hd:=congrArg (positiveDegree M) h
  simp only [positiveDegree_mul,positiveDegree_simpleLift] at hd
  have hc:=congrArg (positiveToCoxeter M) h
  simp only [map_mul,positiveToCoxeter_simpleLift] at hc
  have ha:=positiveToCoxeter_length_le M a
  have hb:=positiveToCoxeter_length_le M b
  have hab:=M.toCoxeterSystem.length_mul_le (positiveToCoxeter M a) (positiveToCoxeter M b)
  rw [hc] at hab
  exact ⟨positive_eq_simpleLift_of_degree M a (by omega),
    positive_eq_simpleLift_of_degree M b (by omega)⟩

lemma longest_inverse_eq (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) : z⁻¹=z := by
  have hzz:=longest_mul_self cs z hz
  calc z⁻¹=z⁻¹*(z*z):=by rw [hzz,mul_one]
       _=z:=by group

lemma length_mul_longest (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (w:M.Group) :
    M.toCoxeterSystem.length (w*z)+M.toCoxeterSystem.length w=M.toCoxeterSystem.length z := by
  have h:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) w⁻¹
  have he:(w*z)⁻¹=z*w⁻¹:=by rw [mul_inv_rev,longest_inverse_eq M z hz]
  rw [←he,M.toCoxeterSystem.length_inv,M.toCoxeterSystem.length_inv] at h
  exact h

lemma positiveSimpleLift_left_complement (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (w:M.Group) :
    positiveSimpleLift M w*positiveSimpleLift M (w⁻¹*z)=positiveSimpleLift M z := by
  have hl:=length_mul_longest M z hz w⁻¹
  rw [M.toCoxeterSystem.length_inv] at hl
  have h:=positiveSimpleLift_mul M w (w⁻¹*z) (by rw [mul_inv_cancel_left];omega)
  simpa only [mul_inv_cancel_left] using h.symm

lemma positiveSimpleLift_right_complement (z:M.Group) (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (w:M.Group) :
    positiveSimpleLift M (z*w⁻¹)*positiveSimpleLift M w=positiveSimpleLift M z := by
  have hl:=length_mul_of_all_descents cs z (all_descents_of_longest cs z hz) w⁻¹
  rw [M.toCoxeterSystem.length_inv] at hl
  have h:=positiveSimpleLift_mul M (z*w⁻¹) w (by rw [inv_mul_cancel_right];omega)
  simpa only [inv_mul_cancel_right] using h.symm

theorem positive_fundamental_left_divisor_iff (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (a:PositiveArtin M) :
    (∃b,a*b=positiveSimpleLift M z) ↔ ∃w:M.Group,a=positiveSimpleLift M w := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨positiveToCoxeter M a,(positive_simple_factors M a b z hb).1⟩
  · rintro ⟨w,rfl⟩
    exact ⟨positiveSimpleLift M (w⁻¹*z),positiveSimpleLift_left_complement M z hz w⟩

theorem positive_fundamental_right_divisor_iff (z:M.Group)
    (hz:∀w,M.toCoxeterSystem.length w≤M.toCoxeterSystem.length z) (a:PositiveArtin M) :
    (∃b,b*a=positiveSimpleLift M z) ↔ ∃w:M.Group,a=positiveSimpleLift M w := by
  constructor
  · rintro ⟨b,hb⟩
    exact ⟨positiveToCoxeter M a,(positive_simple_factors M b a z hb).2⟩
  · rintro ⟨w,rfl⟩
    exact ⟨positiveSimpleLift M (z*w⁻¹),positiveSimpleLift_right_complement M z hz w⟩

end HarmonicArtin

end OAI
