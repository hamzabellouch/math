import OAI.Topology.ArtinGroups.ParabolicIntersections.FoldingSimpleGcd
import OAI.Topology.ArtinGroups.ParabolicIntersections.PositiveHeadProduct

namespace OAI

/-! Greedy heads, and hence left atoms, are preserved by folding. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)
    (Y : Set S) (hY : IsSpherical M Y)
local notation "R" => restrictedMatrix M Y
local notation "N" => unfoldedMatrix M Y
local notation "Φ" => foldedPositiveHom M Y hY
local notation "P" => positiveSimpleLift R

omit [Fintype S] [LinearOrder S] in
private lemma positive_nil : wordPositive R [] = 1 := rfl

omit [Fintype S] [LinearOrder S] in
private lemma positive_cons (i : Y) (w : List Y) :
    wordPositive R (i::w)=positiveGenerator R i*wordPositive R w := rfl

/-- The original and folded positive elements have corresponding greedy heads. -/
theorem folded_positive_head (b : PositiveArtin R) :
    ∃ h : (R).Group,
      PositivePrefix R (P h) b ∧
      (∀ w, PositivePrefix R (P w) b → PositivePrefix R (P w) (P h)) ∧
      PositivePrefix N (Φ (P h)) (Φ b) ∧
      (∀ w, PositivePrefix N (positiveSimpleLift N w) (Φ b) →
        PositivePrefix N (positiveSimpleLift N w) (Φ (P h))) := by
  let : Finite (R).Group := restricted_finite M Y hY
  let : Finite (N).Group := unfolded_finite M Y hY
  let : LinearOrder (Y × FusionLabel (fusionLabelSize M)) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  obtain ⟨z,hz⟩ := exists_longest (R).toCoxeterSystem
  have hzN := unfolded_longest M Y hY z hz
  have cancelR := spherical_positive_cancel_left M Y hY
  have cancelN := finite_positive_cancel_left N
  obtain ⟨word,rfl⟩ := positive_word_surjective R b
  induction word with
  | nil =>
    refine ⟨1,?_,?_,?_,?_⟩
    · simpa only [positiveSimpleLift_one,positive_nil] using positivePrefix_refl R 1
    · intro w hw
      simpa only [positiveSimpleLift_one,positive_nil] using hw
    · simp only [positiveSimpleLift_one,positive_nil,map_one]
      exact positivePrefix_refl N 1
    · intro w hw
      simpa only [positiveSimpleLift_one,positive_nil,map_one] using hw
  | cons i word ih =>
    obtain ⟨h,hh,hhead,hhN,hheadN⟩ := ih
    obtain ⟨g,hgc,hgh,hgreat⟩ := exists_greatest_common_simplePrefix R
      (((R).toCoxeterSystem.simple i)⁻¹*z) h
    obtain ⟨k,hk,hkb,hkhead⟩ := positive_head_product R cancelR z hz
      ((R).toCoxeterSystem.simple i) h g (wordPositive R word) hh hhead hgc hgh hgreat
    have hcN : PositivePrefix N
        (positiveSimpleLift N (unfoldedHom M Y hY g))
        (positiveSimpleLift N ((unfoldedHom M Y hY ((R).toCoxeterSystem.simple i))⁻¹*
          unfoldedHom M Y hY z)) := by
      rw [←map_inv,←map_mul,←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift]
      obtain ⟨r,hr⟩ := hgc
      exact ⟨Φ r,by rw [hr,map_mul]⟩
    have hgN : PositivePrefix N (positiveSimpleLift N (unfoldedHom M Y hY g))
        (positiveSimpleLift N (unfoldedHom M Y hY h)) := by
      rw [←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift]
      obtain ⟨r,hr⟩ := hgh
      exact ⟨Φ r,by rw [hr,map_mul]⟩
    have hgreatN := folded_simple_gcd M Y hY _ _ _ hgc hgh hgreat
    simp only [foldedPositiveHom_simpleLift,map_mul,map_inv] at hgreatN
    obtain ⟨kN,hkN,hkbN,hkheadN⟩ := positive_head_product N cancelN
      (unfoldedHom M Y hY z) hzN
      (unfoldedHom M Y hY ((R).toCoxeterSystem.simple i))
      (unfoldedHom M Y hY h) (unfoldedHom M Y hY g) (Φ (wordPositive R word))
      (by simpa only [foldedPositiveHom_simpleLift] using hhN)
      (by simpa only [foldedPositiveHom_simpleLift] using hheadN) hcN hgN hgreatN
    have heN : positiveSimpleLift N kN=Φ (P k) := by
      rw [hkN,←foldedPositiveHom_simpleLift,←foldedPositiveHom_simpleLift,←map_mul,←hk]
    refine ⟨k,?_,?_,?_,?_⟩
    · simpa only [positiveSimpleLift_simple,positive_cons] using hkb
    · simpa only [positiveSimpleLift_simple,positive_cons] using hkhead
    · rw [←heN]
      simpa only [←foldedPositiveHom_simpleLift,positiveSimpleLift_simple,positive_cons,←map_mul] using hkbN
    · intro w hw
      rw [←heN]
      apply hkheadN
      simpa only [←foldedPositiveHom_simpleLift,positiveSimpleLift_simple,positive_cons,←map_mul] using hw

/-- Every atom dividing an expanded positive word has its entire color as
a left divisor. This is the exact divisibility consequence needed downstream. -/
theorem folded_atom_reflect (b : PositiveArtin R)
    (α : Y × FusionLabel (fusionLabelSize M))
    (hα : PositivePrefix N (positiveGenerator N α) (Φ b)) :
    PositivePrefix R (positiveGenerator R α.1) b := by
  obtain ⟨h,hh,_,_,hhead⟩ := folded_positive_head M Y hY b
  have hp : PositivePrefix N (positiveGenerator N α) (Φ (P h)) := by
    simpa only [positiveSimpleLift_simple,positive_cons] using
      hhead ((N).toCoxeterSystem.simple α) (by simpa only [positiveSimpleLift_simple,positive_cons] using hα)
  exact positivePrefix_trans R ((folded_simple_atom_iff M Y hY h α).mp hp) hh

end HarmonicArtin.ParabolicIntersections

end OAI
