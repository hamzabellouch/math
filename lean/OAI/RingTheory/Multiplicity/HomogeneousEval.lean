import Mathlib

namespace OAI

noncomputable section
namespace Lech.HomogeneousEval
open HomogeneousLocalization
universe u v w
variable {A : Type u} {B : Type v} {σ : Type w}
variable [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
variable (G : ℕ → σ) [GradedRing G]
variable (φ : A →+* B) {f g x : A}

 

def evaluate (f : A) (hf : IsUnit (φ f)) : Away G f →+* B :=
  (Localization.awayLift φ f hf).comp
    (algebraMap (Away G f) (Localization.Away f))

lemma evaluate_mk {d : ℕ} (hf : f ∈ G d) (hu : IsUnit (φ f))
    (v : B) (hv : φ f * v = 1) (j : ℕ) (a : A) (ha : a ∈ G (j • d)) :
    evaluate G φ f hu (Away.mk G hf j a ha) = φ a * v ^ j := by
  exact Localization.awayLift_mk φ f a v hv j

 

lemma evaluate_awayMap {e : ℕ} (hg : g ∈ G e) (hx : x = f * g)
    (hf : IsUnit (φ f)) (hxx : IsUnit (φ x)) (a : Away G f) :
    evaluate G φ x hxx (awayMap G hg hx a) = evaluate G φ f hf a := by
  change Localization.awayLift φ x hxx (awayMap G hg hx a).val = _
  rw [val_awayMap]
  have hcomp : (Localization.awayLift φ x hxx).comp
      (Localization.awayLift (algebraMap A (Localization.Away x)) f
        (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩)
          (IsLocalization.Away.algebraMap_isUnit x))) =
      Localization.awayLift φ f hf := by
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, IsLocalization.Away.lift_eq]
  exact DFunLike.congr_fun hcomp a.val

 

lemma awayMap_comp {d e c : ℕ} {h y : A}
    (hf : f ∈ G d) (hg : g ∈ G e) (hh : h ∈ G c)
    (hx : x = f * g) (hy : y = x * h) (hz : y = f * (g * h))
    (a : Away G f) :
    awayMap G hh hy (awayMap G hg hx a) =
      awayMap G (SetLike.mul_mem_graded hg hh) hz a := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf a
  rw [awayMap_mk, awayMap_mk, awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, mul_pow, mul_assoc]

lemma awayMap_one {d : ℕ} (hf : f ∈ G d) (hx : f = f * 1) (a : Away G f) :
    awayMap G (show (1 : A) ∈ G 0 from SetLike.one_mem_graded G) hx a = a := by
  obtain ⟨j,b,hb,rfl⟩ := Away.mk_surjective G hf a
  rw [awayMap_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, one_pow, mul_one]

end Lech.HomogeneousEval

end

end OAI
