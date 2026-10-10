import Mathlib
import OAI.RingTheory.Multiplicity.CharPModuleLength

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped ENNReal
namespace Lech
universe u
variable {C : Type u} [CommRing C]
lemma AllModuleLength.finite_value_of_annihilator (ell : AllModuleLength C)
    (M : ModuleCat.{u} C) [Module.Finite C M] (J : Ideal C)
    (hJ : J ≤ Module.annihilator C M)
    (hfin : ell.value (ModuleCat.of C (C ⧸ J)) ≠ ⊤) : ell.value M ≠ ⊤ := by
  obtain ⟨n,v,hv⟩ := Module.Finite.exists_fin (R:=C) (M:=M)
  have hb := ResidueGenerators.value_le hJ (ell.torsionLength J) v hv
  apply ne_top_of_le_ne_top _ hb
  rw [nsmul_eq_mul]
  exact ENNReal.mul_ne_top (by simp) hfin
end Lech
namespace Lech.CharP
open IsLocalRing
universe u
variable (D : Type u) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
lemma normalized_perfection_module_finite (ell : AllModuleLength (PerfectClosure D p))
    (hparam : ∀ (z : Fin (dimension D) → D),
      (Ideal.span (Set.range z)).radical = maximalIdeal D → ∀ a : ℕ,0<a →
      ell.value (ModuleCat.of (PerfectClosure D p) ((PerfectClosure D p) ⧸
        (parameterIdeal D z a).map (PerfectClosure.of D p))) =
        (a:ℝ≥0∞)^(dimension D) * ENNReal.ofReal (Primary.multiplicity (Ideal.span (Set.range z))))
    (M : ModuleCat.{u} D) (hM : IsFiniteLength D M) :
    ell.value ((ModuleCat.extendScalars (PerfectClosure.of D p)).obj M) ≠ ⊤ := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hM).1
  obtain ⟨n,z,hz,hzprim,hd⟩ := Lech.Normalization.exists_parameters D
  have hn : n = dimension D := by
    have hh := dimension_cast D
    rw [hd] at hh
    exact_mod_cast hh.symm
  subst n
  obtain ⟨H,hH,hHM⟩ := finiteLength_primary_annihilator hM
  obtain ⟨b,hb⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (show maximalIdeal D ≤ H.radical by rw [hH]) (maximalIdeal D).fg_of_isNoetherianRing
  have hparamH : parameterIdeal D z (b+1) ≤ H := by
    apply Ideal.span_le.mpr
    rintro x ⟨j,rfl⟩
    exact hb ((Ideal.pow_le_pow_right (Nat.le_succ b)) (Ideal.pow_mem_pow (hz j) (b+1)))
  have := finite_extendScalars (PerfectClosure.of D p) M
  apply AllModuleLength.finite_value_of_annihilator ell _
    ((parameterIdeal D z (b+1)).map (PerfectClosure.of D p))
    (extendScalars_annihilator (PerfectClosure.of D p) M _ (hparamH.trans hHM))
  rw [hparam z hzprim (b+1) (by omega)]
  exact ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top
end Lech.CharP

end

end OAI
