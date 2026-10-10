import Mathlib
import OAI.RingTheory.Multiplicity.IdealQuotientFunctor
import OAI.RingTheory.Multiplicity.ModuleComplexQuotient

namespace OAI

noncomputable section
namespace Lech.CartierQuotient
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)
  {ι : Type*} {c : ComplexShape ι}
  {K L : HomologicalComplex (ModuleCat.{u} R) c} (f : K ⟶ L)
  (hr : ∀ q,(f.f q).hom.range=I • (⊤ : Submodule R (L.X q)))

abbrev quotient (J : Ideal R) (K : HomologicalComplex (ModuleCat.{u} R) c) :=
  ((TensorIdeal.quotientFunctor J).mapHomologicalComplex c).obj K

include hr in
lemma map_power (N : ℕ) (q : ι) :
    (I^N • (⊤ : Submodule R (K.X q))).map (f.f q).hom=
      I^(N+1) • (⊤ : Submodule R (L.X q)) := by
  rw [Submodule.map_smul'',Submodule.map_top,hr,pow_succ,Submodule.mul_smul]

def step (N : ℕ) : quotient (I^N) K ⟶ quotient (I^(N+1)) L where
  f q := ModuleCat.ofHom ((I^N • (⊤ : Submodule R (K.X q))).mapQ
    (I^(N+1) • (⊤ : Submodule R (L.X q))) (f.f q).hom
      (Submodule.map_le_iff_le_comap.mp (map_power I f hr N q).le))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact congrArg (fun g : K.X p ⟶ L.X q => Submodule.Quotient.mk (g.hom x)) (f.comm p q)

 
def reduction (N : ℕ) : quotient (I^(N+1)) L ⟶ quotient I L where
  f q := ModuleCat.ofHom ((I^(N+1) • (⊤ : Submodule R (L.X q))).mapQ
    (I • (⊤ : Submodule R (L.X q))) LinearMap.id (by
      simpa only [Submodule.comap_id] using
        (Submodule.smul_mono_left (show I^(N+1)≤I from by simpa only [pow_one] using (Ideal.pow_le_pow_right (I:=I) (show 1≤N+1 by omega))))))
  comm' p q hpq := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => rfl

lemma step_reduction (N : ℕ) : step I f hr N ≫ reduction (L:=L) I N=0 := by
  apply Hom.ext
  funext q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [←hr q]
      exact LinearMap.mem_range_self _ _

def shortComplex (N : ℕ) : ShortComplex (HomologicalComplex (ModuleCat.{u} R) c) :=
  ShortComplex.mk (step I f hr N) (reduction I N) (step_reduction I f hr N)

lemma shortComplex_exact (hi : ∀ q,Function.Injective (f.f q).hom) (N : ℕ) :
    (shortComplex I f hr N).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro q
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
        change Submodule.Quotient.mk y=0 at hy
        have hm := (Submodule.Quotient.mk_eq_zero _).mp hy
        rw [←hr q] at hm
        obtain ⟨x,rfl⟩ := hm
        exact ⟨Submodule.Quotient.mk x,rfl⟩
  · apply (ModuleCat.mono_iff_injective _).mpr
    apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
        change Submodule.Quotient.mk ((f.f q).hom x)=0 at hx
        have hm := (Submodule.Quotient.mk_eq_zero _).mp hx
        rw [←map_power I f hr N q] at hm
        obtain ⟨y,hy,he⟩ := hm
        have heq := hi q he
        subst x
        exact (Submodule.Quotient.mk_eq_zero _).mpr hy
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x => exact ⟨Submodule.Quotient.mk x,rfl⟩
end Lech.CartierQuotient

end

end OAI
