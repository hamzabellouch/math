import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusScalarError
import OAI.RingTheory.Multiplicity.ScalarExtensionComplexCompare

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
namespace Lech.FrobeniusIntermediate
universe u
variable {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
  (p : ℕ) [Fact p.Prime] [CharP D p]
  (B : Subring D) [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom B.subtype]
  [Module.Finite B D]

def frobeniusComplex_order_iso (e : ℕ) (he : ∀ x : D,x^(p^e) ∈ B)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (n : ℕ) :
    (((ModuleCat.extendScalars B.subtype).mapHomologicalComplex _).obj
      (frobeniusComplex B p n
        (((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex _).obj F))) ≅
      frobeniusComplex D p (e+n) F := by
  let f := powerMap p B e he
  let g := iterateFrobenius B p n
  have hx : B.subtype.comp (g.comp f) = iterateFrobenius D p (e+n) := by
    ext x
    change (x^(p^e))^(p^n) = x^(p^(e+n))
    rw [← pow_mul,← pow_add]
  let u := ((ModuleCat.extendScalars B.subtype).mapHomologicalComplex (.up ℤ)).mapIso
    (((NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (.up ℤ)).app F).symm)
  let v := ((NatIso.mapHomologicalComplex
    (ModuleCat.extendScalarsComp (g.comp f) B.subtype) (.up ℤ)).app F).symm
  have q := u ≪≫ v
  rw [hx] at q
  exact q

 

theorem frobenius_homology_order_transfer
    (e : ℕ) (he : ∀ x : D,x^(p^e) ∈ B)
    (hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField B) (IsLocalRing.ResidueField D)))
    (hd : dimension B = dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (i : ℤ)
    (hlim : Tendsto (fun n : ℕ => ((Module.length B ((frobeniusComplex B p n
      (((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex _).obj F)).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension B)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => ((Module.length D ((frobeniusComplex D p n F).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) atTop (𝓝 0) := by
  have hp0 : 0 < (p:ℝ) := by exact_mod_cast (Nat.Prime.pos (Fact.out : p.Prime))
  let G := ((ModuleCat.extendScalars (powerMap p B e he)).mapHomologicalComplex (.up ℤ)).obj F
  obtain ⟨r,g,hg,hbound⟩ := exists_scalar_extension_homology_bound (R:=B) (S:=D) hres
  have hgD : (g:D) ≠ 0 := fun h => hg (Subtype.val_injective h)
  let a : D := g
  have hb (n : ℕ) : Module.length D ((frobeniusComplex D p (e+n) F).homology i) ≤
      r • Module.length B ((frobeniusComplex B p n G).homology i) +
      Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
        (frobeniusComplex D p (e+n) F)).homology i) := by
    let U := ((ModuleCat.extendScalars B.subtype).mapHomologicalComplex (.up ℤ)).obj
      (frobeniusComplex B p n G)
    let iso := frobeniusComplex_order_iso p B e he F n
    have hfree (j : ℤ) : Module.Free D ((frobeniusComplex D p (e+n) F).X j) := by
      have := hF.term_free j
      exact free_extendScalars (iterateFrobenius D p (e+n)) (F.X j)
    have hgi (j : ℤ) : Function.Injective (fun x : U.X j => (algebraMap B D g) • x) := by
      let q := ((eval (ModuleCat D) (.up ℤ) j).mapIso iso).toLinearEquiv
      have := hfree j
      intro x y hxy
      apply q.injective
      apply free_scalar_injective ((frobeniusComplex D p (e+n) F).X j) a hgD
      exact (q.map_smul a x).symm.trans ((congrArg q hxy).trans (q.map_smul a y))
    have hlen : Module.length D (U.homology i) = Module.length D ((frobeniusComplex D p (e+n) F).homology i) :=
      (homologyMapIso iso i).toLinearEquiv.length_eq
    have hh := hbound (frobeniusComplex B p n G) i hgi (by
      change Module.length D (U.homology i) ≠ ⊤
      rw [hlen]
      exact Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p F hF (e+n) i))
    change Module.length D (U.homology i) ≤ _ at hh
    rw [hlen] at hh
    have hq : Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj U).homology i) =
        Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj (frobeniusComplex D p (e+n) F)).homology i) :=
      (homologyMapIso ((complexQuotient (Ideal.span {a}) (.up ℤ)).mapIso iso) i).toLinearEquiv.length_eq
    change Module.length D ((frobeniusComplex D p (e+n) F).homology i) ≤
      r • Module.length B ((frobeniusComplex B p n G).homology i) +
      Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj U).homology i) at hh
    rw [hq] at hh
    exact hh
  have hlim' : Tendsto (fun n : ℕ => (r:ℝ) *
      (((Module.length B ((frobeniusComplex B p n G).homology i)).toNat : ℝ) /
        ((p:ℝ)^n)^(dimension D))) atTop (𝓝 0) := by
    simpa only [hd,mul_zero] using hlim.const_mul (r:ℝ)
  have herr := tendsto_frobenius_shift_zero p (dimension D) e (Nat.Prime.pos Fact.out)
    (fun n => ((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
      (frobeniusComplex D p n F)).homology i)).toNat : ℝ))
    (frobenius_scalar_quotient_homology_tendsto_zero p F hF a hgD i)
  apply tendsto_frobenius_unshift_zero p (dimension D) e (Nat.Prime.pos Fact.out)
  apply squeeze_zero (g := fun n : ℕ =>
    (r:ℝ) * (((Module.length B ((frobeniusComplex B p n G).homology i)).toNat : ℝ) /
      ((p:ℝ)^n)^(dimension D)) +
    (((Module.length D (((complexQuotient (Ideal.span {a}) (.up ℤ)).obj
      (frobeniusComplex D p (e+n) F)).homology i)).toNat : ℝ) / ((p:ℝ)^n)^(dimension D)))
  · intro n; positivity
  · intro n
    rw [← mul_div_assoc,← add_div]
    apply (div_le_div_iff_of_pos_right (by positivity)).mpr
    have hG : IsFiniteHomologyComplex B G :=
      finiteHomology_extendScalars (powerMap p B e he) hd
        (map_radical_primary p B e he (IsLocalRing.maximalIdeal D) (Ideal.IsPrime.radical inferInstance)) F hF
    have hfinB := Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p G hG n i)
    have hfinQ := Module.length_ne_top_iff.mpr (frobenius_quotient_homology_finiteLength p F hF (Ideal.span {a}) (e+n) i)
    have hfinD := Module.length_ne_top_iff.mpr (frobenius_shortComplex_homology_finiteLength p F hF (e+n) i)
    have hh := hb n
    rw [← ENat.natCast_toNat hfinD,← ENat.natCast_toNat hfinB,← ENat.natCast_toNat hfinQ,nsmul_eq_mul] at hh
    exact_mod_cast hh

  · simpa only [add_zero] using hlim'.add herr
end Lech.FrobeniusIntermediate

end

end OAI
