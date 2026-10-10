import Mathlib
import OAI.RingTheory.Multiplicity.ComplexEstimateAllModule
import OAI.RingTheory.Multiplicity.DuttaPerfectionValue
import OAI.RingTheory.Multiplicity.ReductionMultiplicity
import OAI.RingTheory.Multiplicity.ScalarExtensionDepth
import OAI.RingTheory.Multiplicity.ShortRankEuler

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology ENNReal
namespace Lech.CharP
universe u
variable (D : Type u) [CommRing D] [IsDomain D] [IsLocalRing D]
  [IsNoetherianRing D] [IsAdicComplete (maximalIdeal D) D]
  (p : ℕ) [Fact p.Prime] [CharP D p] [PerfectRing (ResidueField D) p]
  [Infinite (ResidueField D)]

 

theorem dutta_minimal_estimate (hd : 0 < dimension D)
    (F : CochainComplex (ModuleCat.{u} D) ℤ) (hF : IsFiniteHomologyComplex D F)
    (hm : IsMinimalComplex F) :
    ∃ (A : ℝ) (c : ℕ),0≤A ∧ ∀ n : ℕ,c < p^n →
      multiplicity D*((p^n-c:ℕ):ℝ)^dimension D*
        ((Module.finrank D (F.X 0):ℝ)-A/((p^n-c:ℕ):ℝ)*
          ∑ i∈Finset.range (dimension D+1),(Module.finrank D (F.X (-(i:ℤ))):ℝ)) ≤
            ((p:ℝ)^n)^dimension D*duttaMultiplicity D p F := by
  classical
  obtain ⟨z,hz,hprim,he,c,hred⟩ := MinimalReduction.exists_minimal_reduction (R:=D)
  obtain ⟨ell,hlim,_,hparam,hK,hpos⟩ := exists_length_with_module_limit D p hd
  obtain ⟨A,hA,H⟩ := complex_estimate_allModule (dimension D) hd
  refine ⟨A,c,hA,?_⟩
  let C := PerfectClosure D p
  let φ := PerfectClosure.of D p
  let Z : Fin (dimension D) → C := fun i => φ (z i)
  let J₀ := Ideal.span (Set.range z)
  let J := Ideal.span (Set.range Z)
  have hmap (a : ℕ) : (parameterIdeal D z a).map φ =
      Ideal.span (Set.range (fun i => Z i^a)) := by
    simp only [parameterIdeal,Ideal.map_span,← Set.range_comp,Function.comp_def,map_pow,Z]
    rfl
  have hJ : J₀.map φ = J := by simpa only [parameterIdeal,pow_one] using hmap 1
  have hepos : 0 ≤ multiplicity D := le_of_lt (he ▸ hpos z hprim)
  have hmu : ell.value (ModuleCat.of C (C ⧸ J)) = ENNReal.ofReal (multiplicity D) := by
    have H := hparam z hprim 1 (by omega)
    have heq : parameterIdeal D z 1 = J₀ := by
      exact congrArg Ideal.span (congrArg Set.range (funext fun i => _root_.pow_one (z i)))
    rw [heq] at H
    change ell.value (ModuleCat.of C (C ⧸ J₀.map φ)) = _ at H
    rw [hJ,he] at H
    simpa only [Nat.cast_one,one_pow,one_mul] using H
  have hpowers (a : ℕ) (ha : 0<a) :
      ell.value (ModuleCat.of C (C ⧸ Ideal.span (Set.range (fun i => Z i^a)))) =
        (a:ℝ≥0∞)^dimension D*ENNReal.ofReal (multiplicity D) := by
    rw [← hmap a]
    rw [hparam z hprim a ha,he]
  have hkoszul (a : ℕ) (ha : 1≤a) (i : ℤ) (hi : i < 0) :
      ell.value ((Koszul.unit (List.ofFn (fun j => Z j^a))).homology i)=0 := by
    have hr : (Koszul.entryIdeal (List.ofFn (fun j => z j^a))).radical = maximalIdeal D := by
      rw [entryIdeal_ofFn]
      exact (Normalization.radical_span_powers z a (by omega)).trans hprim
    have hh := hK (List.ofFn (fun j => z j^a)) (by simp) hr i hi
    simpa only [List.map_ofFn,Function.comp_def,map_pow,Z] using hh
  intro n hn
  let s := p^n-c
  have hs : 0<s := by dsimp [s]; omega
  let K := frobeniusComplex D p n F
  have hKfin : IsFiniteHomologyComplex D K := frobenius_finiteHomology p F hF n
  let G := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj K
  have hfree (i) : Module.Free C (G.X i) := by
    let := hKfin.term_free i
    exact free_extendScalars φ (K.X i)
  have hfinite (i) : Module.Finite C (G.X i) := by
    let := hKfin.term_finite i
    exact finite_extendScalars φ (K.X i)
  have hrank (i : ℤ) : Module.finrank C (G.X i) = Module.finrank D (F.X i) := by
    let := hKfin.term_free i
    let := hKfin.term_finite i
    change Module.finrank C ((ModuleCat.extendScalars φ).obj (K.X i)) = _
    rw [finrank_extendScalars φ (K.X i)]
    let := hF.term_free i
    let := hF.term_finite i
    exact finrank_extendScalars (iterateFrobenius D p n) (F.X i)
  have hb (i : ℤ) (hi : i < -(dimension D:ℤ) ∨ 0 < i) : IsZero (G.X i) :=
    (ModuleCat.extendScalars φ).map_isZero (hKfin.bounded i hi)
  have hac (j) : (((baseChangeFunctor C (Localization.Away (Z j))).mapHomologicalComplex _).obj G).Acyclic :=
    short_extension_acyclicAway φ K hKfin (z j) (hz j)
  have hδ (i : ℤ) : (G.d i (i+1)).hom.range ≤ J^s • (⊤ : Submodule C (G.X (i+1))) := by
    apply extendScalars_range_le φ (K.d i (i+1)) ((maximalIdeal D)^(p^n)) (J^s)
      (frobenius_minimal_depth p F hm n i)
    have hbound : (maximalIdeal D)^(p^n) ≤ J₀ ^ s := by
      have H := hred s
      have hsc : s+c=p^n := by dsimp [s]; omega
      rwa [hsc] at H
    calc
      ((maximalIdeal D)^(p^n)).map φ ≤ (J₀ ^ s).map φ := Ideal.map_mono hbound
      _ = J^s := by rw [Ideal.map_pow,hJ]
  have halt : ∑ i∈Finset.range (dimension D+1),(-1:ℝ)^i*(Module.finrank C (G.X (-(i:ℤ))):ℝ)=0 := by
    simp_rw [hrank]
    exact short_rank_euler_zero hd F hF
  have hh := H Z ell (multiplicity D) hepos hmu hpowers hkoszul G hfree hfinite hb hac s hs hδ halt
  simp_rw [hrank] at hh
  rw [perfection_complex_value D p ell hlim hparam F hF n] at hh
  exact hh
end Lech.CharP

end

end OAI
