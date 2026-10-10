import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusHomologyGrowth

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
namespace Lech.Koszul
universe u
variable {R : Type u} [CommRing R]

lemma entryIdeal_powers_radical (zs : List R) (a : ℕ) (ha : 0 < a) :
    (entryIdeal (zs.map (fun z => z^a))).radical = (entryIdeal zs).radical := by
  apply le_antisymm
  · apply Ideal.radical_mono
    apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    have hm : z∈entryIdeal zs := Ideal.subset_span hz
    exact (entryIdeal zs).pow_mem_of_pow_mem
      (show z^1 ∈ entryIdeal zs by simpa only [pow_one] using hm) ha
  · apply Ideal.radical_le_radical_iff.mpr
    apply Ideal.span_le.mpr
    intro z hz
    exact ⟨a,Ideal.subset_span (List.mem_map.mpr ⟨z,hz,rfl⟩)⟩

lemma sup_entryIdeal_powers_radical (I : Ideal R) (zs : List R) (a : ℕ) (ha : 0<a) :
    (I ⊔ entryIdeal (zs.map (fun z => z^a))).radical = (I ⊔ entryIdeal zs).radical := by
  rw [Ideal.radical_sup I,entryIdeal_powers_radical zs a ha,← Ideal.radical_sup]

def quotient_scalar_zero (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (hx : x∈I) :
    Homotopy (x • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0 :=
  Homotopy.ofEq (by
    ext i : 1
    exact moduleQuotient_annihilated I x hx (F.X i))

lemma quotient_tensor_annihilator (I : Ideal R) (zs : List R)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    I ⊔ entryIdeal zs ≤ Module.annihilator R
      ((tensor zs ((complexQuotient I (.up ℤ)).obj F)).homology i) := by
  apply sup_le
  · intro x hx
    exact scalar_annihilates_homology _ x
      (tensorScalarHomotopy x zs (quotient_scalar_zero I F x hx)) i
  · exact tensor_homology_annihilator zs _ i

lemma finite_moduleQuotient (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite R ((moduleQuotient I).obj M) := by
  change Module.Finite R (M ⧸ I • (⊤ : Submodule R M))
  infer_instance

lemma single_terms_finite (M : ModuleCat.{u} R) [Module.Finite R M] (j k : ℤ) :
    Module.Finite R (((single (ModuleCat R) (.up ℤ) j).obj M).X k) := by
  by_cases hk : k=j
  · subst k
    exact Module.Finite.equiv (singleObjXSelf (.up ℤ) j M).toLinearEquiv.symm
  · have := ModuleCat.isZero_iff_subsingleton.mp (isZero_single_obj_X (.up ℤ) j M k hk)
    infer_instance

lemma quotient_tensor_single_finiteLength [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R) (zs : List R)
    (hI : (I ⊔ entryIdeal zs).radical = IsLocalRing.maximalIdeal R) (j i : ℤ) :
    IsFiniteLength R ((tensor zs ((complexQuotient I (.up ℤ)).obj
      ((single (ModuleCat R) (.up ℤ) j).obj (ModuleCat.of R R)))).homology i) := by
  let F := (single (ModuleCat.{u} R) (.up ℤ) j).obj (ModuleCat.of R R)
  have hfin (k : ℤ) : Module.Finite R (((complexQuotient I (.up ℤ)).obj F).X k) := by
    have : Module.Finite R (F.X k) := single_terms_finite _ j k
    exact finite_moduleQuotient I (F.X k)
  have := tensor_terms_finite zs _ hfin i
  have := finite_cochain_homology (tensor zs ((complexQuotient I (.up ℤ)).obj F)) i
  exact finiteLength_of_primary_annihilator _ hI (quotient_tensor_annihilator I zs F i)
end Lech.Koszul

end

end OAI
