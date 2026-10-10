import Mathlib
import OAI.RingTheory.Multiplicity.FrobeniusHomologyFinite
import OAI.RingTheory.Multiplicity.KoszulFiniteComplexBound

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open scoped TensorProduct
namespace Lech
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

lemma free_extendScalars (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.Free S ((ModuleCat.extendScalars φ).obj M) := by
  let := φ.toAlgebra
  change Module.Free S (S ⊗[R] M)
  infer_instance

lemma finrank_extendScalars [Nontrivial R] [Nontrivial S]
    (φ : R →+* S) (M : ModuleCat.{u} R) [Module.Free R M] :
    Module.finrank S ((ModuleCat.extendScalars φ).obj M) = Module.finrank R M := by
  let := φ.toAlgebra
  change Module.finrank S (S ⊗[R] M) = Module.finrank R M
  exact Module.finrank_baseChange

namespace Koszul
instance moduleQuotient_linear (I : Ideal R) : (moduleQuotient (R:=R) I).Linear R where
  map_smul {M N} f x := by
    ext m
    obtain ⟨m,rfl⟩ := (I • (⊤ : Submodule R M)).mkQ_surjective m
    rfl

def quotient_nullhomotopy (I : Ideal R) (F : CochainComplex (ModuleCat.{u} R) ℤ)
    (x : R) (H : Homotopy (x • 𝟙 F) 0) :
    Homotopy (x • 𝟙 ((complexQuotient I (.up ℤ)).obj F)) 0 := by
  simp only [complexQuotient]
  have h := (moduleQuotient I).mapHomotopy H
  simp only [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_zero] at h
  exact h
end Koszul

 

theorem frobenius_quotient_homology_bound [IsNoetherianRing R] [IsLocalRing R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsFiniteHomologyComplex R F)
    (I : Ideal R) (zs : List R) (hzs : ∀ z∈zs,z∈IsLocalRing.maximalIdeal R) :
    ∃ a : ℕ, 0 < a ∧ ∀ n i,
      Module.length R (((complexQuotient I (.up ℤ)).obj (frobeniusComplex R p n F)).homology i) ≤
        ((p^n)^zs.length) • ∑ k∈Finset.range (dimension R+1),
          Module.finrank R (F.X (-(dimension R : ℤ)+k)) • Module.length R
            ((Koszul.tensor (zs.map (fun z => z^a)) ((complexQuotient I (.up ℤ)).obj
              ((single (ModuleCat R) (.up ℤ) (-(dimension R : ℤ)+k)).obj
                (ModuleCat.of R R)))).homology i) := by
  obtain ⟨a,ha,haF⟩ := shortComplex_uniform_nullhomotopy F hF
  refine ⟨a,ha,fun n i => ?_⟩
  let G := frobeniusComplex R p n F
  have hfree (j : ℤ) : Module.Free R (G.X j) := by
    have := hF.term_free j
    exact free_extendScalars (iterateFrobenius R p n) (F.X j)
  have hfin (j : ℤ) : Module.Finite R (G.X j) := by
    have := hF.term_finite j
    exact finite_extendScalars (iterateFrobenius R p n) (F.X j)
  have hb (j : ℤ) (hj : j < -(dimension R:ℤ) ∨ -(dimension R:ℤ)+(dimension R+1) ≤ j) :
      IsZero (G.X j) :=
    (ModuleCat.extendScalars (iterateFrobenius R p n)).map_isZero
      (hF.bounded j (by omega))
  have H (r : R) (hr : r∈zs.map (fun z => z^a)) :
      Homotopy (r^(p^n) • 𝟙 ((complexQuotient I (.up ℤ)).obj G)) 0 := by
    apply Classical.choice
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hr
    have Hz := (haF (Ideal.pow_mem_pow (hzs z hz) a)).some
    refine ⟨?_⟩
    simpa only [pow_mul] using Koszul.quotient_nullhomotopy I G _
      (frobenius_nullhomotopy p n a F z Hz)
  have hl := Koszul.length_quotient_le_koszul_powers I (zs.map (fun z => z^a)) (p^n)
    G (-(dimension R:ℤ)) (dimension R+1) i hb hfree hfin H
  have hrank (j : ℤ) : Module.finrank R (G.X j) = Module.finrank R (F.X j) := by
    have := hF.term_free j
    exact finrank_extendScalars (iterateFrobenius R p n) (F.X j)
  simpa only [List.length_map,hrank] using hl
end Lech

end

end OAI
