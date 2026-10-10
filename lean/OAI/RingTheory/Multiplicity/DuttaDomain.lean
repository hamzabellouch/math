import Mathlib
import OAI.RingTheory.Multiplicity.DuttaAlgClosed

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u

lemma isLocalHom_of_map_maximal {R S : Type u} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (φ : R →+* S)
    (hmax : (maximalIdeal R).map φ=maximalIdeal S) : IsLocalHom φ := by
  constructor
  intro x hx
  by_contra hn
  have hm : x ∈ maximalIdeal R := (mem_maximalIdeal x).mpr hn
  have hm' : φ x ∈ maximalIdeal S := hmax ▸ Ideal.mem_map_of_mem φ hm
  exact hm' hx

lemma dutta_complete_charp (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    (∀ n i,IsFiniteLength R ((frobeniusComplex R p n F).homology i)) ∧
      Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
      multiplicity R ≤ duttaMultiplicity R p F := by
  let E := residueExtension R p
  let S := E.S
  have : IsLocalHom (algebraMap R S) := isLocalHom_of_map_maximal _ E.maximal_map
  have : CharP S p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    have h := congrArg (algebraMap R S) (CharP.cast_eq_zero R p)
    simpa only [map_natCast,map_zero] using h)
  let G := (((ModuleCat.extendScalars (algebraMap R S)).mapHomologicalComplex (.up ℤ)).obj F)
  have hG : IsShortComplex S G := shortComplex_baseChange E.maximal_map F hF
  have he : duttaSequence S p G=duttaSequence R p F :=
    funext (duttaSequence_baseChange p E.maximal_map F)
  have hm : duttaMultiplicity S p G=duttaMultiplicity R p F := congrArg (limUnder atTop) he
  obtain ⟨ht,hl⟩ := dutta_algClosed p G hG
  rw [he,hm] at ht
  rw [hm,multiplicity_eq_of_map_maximalIdeal E.maximal_map] at hl
  exact ⟨fun n i => (frobenius_finiteHomology p F hF.finiteHomology n).homology_finite_length i,ht,hl⟩

 
theorem dutta_domain : DuttaDomainClaim.{u} := by
  intro D _ _ _ _ _ p _ _ F hF
  exact dutta_complete_charp D p F hF

end Lech

end

end OAI
