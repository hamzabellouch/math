import Mathlib
import OAI.RingTheory.Multiplicity.CyclicDutta
import OAI.RingTheory.Multiplicity.PrimeFiltrationMultiplicity

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter IsLocalRing
open scoped Topology
namespace Lech
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsAlgClosed (ResidueField R)]

lemma dutta_algClosed (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsShortComplex R F) :
    Tendsto (duttaSequence R p F) atTop (𝓝 (duttaMultiplicity R p F)) ∧
      multiplicity R ≤ duttaMultiplicity R p F := by
  classical
  obtain ⟨ps,hps⟩ := PrimeFiltration.factors_of_above
    (PrimeFiltration.exists_above (⊥ : Submodule R R))
  have he (n : ℕ) : duttaSequence R p F n=
      (ps.map (fun P => cyclicDuttaSequence p F P n)).sum := by
    unfold duttaSequence cyclicDuttaSequence
    rw [List.sum_map_mul_left,hps.euler_self _ (frobenius_finiteHomology p F hF.finiteHomology n)]
  have ht := tendsto_list_sum ps (fun P hP => by
    have := hps.isPrime P hP
    exact cyclicDuttaSequence_tendsto p F hF P)
  have ht' : Tendsto (duttaSequence R p F) atTop
      (𝓝 (ps.map (cyclicDuttaContribution p F)).sum) := ht.congr (fun n => (he n).symm)
  have hl : duttaMultiplicity R p F=(ps.map (cyclicDuttaContribution p F)).sum := ht'.limUnder_eq
  rw [hl]
  refine ⟨ht',?_⟩
  rw [hps.multiplicity_self]
  apply List.sum_le_sum
  intro P hP
  have := hps.isPrime P hP
  exact cyclicDuttaContribution_lower p F hF P
end Lech

end

end OAI
