import Mathlib
import OAI.RingTheory.Multiplicity.CharPModuleLength

namespace OAI

noncomputable section
namespace Lech
open CategoryTheory CategoryTheory.Limits HomologicalComplex Filter
open scoped Topology
universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

 
structure IsShortComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  term_free : ∀ i, Module.Free R (F.X i)
  term_finite : ∀ i, Module.Finite R (F.X i)
  bounded : ∀ i, i < -(dimension R : ℤ) ∨ 0 < i → IsZero (F.X i)
  homology_finite_length : ∀ i, IsFiniteLength R (F.homology i)
  homology_zero_nonzero : ¬ IsZero (F.homology 0)

 

structure IsFiniteHomologyComplex (F : CochainComplex (ModuleCat.{u} R) ℤ) : Prop where
  term_free : ∀ i, Module.Free R (F.X i)
  term_finite : ∀ i, Module.Finite R (F.X i)
  bounded : ∀ i, i < -(dimension R : ℤ) ∨ 0 < i → IsZero (F.X i)
  homology_finite_length : ∀ i, IsFiniteLength R (F.homology i)

omit [IsNoetherianRing R] [IsLocalRing R] in
lemma IsShortComplex.finiteHomology [IsNoetherianRing R] [IsLocalRing R]
    {F : CochainComplex (ModuleCat.{u} R) ℤ}
    (hF : IsShortComplex R F) : IsFiniteHomologyComplex R F :=
  ⟨hF.term_free,hF.term_finite,hF.bounded,hF.homology_finite_length⟩

 
def frobeniusComplex (p : ℕ) [Fact p.Prime] [CharP R p] (n : ℕ)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  ((ModuleCat.extendScalars (iterateFrobenius R p n)).mapHomologicalComplex (.up ℤ)).obj F

 
def shortEuler (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  ∑ i∈Finset.range (dimension R+1),(-1:ℝ)^i*
    ((Module.length R (F.homology (-(i:ℤ)))).toNat : ℝ)

def duttaSequence (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) : ℝ :=
  (p:ℝ)^(-(n*dimension R : ℤ)) * shortEuler R (frobeniusComplex R p n F)

def duttaMultiplicity (p : ℕ) [Fact p.Prime] [CharP R p]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) : ℝ :=
  limUnder atTop (duttaSequence R p F)

 

def DuttaDomainClaim : Prop :=
  ∀ (D : Type u) [CommRing D] [IsNoetherianRing D] [IsLocalRing D] [IsDomain D]
    [IsAdicComplete (IsLocalRing.maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP D p]
    (F : CochainComplex (ModuleCat.{u} D) ℤ), IsShortComplex D F →
      (∀ n i,IsFiniteLength D ((frobeniusComplex D p n F).homology i)) ∧
      Tendsto (duttaSequence D p F) atTop (𝓝 (duttaMultiplicity D p F)) ∧
      multiplicity D ≤ duttaMultiplicity D p F
end Lech

end

end OAI
