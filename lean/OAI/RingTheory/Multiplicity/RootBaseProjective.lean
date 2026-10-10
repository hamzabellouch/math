import Mathlib
import OAI.RingTheory.Multiplicity.HomogeneousZeroPiece
import OAI.RingTheory.Multiplicity.RootOverlap

namespace OAI

noncomputable section
namespace Lech.ProjectiveScalar
universe u v w
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {M : Type w} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

lemma trans [Module.Projective R S] [Module.Projective S M] : Module.Projective R M := by
  classical
  obtain ⟨i,hi⟩ := (inferInstance : Module.Projective S M).out
  have hp : Module.Projective R (M →₀ S) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp R).symm
  apply Module.Projective.of_split (i.restrictScalars R)
    ((Finsupp.linearCombination S id).restrictScalars R)
  ext x
  exact hi x
end Lech.ProjectiveScalar

namespace Lech.ProjectiveRoot
open HomogeneousLocalization MvPolynomial
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra Homogeneous.awayAddCommGroup

def baseBasisEquiv (s : Finset (Fin (n+1))) : Ring R n s ≃ₗ[R]
    ({e : PartialLaurent.exponents s // PartialLaurent.degree s e=0} →₀ R) :=
  (Homogeneous.zeroPieceEquiv (ProjectiveCoefficientChart.grading R n)
    (product_homogeneous R n s)).trans
    ((PartialLaurent.polynomialTwistEquiv R s 0).trans
      (PartialLaurent.homogeneousEquiv R s 0))

lemma ring_base_free (s : Finset (Fin (n+1))) : Module.Free R (Ring R n s) :=
  Module.Free.of_equiv (baseBasisEquiv R n s).symm

lemma sections_base_projective (s : Finset (Fin (n+1))) (hs : s.Nonempty) (m : Fin n → ℤ) :
    Module.Projective R (Sections R n s hs m) := by
  let := ring_base_free R n s
  obtain ⟨k,hk⟩ := hs
  let : Fact (k ∈ s) := ⟨hk⟩
  let := (Sections_properties R n k s ⟨k,hk⟩ m).2.1
  exact ProjectiveScalar.trans (R:=R) (S:=Ring R n s)
end Lech.ProjectiveRoot

end

end OAI
