import Mathlib
import OAI.Topology.ArtinGroups.Complexes.InitialHomSpaceNegative
import OAI.Topology.ArtinGroups.Complexes.PureCoefficientCohomology

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
variable {V A : Type u} {K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

noncomputable def frameCappedInjection (hn : ∀ a, Q.source a ≠ Q.target a)
    (C : CoxeterMatrix V) (hC : UnfoldedPresentation Q C) (x : Artin C) (α β : V)
    {T : Type*} [Fintype T] [DecidableEq T]
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q
      (frameModel_minimal Q hn C hC x α) q))
    (π : Map Q ((frameModel Q (K := K) hn C hC x α).complex.pureLayer Q
      (frameModel_minimal Q hn C hC x α) q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : (frameModel Q (K := K) hn C hC x α).complex.CappedOn Q U q)
    (hd : d < q) (hdeg : n+v = d-q) :
    {f : homCohomology Q M ((frameModel Q (K := K) hn C hC x β).complex.pureLayer Q
        (frameModel_minimal Q hn C hC x β) d) n v →ₗ[K]
      homCohomology Q M ((frameModel Q (K := K) hn C hC x β).complex.pureLayer Q
        (frameModel_minimal Q hn C hC x β) (d-1)) (n+1) v // Function.Injective f} :=
  cappedSummandInjection Q (frameModel Q (K := K) hn C hC x α).complex
    (frameModel Q (K := K) hn C hC x β).complex
    (frameModel_minimal Q hn C hC x α) (frameModel_minimal Q hn C hC x β)
    M U q d n v hM hU ι π hret hcap
    (frameModel_negative_pair_homDimension Q hn C hC x α β n v (by omega)) hdeg

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
