import Mathlib
import OAI.Topology.ArtinGroups.Complexes.SummandSecondary

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype A] [DecidableEq V]
variable {I J T : Type*} [Fintype I] [Fintype J] [Fintype T]

noncomputable def pureCoefficientCohomology (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k n v : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k)
    (h : n+v = k-l) : homCohomology Q E F n v ≃ₗ[K] homCycles Q E F n v :=
  Submodule.quotEquivOfEqBot _ (by
    rw [pure_coefficient_boundaries_zero Q E F hE hF h, Submodule.comap_bot]
    exact Submodule.ker_subtype _)

noncomputable def summandSecondaryOnCycles (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    homCycles Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v :=
  (summandSecondary Q E F hE M q d n ι π).restrict fun _ hf =>
    summandSecondary_cycles Q E F hE hF M q d n v ι π hf

noncomputable def summandSecondaryClass (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (q d n v : ℤ)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M) :
    homCycles Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCohomology Q M (F.pureLayer Q hF (d-1)) (n+1) v :=
  ((homBoundaries Q M (F.pureLayer Q hF (d-1)) (n+1) v).comap
    (homCycles Q M (F.pureLayer Q hF (d-1)) (n+1) v).subtype).mkQ.comp
    (summandSecondaryOnCycles Q E F hE hF M q d n v ι π)

lemma summandSecondaryClass_injective [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q) :
    Function.Injective (summandSecondaryClass Q E F hE hF M q d n v ι π) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro f hf
  change Submodule.Quotient.mk (summandSecondaryOnCycles Q E F hE hF M q d n v ι π f) = 0 at hf
  have hb := (Submodule.Quotient.mk_eq_zero _).mp hf
  change f = 0
  apply Subtype.ext
  exact summandSecondary_kernel_zero Q E F hE hF M U q d n v hM hU ι π hret hcap hd hdeg
    f.property hb

noncomputable def cappedSummandInjection [Fintype V] [DecidableEq T]
    (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J)
    (hE : E.IsMinimal Q) (hF : F.IsMinimal Q)
    (M : BasedComplex Q (K := K) T) (U : Set V) (q d n v : ℤ)
    (hM : ∀ i, (M.placement i).level = q) (hU : ∀ i, (M.placement i).color ∈ U)
    (ι : Map Q M (E.pureLayer Q hE q)) (π : Map Q (E.pureLayer Q hE q) M)
    (hret : ι.matrix * π.matrix = projectiveIdentity Q M.placement)
    (hcap : E.CappedOn Q U q) (hd : homDimension Q E F n v = 0)
    (hdeg : n+v = d-q) :
    { f : homCohomology Q M (F.pureLayer Q hF d) n v →ₗ[K]
      homCohomology Q M (F.pureLayer Q hF (d-1)) (n+1) v // Function.Injective f } :=
  ⟨ (summandSecondaryClass Q E F hE hF M q d n v ι π).comp
      (pureCoefficientCohomology Q M (F.pureLayer Q hF d) hM (fun i => i.property) hdeg).toLinearMap,
     (summandSecondaryClass_injective Q E F hE hF M U q d n v hM hU ι π hret hcap hd hdeg).comp
      (pureCoefficientCohomology Q M (F.pureLayer Q hF d) hM (fun i => i.property) hdeg).injective ⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
