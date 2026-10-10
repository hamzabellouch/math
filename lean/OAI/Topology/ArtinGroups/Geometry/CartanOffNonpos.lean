import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.HarmonicExtension
import OAI.Topology.ArtinGroups.Geometry.StrictChamber

namespace OAI

namespace HarmonicArtin.Geometric
open Matrix
open scoped Matrix BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S W:Type*} [Fintype S] [DecidableEq S] [Group W] [Fintype W]
  {M:CoxeterMatrix S} (cs:CoxeterSystem M W)

omit [Fintype S] in
lemma cartan_off_nonpos (M:CoxeterMatrix S) (i j:S) (h:i≠j) : cartan M i j ≤ 0 := by
  simpa [cartan,HarmonicArtin.framedCartan] using
    HarmonicArtin.framedCartan_off M (.inl i) (.inl j) (by simpa using h)

include cs in

theorem exists_positive_chamber : ∃ p:S → ℝ,(∀ i,0 < p i) ∧ ∀ i,(cartan M *ᵥ p) i=1 := by
  obtain ⟨p,hp⟩:=exists_strict_chamber cs
  have hn : ∀ i,0 ≤ p i := HarmonicArtin.harmonic_minimum_principle (cartan M)
    (cartan_posDef cs) (cartan_off_nonpos M) p (fun i=>by rw [hp]; norm_num)
  refine ⟨p,?_,hp⟩
  intro i
  by_contra hi
  have hz : p i=0 := le_antisymm (le_of_not_gt hi) (hn i)
  have hh : (cartan M *ᵥ p) i ≤ 0 := by
    apply Finset.sum_nonpos
    intro j _
    by_cases hij:i=j
    · subst j
      simp [hz]
    · exact mul_nonpos_of_nonpos_of_nonneg (cartan_off_nonpos M i j hij) (hn j)
  rw [hp i] at hh
  norm_num at hh

end HarmonicArtin.Geometric

end OAI
