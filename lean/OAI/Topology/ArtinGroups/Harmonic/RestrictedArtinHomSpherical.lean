import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft
import OAI.Topology.ArtinGroups.Harmonic.InitialProbe

namespace OAI

namespace HarmonicArtin
open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

theorem restrictedArtinHom_spherical_injective (T:Set S) (hT:IsSpherical M T) :
    Function.Injective (restrictedArtinHom M T) := by
  apply (injective_iff_map_eq_one (restrictedArtinHom M T)).mpr
  intro g hg
  have : Finite (restrictedMatrix M T).Group := restricted_finite M T hT
  obtain ⟨a,b,hfrac⟩:=finiteArtin_positive_left_fraction (restrictedMatrix M T) g
  have he:wordArtin M (a.map Subtype.val)=wordArtin M (b.map Subtype.val):=by
    have hh:=hg
    rw [hfrac,map_mul,map_inv,restrictedArtinHom_word,restrictedArtinHom_word] at hh
    exact inv_mul_eq_one.mp hh
  have hp:∀s:T,(s:S)∈(Set.univ:Set S)→∀L d,
      probePositiveWord M T a (sourceInitialProbe M (K:=ℚ) s L d)=
        probePositiveWord M T b (sourceInitialProbe M (K:=ℚ) s L d):=by
    intro s _ L d
    simp only [probePositiveWord,he]
  obtain ⟨u,v,hu,hv,heq⟩:=positive_equal_probe_fraction M T hT Set.univ a b hp
  have hun:u=[]:=List.eq_nil_iff_forall_not_mem.mpr (by intro s hs;exact hu s hs (Set.mem_univ _))
  have hvn:v=[]:=List.eq_nil_iff_forall_not_mem.mpr (by intro s hs;exact hv s hs (Set.mem_univ _))
  rw [hfrac,heq,hun,hvn]
  simp [wordArtin]

end HarmonicArtin

end OAI
