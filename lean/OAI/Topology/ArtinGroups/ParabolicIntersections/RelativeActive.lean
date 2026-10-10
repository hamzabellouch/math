import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeHeight
import OAI.Topology.ArtinGroups.Geometry.SphericalCartanPos2

namespace OAI

/-! Sphericity of all active upper colors in the actual relative filtration. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ)

def relativeActiveSet (Y : Set S) (P : Deligne M) : Set S :=
  {i | i ∈ Y ∧ i ∉ P.val.1 ∧ relativeActive (framedCartan M) U (pointedProfile M f P cutoff) (.inl i)}

theorem relativeActiveSet_spherical (Y : Set S) (P : Deligne M)
    (hPY : P.val.1 ⊆ Y) (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) :
    IsSpherical M (P.val.1 ∪ relativeActiveSet M f U cutoff Y P) := by
  let K := P.val.1 ∪ relativeActiveSet M f U cutoff Y P
  let T : Set (S ⊕ Unit) := Sum.inl '' P.val.1
  let L : Set (S ⊕ Unit) := Sum.inl '' K
  have hL : ((framedCartan M).submatrix ((↑) : L → S ⊕ Unit) Subtype.val).PosDef := by
    apply relative_active_posDef (framedCartan M) (framedCartan_symm M)
      (framedCartan_off M) (fun i => by rw [framedCartan_diag]; norm_num) U
      (pointedProfile M f P cutoff)
      (fun k i => pointedCosetVector_nonneg M f P (cutoff+k) i)
      T (framed_spherical_posDef M P.val.1 P.property.1)
    · intro k i hi
      exact pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,hi⟩
    · rintro i ⟨j,hj,rfl⟩
      exact hYU j (hj.elim (fun h => hPY h) (fun h => h.1))
    · rintro i ⟨j,(hj|hj),rfl⟩
      · exact Or.inl ⟨j,hj,rfl⟩
      · exact Or.inr hj.2.2
  let g : K → L := fun i => ⟨.inl (i:S),⟨i,i.property,rfl⟩⟩
  have hg : Function.Injective g := by
    intro i j h
    exact Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
  apply Geometric.spherical_of_cartan_posDef M K
  convert hL.submatrix hg using 1
  ext i j
  rfl

end HarmonicArtin.ParabolicIntersections

end OAI
