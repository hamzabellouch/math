import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Characteristic
import OAI.Topology.ArtinGroups.Realizations.LiftedWeightStar

namespace OAI

namespace HarmonicArtin
open Topology Set CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S] (M : CoxeterMatrix S)

lemma sourceCharacteristic_saturated_interior (T : SphericalType M)
    {x y : SourceModelCell M T}
    (hx : x.val ∈ interior (permutahedron (restrictedMatrix M T.val)))
    (he : sourceCharacteristic M T x=sourceCharacteristic M T y) :
    y.val ∈ interior (permutahedron (restrictedMatrix M T.val)) := by
  have hd := congrArg (sourceSalvettiHomeomorph M) he
  rw [sourceCharacteristic_deck M (1,T),sourceCharacteristic_deck M (1,T)] at hd
  obtain ⟨g,hg⟩ := (salvettiDeckProjection_quotientCovering M).apply_eq_iff_mem_orbit.mp hd
  have hm := congrArg weightMax hg
  rw [liftedWeights_max_smul,(sourceCellMap_interior_iff M (1,T) x).mp hx] at hm
  have ht : (weightMax (sourceCellMap M (1,T) y)).2=T :=
    congrArg (fun c : LiftedCell M => c.2) hm
  apply (sourceCellMap_interior_iff M (1,T) y).mpr
  exact lifted_eq_of_le_type_eq M
    (sourceCellMap_support M (1,T) y _ (weightMax_mem _)) (congrArg Subtype.val ht)

lemma sourceCharacteristic_preimage_openCell (T : SphericalType M) :
    sourceCharacteristic M T ⁻¹' sourceOpenCell M T =
      {x : SourceModelCell M T | x.val ∈ interior (permutahedron (restrictedMatrix M T.val))} := by
  ext x
  constructor
  · rintro ⟨y,hy⟩
    exact sourceCharacteristic_saturated_interior M T y.property hy
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

theorem sourceCharacteristic_interior_embedding (T : SphericalType M) :
    IsEmbedding (fun x : SourceModelInterior M T => sourceCharacteristic M T x.val) := by
  let f := sourceCharacteristic M T
  let O := sourceOpenCell M T
  have hc : IsClosedMap (O.restrictPreimage f) := f.continuous.isClosedMap.restrictPreimage O
  have hi : Function.Injective (O.restrictPreimage f) := by
    intro x y he
    have hx : x.val.val ∈ interior (permutahedron (restrictedMatrix M T.val)) := by
      exact (Set.ext_iff.mp (sourceCharacteristic_preimage_openCell M T) x.val).mp x.property
    have hy : y.val.val ∈ interior (permutahedron (restrictedMatrix M T.val)) := by
      exact (Set.ext_iff.mp (sourceCharacteristic_preimage_openCell M T) y.val).mp y.property
    have he' := congrArg Subtype.val he
    have hin := sourceCharacteristic_interior_injective M T
      (a₁ := ⟨x.val,hx⟩) (a₂ := ⟨y.val,hy⟩) he'
    exact Subtype.ext (congrArg (fun z : SourceModelInterior M T => z.val) hin)
  have hf := (IsClosedEmbedding.of_continuous_injective_isClosedMap
    (f.continuous.restrictPreimage) hi hc).isEmbedding
  let e : SourceModelInterior M T ≃ₜ (f ⁻¹' O) :=
    Homeomorph.setCongr (sourceCharacteristic_preimage_openCell M T).symm
  exact IsEmbedding.subtypeVal.comp (hf.comp e.isEmbedding)

end HarmonicArtin

end OAI
