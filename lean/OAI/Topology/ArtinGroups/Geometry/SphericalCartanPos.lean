import Mathlib
import OAI.Topology.ArtinGroups.Model
import OAI.Topology.ArtinGroups.Geometry.Form

namespace OAI

namespace HarmonicArtin.Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_cartan_posDef (M:CoxeterMatrix S) (J:Set S) (hJ:IsSpherical M J) :
    ((cartan M).submatrix ((↑):J → S) ((↑):J → S)).PosDef := by
  let : Finite (coxeterParabolic M J) := hJ
  let : Fintype (coxeterParabolic M J) := Fintype.ofFinite _
  let ρ := (representation M.toCoxeterSystem).comp (coxeterParabolic M J).subtype
  let g:J → coxeterParabolic M J := fun i=>⟨M.simple i,
    Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)⟩
  apply FiniteOrbit.principal_posDef ρ ((↑):J → S) g
  · intro i
    exact representation_simple M.toCoxeterSystem i
  · exact Subtype.val_injective

end HarmonicArtin.Geometric

end OAI
