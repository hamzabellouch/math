import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength
import OAI.Topology.ArtinGroups.Geometry.CartanForm

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] [DecidableEq S]

theorem spherical_of_cartan_posDef (M:CoxeterMatrix S) (J:Set S)
    (hJ:((cartan M).submatrix ((↑):J→S) Subtype.val).PosDef) : IsSpherical M J := by
  have hC:(cartan (restrictedMatrix M J)).PosDef := by rwa [cartan_restricted]
  let : Finite (restrictedMatrix M J).Group := finite_of_cartan_posDef
    (restrictedMatrix M J).toCoxeterSystem hC
  have hr:coxeterParabolic M J≤(restrictionHom M J).range := by
    apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    exact ⟨(restrictedMatrix M J).toCoxeterSystem.simple ⟨i,hi⟩,restrictionHom_simple M J ⟨i,hi⟩⟩
  apply Finite.of_surjective
    (fun w=>(⟨restrictionHom M J w,restrictionHom_mem_parabolic M J w⟩:coxeterParabolic M J))
  intro y
  obtain ⟨w,hw⟩:=hr y.property
  exact ⟨w,Subtype.ext hw⟩

theorem spherical_iff_cartan_posDef (M:CoxeterMatrix S) (J:Set S) :
    IsSpherical M J ↔ ((cartan M).submatrix ((↑):J→S) Subtype.val).PosDef :=
  ⟨spherical_cartan_posDef M J,spherical_of_cartan_posDef M J⟩

end HarmonicArtin.Geometric

end OAI
