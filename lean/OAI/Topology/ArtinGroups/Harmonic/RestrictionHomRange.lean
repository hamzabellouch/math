import Mathlib
import OAI.Topology.ArtinGroups.Geometry.RestrictionLength
import OAI.Topology.ArtinGroups.Harmonic.PositivePrefix

namespace OAI

namespace HarmonicArtin
open CoxeterExchange Geometric

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type*} [Fintype S] (M:CoxeterMatrix S)

omit [Fintype S] in
lemma restrictionHom_range_eq (J:Set S) :
    (restrictionHom M J).range=coxeterParabolic M J := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩
    exact Geometric.restrictionHom_mem_parabolic M J w
  · apply (Subgroup.closure_le _).mpr
    rintro y ⟨i,hi,rfl⟩
    exact ⟨(restrictedMatrix M J).toCoxeterSystem.simple ⟨i,hi⟩,
      restrictionHom_simple M J ⟨i,hi⟩⟩

theorem exists_longest_descent_factor (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    ∃q:(restrictedMatrix M J).Group,∃v:M.Group,
      (∀r:(restrictedMatrix M J).Group,(restrictedMatrix M J).toCoxeterSystem.length r≤
        (restrictedMatrix M J).toCoxeterSystem.length q) ∧
      IsParabolicMinimum M.toCoxeterSystem J v ∧
      w=restrictionHom M J q*v ∧
      M.toCoxeterSystem.length w=(restrictedMatrix M J).toCoxeterSystem.length q+
        M.toCoxeterSystem.length v := by
  obtain ⟨a,v,ha,hv,he,hl⟩:=exists_parabolic_decomposition M.toCoxeterSystem J w
  have hmem:a∈(restrictionHom M J).range:=by
    rw [restrictionHom_range_eq]
    exact ha
  obtain ⟨q,hq⟩:=hmem
  have hd:∀s:J,(restrictedMatrix M J).toCoxeterSystem.length
      ((restrictedMatrix M J).toCoxeterSystem.simple s*q)<
      (restrictedMatrix M J).toCoxeterSystem.length q:=by
    intro s
    have hh: M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*a)<M.toCoxeterSystem.length a:=
      (descent_parabolic_factor M.toCoxeterSystem J ha hv s.property).mp (by rw [←he];exact hJ s s.property)
    rw [←hq,←restrictionHom_simple M J s,←map_mul,restriction_length,restriction_length] at hh
    exact hh
  have hdi:∀s:J,(restrictedMatrix M J).toCoxeterSystem.length
      (q⁻¹*(restrictedMatrix M J).toCoxeterSystem.simple s)+1=
      (restrictedMatrix M J).toCoxeterSystem.length q⁻¹:=by
    intro s
    have hi:((restrictedMatrix M J).toCoxeterSystem.simple s*q)⁻¹=q⁻¹*(restrictedMatrix M J).toCoxeterSystem.simple s:=by
      rw [mul_inv_rev,(restrictedMatrix M J).toCoxeterSystem.inv_simple]
    have hh:=hd s
    have hp:=(restrictedMatrix M J).toCoxeterSystem.length_simple_mul q s
    rcases hp with hp|hp
    · omega
    · simpa only [←hi,CoxeterSystem.length_inv] using hp
  refine ⟨q,v,?_,hv,by rw [hq];exact he,?_⟩
  · intro r
    simpa only [CoxeterSystem.length_inv] using
      length_le_of_all_descents (restrictedMatrix M J).toCoxeterSystem q⁻¹ hdi r
  · simpa only [←hq,restriction_length] using hl

theorem spherical_of_left_descents (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    IsSpherical M J := by
  obtain ⟨q,v,hq,hv,he,hl⟩:=exists_longest_descent_factor M J w hJ
  let : Finite (restrictedMatrix M J).Group:=finite_of_all_descents
    (restrictedMatrix M J).toCoxeterSystem q
      (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem q hq)
  apply Finite.of_surjective
    (fun r=>(⟨restrictionHom M J r,Geometric.restrictionHom_mem_parabolic M J r⟩:coxeterParabolic M J))
  intro a
  have ha:a.val∈(restrictionHom M J).range:=by rw [restrictionHom_range_eq];exact a.property
  obtain ⟨r,hr⟩:=ha
  exact ⟨r,Subtype.ext hr⟩

theorem positive_longest_descent_prefix (J:Set S) (w:M.Group)
    (hJ:∀s∈J,M.toCoxeterSystem.length (M.toCoxeterSystem.simple s*w)<M.toCoxeterSystem.length w) :
    ∃q:(restrictedMatrix M J).Group,
      (∀r:(restrictedMatrix M J).Group,(restrictedMatrix M J).toCoxeterSystem.length r≤
        (restrictedMatrix M J).toCoxeterSystem.length q) ∧
      PositivePrefix M (positiveSimpleLift M (restrictionHom M J q)) (positiveSimpleLift M w) := by
  obtain ⟨q,v,hq,hv,he,hl⟩:=exists_longest_descent_factor M J w hJ
  refine ⟨q,hq,v |> positiveSimpleLift M,?_⟩
  rw [he]
  apply positiveSimpleLift_mul
  simpa only [he,restriction_length] using hl

end HarmonicArtin

end OAI
