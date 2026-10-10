import Mathlib
import OAI.Topology.ArtinGroups.Geometry.CartanRestricted

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

theorem restriction_length (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) :
    M.toCoxeterSystem.length (restrictionHom M J w)=
      (restrictedMatrix M J).toCoxeterSystem.length w := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_right with
  | one => simp
  | mul_simple_right w i ih =>
    rw [map_mul,restrictionHom_simple]
    rcases (restrictedMatrix M J).toCoxeterSystem.length_mul_simple w i with ha | hd
    · rw [(restriction_ascent_iff M J w i).mpr ha,ha,ih]
    · rcases M.toCoxeterSystem.length_mul_simple (restrictionHom M J w) i with ha | hd'
      · have hb := (restriction_ascent_iff M J w i).mp ha
        omega
      · omega

omit [Fintype S] [DecidableEq S] in
lemma restriction_wordProd (M : CoxeterMatrix S) (J : Set S) (u : List J) :
    restrictionHom M J ((restrictedMatrix M J).toCoxeterSystem.wordProd u)=
       M.toCoxeterSystem.wordProd (u.map Subtype.val) := by
  induction u with
  | nil => simp
  | cons i u ih =>
    simp only [CoxeterSystem.wordProd_cons,map_mul,restrictionHom_simple,ih,List.map_cons]

lemma restriction_reduced_iff (M : CoxeterMatrix S) (J : Set S) (u : List J) :
    M.toCoxeterSystem.IsReduced (u.map Subtype.val) ↔
      (restrictedMatrix M J).toCoxeterSystem.IsReduced u := by
  simp only [CoxeterSystem.IsReduced,← restriction_wordProd,restriction_length,List.length_map]

omit [Fintype S] [DecidableEq S] in
lemma restrictionHom_mem_parabolic (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) : restrictionHom M J w ∈ coxeterParabolic M J := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_left with
  | one => simpa only [map_one] using (coxeterParabolic M J).one_mem
  | mul_simple_left w i ih =>
    rw [map_mul,restrictionHom_simple]
    exact (coxeterParabolic M J).mul_mem
      (Subgroup.subset_closure (Set.mem_image_of_mem _ i.property)) ih

theorem restricted_finite (M : CoxeterMatrix S) (J : Set S) (hJ : IsSpherical M J) :
    Finite (restrictedMatrix M J).Group := by
  let : Finite (coxeterParabolic M J) := hJ
  exact Finite.of_injective
    (fun w => (⟨restrictionHom M J w,restrictionHom_mem_parabolic M J w⟩ : coxeterParabolic M J))
    (fun a b h => restrictionHom_injective M J (congrArg Subtype.val h))

end HarmonicArtin.Geometric

end OAI
