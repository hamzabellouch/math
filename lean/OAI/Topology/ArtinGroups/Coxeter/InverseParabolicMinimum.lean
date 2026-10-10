import Mathlib
import OAI.Topology.ArtinGroups.Coxeter.Parabolic

namespace OAI

namespace HarmonicArtin.CoxeterExchange
variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

lemma inverse_is_parabolic_minimum (J : Set B) (w : W)
    (hw : ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (w*a)) :
    IsParabolicMinimum cs J w⁻¹ := by
  intro a ha
  calc
    cs.length w⁻¹ = cs.length w := cs.length_inv w
    _ ≤ cs.length (w*a⁻¹) := hw a⁻¹ ((parabolic cs J).inv_mem ha)
    _ = cs.length (a*w⁻¹) := by
      rw [← cs.length_inv (w*a⁻¹),mul_inv_rev,inv_inv]

lemma length_mul_of_right_minimum (J : Set B) (w : W)
    (hw : ∀ a ∈ parabolic cs J, cs.length w ≤ cs.length (w*a))
    (a : W) (ha : a ∈ parabolic cs J) :
    cs.length (w*a) = cs.length w+cs.length a := by
  have hm := inverse_is_parabolic_minimum cs J w hw
  calc
    cs.length (w*a) = cs.length (a⁻¹*w⁻¹) := by rw [← mul_inv_rev,cs.length_inv]
    _ = cs.length a⁻¹+cs.length w⁻¹ :=
      length_mul_of_minimum cs J w⁻¹ hm a⁻¹ ((parabolic cs J).inv_mem ha)
    _ = _ := by rw [cs.length_inv,cs.length_inv,Nat.add_comm]

end HarmonicArtin.CoxeterExchange

end OAI
