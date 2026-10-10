import Mathlib
import OAI.Topology.ArtinGroups.Quivers.SmulMul
import OAI.Topology.ArtinGroups.Geometry.CoordinateExtension
import OAI.Topology.ArtinGroups.Geometry.RootNonnegAscent
import OAI.Topology.ArtinGroups.Coxeter.RestrictedMatrix

namespace OAI

namespace HarmonicArtin.Geometric
open HarmonicArtin.CoxeterExchange
open scoped BigOperators

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type*} [Fintype S] [DecidableEq S]

omit [Fintype S] in
lemma cartan_restricted (M : CoxeterMatrix S) (J : Set S) :
    cartan (restrictedMatrix M J)=(cartan M).submatrix Subtype.val Subtype.val := by
  ext i j
  by_cases hij : i=j
  · subst j
    simp [cartan]
  · have hval : (i:S)≠j := fun h => hij (Subtype.ext h)
    simp [cartan,hij,hval]

lemma coordinateExtension_injective (J : Set S) : Function.Injective (coordinateExtension J) := by
  intro x y h
  funext j
  simpa only [coordinateExtension_apply] using congrFun h (j:S)

lemma coordinateExtension_add (J : Set S) (x y : J → ℝ) :
    coordinateExtension J (x+y)=coordinateExtension J x+coordinateExtension J y := by
  simp only [coordinateExtension,Pi.add_apply,add_smul,Finset.sum_add_distrib]

lemma coordinateExtension_sub (J : Set S) (x y : J → ℝ) :
    coordinateExtension J (x-y)=coordinateExtension J x-coordinateExtension J y := by
  simp only [coordinateExtension,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]

lemma coordinateExtension_smul (J : Set S) (r : ℝ) (x : J → ℝ) :
    coordinateExtension J (r • x)=r • coordinateExtension J x := by
  simp only [coordinateExtension,Pi.smul_apply,smul_eq_mul,mul_smul,Finset.smul_sum]

lemma coordinateExtension_single (J : Set S) (i : J) :
    coordinateExtension J (Pi.single i 1)=Pi.single (i:S) 1 := by
  ext k
  by_cases hk : k ∈ J
  · simpa only [Pi.single_apply,Subtype.ext_iff] using
      coordinateExtension_apply J (Pi.single i 1) ⟨k,hk⟩
  · rw [coordinateExtension_outside J _ k hk]
    have hki : k≠(i:S) := fun h => hk (h.symm ▸ i.property)
    simp [hki]

lemma rootRow_extension (M : CoxeterMatrix S) (J : Set S) (i : J) (x : J → ℝ) :
    rootRow M i (coordinateExtension J x)=rootRow (restrictedMatrix M J) i x := by
  rw [rootRow_apply,rootRow_apply]
  unfold coordinateExtension
  rw [Matrix.mulVec_sum,Finset.sum_apply]
  simp only [Matrix.mulVec_smul,Pi.smul_apply,Matrix.mulVec_single,smul_eq_mul,
    Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,one_smul]
  rw [cartan_restricted]
  simp only [Matrix.mulVec,dotProduct,Matrix.submatrix_apply,mul_comm]

lemma reflection_extension (M : CoxeterMatrix S) (J : Set S) (i : J) (x : J → ℝ) :
    simpleReflection M i (coordinateExtension J x)=
      coordinateExtension J (simpleReflection (restrictedMatrix M J) i x) := by
  simp only [simpleReflection_apply,← rootRow_apply,rootRow_extension,
    coordinateExtension_sub,coordinateExtension_smul,coordinateExtension_single]

lemma representation_extension (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) (x : J → ℝ) :
    representation M.toCoxeterSystem (restrictionHom M J w) (coordinateExtension J x)=
      coordinateExtension J (representation (restrictedMatrix M J).toCoxeterSystem w x) := by
  induction w using (restrictedMatrix M J).toCoxeterSystem.simple_induction_left generalizing x with
  | one => simp
  | mul_simple_left w i ih =>
    rw [map_mul,map_mul,LinearEquiv.mul_apply,restrictionHom_simple,representation_simple,ih,
      map_mul,LinearEquiv.mul_apply,representation_simple,reflection_extension]

theorem restrictionHom_injective (M : CoxeterMatrix S) (J : Set S) :
    Function.Injective (restrictionHom M J) := by
  have hker : ∀ w, restrictionHom M J w=1 → w=1 := by
    intro w hw
    apply representation_map_eq_one (restrictedMatrix M J).toCoxeterSystem w
    apply LinearEquiv.ext
    intro x
    apply coordinateExtension_injective J
    have he := representation_extension M J w x
    rw [hw,map_one] at he
    exact he.symm
  intro a b h
  have hmap : restrictionHom M J (a*b⁻¹)=1 := by simp only [map_mul,map_inv,h,mul_inv_cancel]
  exact mul_inv_eq_one.mp (hker _ hmap)

lemma coordinateExtension_nonneg_iff (J : Set S) (x : J → ℝ) :
    (∀ k,0 ≤ coordinateExtension J x k) ↔ (∀ i,0 ≤ x i) := by
  constructor
  · intro h i
    simpa only [coordinateExtension_apply] using h i
  · intro h k
    by_cases hk : k∈J
    · change 0 ≤ coordinateExtension J x (⟨k,hk⟩ : J)
      rw [coordinateExtension_apply]
      exact h _
    · rw [coordinateExtension_outside J x k hk]

theorem restriction_ascent_iff (M : CoxeterMatrix S) (J : Set S)
    (w : (restrictedMatrix M J).Group) (i : J) :
    M.toCoxeterSystem.length (restrictionHom M J w*M.toCoxeterSystem.simple i)=
        M.toCoxeterSystem.length (restrictionHom M J w)+1 ↔
      (restrictedMatrix M J).toCoxeterSystem.length (w*(restrictedMatrix M J).toCoxeterSystem.simple i)=
        (restrictedMatrix M J).toCoxeterSystem.length w+1 := by
  rw [← root_nonneg_iff_ascent,← root_nonneg_iff_ascent,
    ← coordinateExtension_single J i,representation_extension,coordinateExtension_nonneg_iff]

end HarmonicArtin.Geometric

end OAI
