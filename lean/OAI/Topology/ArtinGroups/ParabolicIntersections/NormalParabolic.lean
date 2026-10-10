import OAI.Topology.ArtinGroups.ParabolicIntersections.DynamicsDefinitions
import OAI.Topology.ArtinGroups.Coxeter.ArtinCoxeter
import OAI.Topology.ArtinGroups.Geometry.CoordinateExtension

namespace OAI

/-!
# Normal parabolics in irreducible Artin groups

This proves the sufficient case of Charney--Martin--Morris-Wright (2026),
Lemma 3.3, used in the visual-splitting argument. The obstruction is detected
in the actual Coxeter geometric representation, without any assumption on
positive-monoid embeddings.
-/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] (M : CoxeterMatrix S)

omit [Fintype S] in
lemma artinCoxeter_mem_parabolic {X : Set S} {a : Artin M}
    (ha : a ∈ artinParabolic M X) :
    artinCoxeter M a ∈ coxeterParabolic M X := by
  induction ha using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨s,hs,rfl⟩ := hx
    rw [artinCoxeter_generator]
    exact Subgroup.subset_closure ⟨s,hs,rfl⟩
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy => rw [map_mul]; exact Subgroup.mul_mem _ ihx ihy
  | inv x hx ih => rw [map_inv]; exact Subgroup.inv_mem _ ih

/-- The standard generators in a standard parabolic are exactly its type. -/
lemma generator_mem_standard_iff (X : Set S) (t : S) :
    generator M t ∈ artinParabolic M X ↔ t∈X := by
  constructor
  · intro h
    by_contra ht
    have he := parabolic_exterior M X ⟨_,artinCoxeter_mem_parabolic M h⟩
      (Pi.single t 1) t ht
    change representation M.toCoxeterSystem (artinCoxeter M (generator M t))
      (Pi.single t 1) t=(Pi.single t 1 : S → ℝ) t at he
    rw [artinCoxeter_generator,representation_simple,simpleReflection_apply] at he
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,
      Matrix.mulVec_single,Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,
      one_smul,cartan_diag] at he
    norm_num at he
  · intro ht
    exact Subgroup.subset_closure ⟨t,ht,rfl⟩

lemma standard_ne_top_of_ne_univ {X : Set S} (hX : X≠Set.univ) :
    artinParabolic M X≠⊤ := by
  intro he
  apply hX
  apply Set.eq_univ_of_forall
  intro t
  apply (generator_mem_standard_iff M X t).mp
  rw [he]
  trivial

omit [Fintype S] in
lemma cartan_ne_zero_of_not_commuting (s t : S) (hst : s ≠ t) (hlabel : M s t ≠ 2) :
    cartan M s t ≠ 0 := by
  by_cases hz : M s t=0
  · simp [cartan,hst,hz]
  · have hm : 3 ≤ M s t := by have := M.off_diagonal s t hst; omega
    have hmr : (2 : ℝ)<M s t := by exact_mod_cast (by omega : 2<M s t)
    have hp : 0 < Real.pi/(M s t : ℝ) := div_pos Real.pi_pos (by linarith)
    have hlt : Real.pi/(M s t : ℝ)<Real.pi/2 := by
      apply (div_lt_div_iff₀ (by linarith : (0 : ℝ)<M s t) (by norm_num)).mpr
      nlinarith [Real.pi_pos]
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hlt⟩
    simp only [cartan,ite_eq_right hst,ite_eq_right hz]
    exact mul_ne_zero (by norm_num) (ne_of_gt hc)

/-- A noncommuting generator outside a standard parabolic does not normalize it. -/
theorem generator_conjugate_not_mem {X : Set S} {s t : S}
    (hs : s∈X) (ht : t∉X) (hlabel : M s t≠2) :
    generator M t * generator M s * (generator M t)⁻¹ ∉ artinParabolic M X := by
  intro h
  have hst : s≠t := fun he => ht (he ▸ hs)
  have hc := cartan_ne_zero_of_not_commuting M s t hst hlabel
  have he := parabolic_exterior M X ⟨_,artinCoxeter_mem_parabolic M h⟩
    (Pi.single t 1) t ht
  have hinv : (simpleReflection M t)⁻¹=simpleReflection M t := by
    exact inv_eq_of_mul_eq_one_left (simpleReflection_squared M t)
  simp only [map_mul,map_inv,artinCoxeter_generator,representation_simple,hinv,
    LinearEquiv.mul_apply] at he
  rw [simpleReflection_apply,simpleReflection_apply,simpleReflection_apply] at he
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Pi.single_eq_same,
    Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_single,
    Matrix.col,Matrix.transpose_apply,MulOpposite.op_one,one_smul,cartan_diag,
    Pi.single_eq_of_ne hst.symm] at he
  rw [cartan_symm M t s] at he
  nlinarith [sq_pos_of_ne_zero hc]

/-- CMMW Lemma 3.3: in irreducible type a normal standard parabolic is
trivial or the whole Artin group. -/
theorem normal_standard_parabolic (hIrred : IsIrreducible M) (X : Set S)
    (hn : (artinParabolic M X).Normal) : X=∅ ∨ X=Set.univ := by
  by_cases hx : X=∅
  · exact Or.inl hx
  right
  by_contra hu
  have hx' : X.Nonempty := Set.nonempty_iff_ne_empty.mpr hx
  have hu' : Xᶜ.Nonempty := Set.nonempty_compl.mpr hu
  obtain ⟨s,hs,t,ht,hst⟩ := hIrred X hx' hu'
  have hgen : generator M s ∈ artinParabolic M X := Subgroup.subset_closure ⟨s,hs,rfl⟩
  exact generator_conjugate_not_mem M hs ht hst (hn.conj_mem _ hgen _)

end HarmonicArtin.ParabolicIntersections

end OAI
