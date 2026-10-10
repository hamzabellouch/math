import OAI.Topology.ArtinGroups.ParabolicIntersections.StandardEmbedding

namespace OAI

/-! Infinite cyclic generator subgroups and their intersections with standard
parabolics. The retraction argument supplies infinite branching in visual trees. -/
namespace HarmonicArtin.ParabolicIntersections
open CoxeterExchange Geometric
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

private lemma exponent_alternating (s t : S) (n : ℕ) :
    FreeGroup.lift (fun _ : S => Multiplicative.ofAdd (1 : ℤ)) (alternating s t n)=
      Multiplicative.ofAdd (n : ℤ) := by
  induction n generalizing s t with
  | zero => rfl
  | succ n ih =>
    rw [alternating,map_mul,FreeGroup.lift_apply_of,ih]
    change Multiplicative.ofAdd (1+(n : ℤ))=Multiplicative.ofAdd (n+1 : ℤ)
    congr 1
    omega

private lemma exponent_relators : ∀ r∈braidRelators M,
    FreeGroup.lift (fun _ : S => Multiplicative.ofAdd (1 : ℤ)) r=1 := by
  rintro r ⟨⟨s,t⟩,rfl⟩
  rw [map_mul,map_inv,exponent_alternating,exponent_alternating,mul_inv_cancel]

/-- The total exponent homomorphism for the Artin presentation. -/
def artinExponent : Artin M →* Multiplicative ℤ :=
  PresentedGroup.toGroup (exponent_relators M)

@[simp] lemma artinExponent_generator (s : S) :
    artinExponent M (generator M s)=Multiplicative.ofAdd (1 : ℤ) :=
  PresentedGroup.toGroup.of _

lemma generator_zpow_eq_one_iff (s : S) (n : ℤ) :
    generator M s ^ n=1 ↔ n=0 := by
  constructor
  · intro h
    have he := congrArg (artinExponent M) h
    simp only [map_zpow,map_one] at he
    rw [artinExponent_generator] at he
    simpa using congrArg Multiplicative.toAdd he
  · rintro rfl
    exact zpow_zero _

variable [Fintype S] (J : Set S)
local notation "cs" => M.toCoxeterSystem
local notation "R" => restrictedMatrix M J

lemma parabolicStepLetter_one_outside (t : S) (ht : t∉J) :
    parabolicStepLetter cs J 1 t=none := by
  have hrep : parabolicRep cs J 1=1 :=
    parabolicRep_of_minimum cs J 1 (by intro a _; simp only [(cs).length_one]; omega)
  have hcomp : parabolicComponent cs J 1=1 := by simp only [parabolicComponent,hrep,inv_one,mul_one]
  cases hh : parabolicStepLetter cs J 1 t with
  | none => rfl
  | some s =>
    have he := parabolicStepLetter_conjugate cs J 1 t s hh
    simp only [hcomp,MulAut.conj_apply,one_mul,inv_one,mul_one] at he
    exact False.elim (ht ((simple_injective cs he) ▸ s.property))

lemma parabolicStepArtin_one_outside (t : S) (ht : t∉J) :
    parabolicStepArtin M J 1 t=1 := by
  simp only [parabolicStepArtin,parabolicStepLetter_one_outside M J t ht,
    Option.toList_none,wordArtin,List.map_nil,List.prod_nil]

/-- Every integral power of an outside generator has trivial parabolic read. -/
lemma generator_power_retraction (t : S) (ht : t∉J) (n : ℤ) :
    (MulOpposite.unop (parabolicRetractionAction M J (generator M t ^ n))
      (1,1)).2=1 := by
  let f := parabolicStepPerm M J t
  let B : Set (M.Group × Artin R) := {x | (x.1=1 ∨ x.1=(cs).simple t) ∧ x.2=1}
  have hs := parabolicStepArtin_one_outside M J t ht
  have hs' : parabolicStepArtin M J ((cs).simple t) t=1 := by
    simpa only [one_mul] using (parabolicStepArtin_reverse M J 1 t).trans hs
  have hf : ∀ x∈B, f x∈B := by
    rintro ⟨w,a⟩ ⟨hw,ha⟩
    rcases hw with rfl|rfl
    · refine ⟨Or.inr (one_mul _),?_⟩
      change a*parabolicStepArtin M J 1 t=1
      rwa [hs,mul_one]
    · refine ⟨Or.inl ((cs).simple_mul_simple_self t),?_⟩
      change a*parabolicStepArtin M J ((cs).simple t) t=1
      rwa [hs',mul_one]
  have hfi : ∀ x∈B, f.symm x∈B := by
    rintro ⟨w,a⟩ ⟨hw,ha⟩
    rcases hw with rfl|rfl
    · refine ⟨Or.inr (one_mul _),?_⟩
      change a*(parabolicStepArtin M J 1 t)⁻¹=1
      rwa [hs,inv_one,mul_one]
    · refine ⟨Or.inl ((cs).simple_mul_simple_self t),?_⟩
      change a*(parabolicStepArtin M J ((cs).simple t) t)⁻¹=1
      rwa [hs',inv_one,mul_one]
  have hall : ∀ n : ℤ, MulOpposite.unop (parabolicRetractionAction M J (generator M t ^ n)) (1,1)∈B := by
    intro n
    induction n using Int.induction_on with
    | zero =>
      simp only [zpow_zero,map_one,MulOpposite.unop_one,Equiv.Perm.one_apply]
      exact ⟨Or.inl rfl,rfl⟩
    | succ n ih =>
      rw [zpow_add_one,map_mul,MulOpposite.unop_mul,Equiv.Perm.mul_apply,
        parabolicRetractionAction_generator,MulOpposite.unop_op]
      exact hf _ ih
    | pred n ih =>
      rw [zpow_sub_one,map_mul,map_inv,MulOpposite.unop_mul,Equiv.Perm.mul_apply,
        parabolicRetractionAction_generator,MulOpposite.unop_inv,MulOpposite.unop_op]
      exact hfi _ ih
  exact (hall n).2

/-- A nonzero power of an omitted generator never lies in a standard parabolic. -/
theorem generator_zpow_not_mem (t : S) (ht : t∉J) (n : ℤ) (hn : n≠0) :
    generator M t ^ n∉artinParabolic M J := by
  intro hm
  obtain ⟨a,ha⟩ := (restrictedArtinHom_range M J ▸ hm)
  have h := parabolicRetractionAction_standard M J a 1
  have he := generator_power_retraction M J t ht n
  rw [←ha] at he
  change (MulOpposite.unop (parabolicRetractionAction M J (restrictedArtinHom M J a))
    (parabolicState M J 1)).2=1 at he
  rw [h] at he
  change 1*a=1 at he
  rw [one_mul] at he
  have hh : generator M t ^ n=1 := by rw [←ha,he,map_one]
  exact hn ((generator_zpow_eq_one_iff M t n).mp hh)

end HarmonicArtin.ParabolicIntersections

end OAI
