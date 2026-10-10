import Mathlib
import OAI.RingTheory.Multiplicity.LinearNormalization

namespace OAI

noncomputable section
open MvPolynomial
namespace Lech.LinearNormalization
universe u v
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma exists_direction_first_nonzero [Infinite k] {N d : ℕ}
    (f : MvPolynomial (Fin (N+1)) k) (hf : f.IsHomogeneous d) (hne : f ≠ 0) :
    ∃ a : Fin (N+1) → k, a 0 ≠ 0 ∧ eval a f ≠ 0 := by
  obtain ⟨a,ha⟩ := exists_homogeneous_direction (f*X 0)
    (hf.mul (isHomogeneous_X k (0 : Fin (N+1)))) (mul_ne_zero hne (X_ne_zero _))
  simp only [map_mul,eval_X,ne_eq,mul_eq_zero,not_or] at ha
  exact ⟨a,ha.2,ha.1⟩

lemma integrality_descends_through_adjoin {N s : ℕ}
    (y : Fin N → A) (z : Fin s → A)
    (hz : ∀ j,z j ∈ (Algebra.adjoin k (Set.range y)))
    (hy : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (y i))
    {x : A} (hx : IsIntegral (Algebra.adjoin k (Set.range y)) x) :
    IsIntegral (Algebra.adjoin k (Set.range z)) x := by
  let B := Algebra.adjoin k (Set.range y)
  let C := Algebra.adjoin k (Set.range z)
  have hCB : C ≤ B := Algebra.adjoin_le_iff.mpr (by rintro _ ⟨j,rfl⟩; exact hz j)
  let : Algebra C B := (Subalgebra.inclusion hCB).toRingHom.toAlgebra
  let : IsScalarTower k C B := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  let : IsScalarTower C B A := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have hB : B ≤ (integralClosure C A).restrictScalars k := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    exact hy i
  let ι : B →ₐ[C] A := IsScalarTower.toAlgHom C B A
  let : Algebra.IsIntegral C B := ⟨fun b =>
    (isIntegral_algHom_iff ι Subtype.val_injective).mp (hB b.property)⟩
  exact isIntegral_trans x hx

 

theorem exists_linear_normalization [Nontrivial A] [Infinite k]
    (G : ℕ → Submodule k A) [GradedAlgebra G] {N : ℕ}
    (x : Fin N → A) (hx : ∀ i,x i ∈ G 1) :
    ∃ s : ℕ, s ≤ N ∧ ∃ z : Fin s → A,
      (∀ j,z j ∈ Submodule.span k (Set.range x)) ∧
      Function.Injective (aeval (R:=k) z) ∧
      (∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) := by
  classical
  induction N with
  | zero =>
    refine ⟨0,le_rfl,x,fun i => Fin.elim0 i,?_,fun i => Fin.elim0 i⟩
    exact aeval_injective_iff_of_isEmpty.mpr (algebraMap k A).injective
  | succ N ih =>
    by_cases hind : Function.Injective (aeval (R:=k) x)
    · refine ⟨N+1,le_rfl,x,fun i => Submodule.subset_span (Set.mem_range_self i),hind,?_⟩
      intro i
      exact isIntegral_algebraMap
        (x := (⟨x i,Algebra.subset_adjoin (Set.mem_range_self i)⟩ :
          Algebra.adjoin k (Set.range x)))
    · obtain ⟨d,f,hf0,hf,hrel⟩ := homogeneous_relation G x hx hind
      obtain ⟨a,ha0,ha⟩ := exists_direction_first_nonzero f hf hf0
      let y : Fin N → A := fun i => x i.succ - a i.succ • ((a 0)⁻¹ • x 0)
      have hyspan (i : Fin N) : y i ∈ Submodule.span k (Set.range x) :=
        Submodule.sub_mem _ (Submodule.subset_span (Set.mem_range_self i.succ))
          (Submodule.smul_mem _ _ (Submodule.smul_mem _ _
            (Submodule.subset_span (Set.mem_range_self 0))))
      have hyG (i : Fin N) : y i ∈ G 1 :=
        Submodule.sub_mem _ (hx i.succ)
          (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (hx 0)))
      obtain ⟨s,hs,z,hz,hzi,hyi⟩ := ih y hyG
      have hySpanLe : Submodule.span k (Set.range y) ≤ Submodule.span k (Set.range x) :=
        Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hyspan i)
      have hyAdj : Submodule.span k (Set.range y) ≤
          (Algebra.adjoin k (Set.range y)).toSubmodule :=
        Submodule.span_le.mpr Algebra.subset_adjoin
      refine ⟨s,hs.trans (Nat.le_succ N),z,fun j => hySpanLe (hz j),hzi,?_⟩
      intro i
      apply integrality_descends_through_adjoin y z (fun j => hyAdj (hz j)) hyi
      exact integral_over_reduced_generators x a ha0 f hf ha hrel i

end Lech.LinearNormalization

end

end OAI
