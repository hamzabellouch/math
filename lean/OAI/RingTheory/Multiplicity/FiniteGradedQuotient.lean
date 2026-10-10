import Mathlib
import OAI.RingTheory.Multiplicity.GradedLinearNormalization

namespace OAI

noncomputable section
open MvPolynomial DirectSum
namespace Lech.LinearNormalization
universe u v w
variable {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]

lemma integral_image_of_generators_zero {Q : Type w} [CommRing Q] [Algebra k Q]
    (q : A →ₐ[k] Q) {s : ℕ} (z : Fin s → A) (hz : ∀ i,q (z i) = 0)
    {x : A} (hx : IsIntegral (Algebra.adjoin k (Set.range z)) x) :
    IsIntegral k (q x) := by
  let B := Algebra.adjoin k (Set.range z)
  let C := integralClosure k Q
  have hB : B ≤ C.comap q := by
    apply Algebra.adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    change IsIntegral k (q (z i))
    rw [hz i]
    exact isIntegral_zero
  let φ : B →ₐ[k] C := (q.comp B.val).codRestrict C (fun b => hB b.property)
  have h : (algebraMap C Q).comp φ.toRingHom = q.toRingHom.comp (algebraMap B A) := rfl
  exact isIntegral_trans (q x) (hx.map_of_comp_eq φ.toRingHom q.toRingHom h)

lemma finite_quotient_of_integral_generators {N s : ℕ} (x : Fin N → A) (z : Fin s → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hi : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) :
    Module.Finite k (A ⧸ Ideal.span (Set.range z)) := by
  let J := Ideal.span (Set.range z)
  let q : A →ₐ[k] A ⧸ J := Ideal.Quotient.mkₐ k J
  have hqz (i) : q (z i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self i))
  have hgen : Algebra.adjoin k (Set.range (fun i => q (x i))) = ⊤ := by
    simpa only [AlgHom.map_adjoin,← Set.range_comp,Function.comp_def,Algebra.map_top,
      (AlgHom.range_eq_top q).mpr Ideal.Quotient.mk_surjective] using
      congrArg (Subalgebra.map q) hx
  let := Algebra.finite_adjoin_of_finite_of_isIntegral (Set.finite_range (fun i => q (x i)))
    (by rintro _ ⟨i,rfl⟩; exact integral_image_of_generators_zero q z hqz (hi i))
  exact Module.Finite.of_surjective
    (Algebra.adjoin k (Set.range (fun i => q (x i)))).val.toLinearMap
    (by intro a; exact ⟨⟨a,by rw [hgen]; trivial⟩,rfl⟩)

 

lemma finite_grading_bounded {M : Type v} [AddCommGroup M] [Module k M]
    [Module.Finite k M] (G : ℕ → Submodule k M) [Decomposition G] :
    ∃ c : ℕ, ∀ n, c ≤ n → G n = ⊥ := by
  classical
  obtain ⟨r,x,hx⟩ := Module.Finite.exists_fin (R:=k) (M:=M)
  let c := (Finset.univ : Finset (Fin r)).sup
    (fun i => ((decompose G (x i)).support.sup id)+1)
  refine ⟨c,?_⟩
  intro n hn
  let π : M →ₗ[k] G n := (DFinsupp.lapply n).comp (decomposeLinearEquiv G).toLinearMap
  have hπx (i : Fin r) : π (x i) = 0 := by
    apply DFinsupp.notMem_support_iff.mp
    intro hm
    change n ∈ (decompose G (x i)).support at hm
    have hle : n ≤ (decompose G (x i)).support.sup id := Finset.le_sup (f:=id) hm
    have hlt : ((decompose G (x i)).support.sup id)+1 ≤ c :=
      Finset.le_sup (f:=fun i => ((decompose G (x i)).support.sup id)+1) (Finset.mem_univ i)
    omega
  have hπ : LinearMap.ker π = ⊤ := by
    apply top_unique
    rw [← hx]
    exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hπx i)
  apply eq_bot_iff.mpr
  intro a ha
  have hz : π a = 0 := by
    change a ∈ LinearMap.ker π
    rw [hπ]; trivial
  have he : (π a : M) = a := decompose_of_mem_same G ha
  rw [← he,hz]
  exact Submodule.zero_mem _

lemma high_grades_in_span {N s : ℕ} (G : ℕ → Submodule k A) [GradedAlgebra G]
    (x : Fin N → A) (z : Fin s → A)
    (hx : Algebra.adjoin k (Set.range x) = ⊤)
    (hz : ∀ i,z i ∈ G 1)
    (hi : ∀ i,IsIntegral (Algebra.adjoin k (Set.range z)) (x i)) :
    ∃ c : ℕ, ∀ n,c ≤ n → ∀ a ∈ G n,a ∈ Ideal.span (Set.range z) := by
  let J := Ideal.span (Set.range z)
  let q : A →ₗ[k] A ⧸ J := J.mkQ.restrictScalars k
  have hJ : J.IsHomogeneous G := Ideal.homogeneous_span G _
    (by rintro _ ⟨i,rfl⟩; exact ⟨1,hz i⟩)
  have hker : q.ker.IsHomogeneous G := by
    rw [LinearMap.ker_restrictScalars,Submodule.ker_mkQ]
    exact hJ
  let H := Grading.imagePiece G q
  let : Decomposition H := Grading.imageDecomposition G q J.mkQ_surjective hker
  let : Module.Finite k (A ⧸ J) := finite_quotient_of_integral_generators x z hx hi
  obtain ⟨c,hc⟩ := finite_grading_bounded H
  refine ⟨c,fun n hn a ha => ?_⟩
  have hqa : q a ∈ H n := ⟨a,ha,rfl⟩
  rw [hc n hn] at hqa
  change a ∈ J
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q a = 0
  simpa using hqa
end Lech.LinearNormalization

end

end OAI
