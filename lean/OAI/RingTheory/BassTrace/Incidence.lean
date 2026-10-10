import OAI.RingTheory.BassTrace.ExteriorChains

namespace OAI

noncomputable section

namespace BassTrace

namespace OrientedIncidence

section

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V]

abbrev vertices {n : ℕ} (s : Set.powersetCard V n) : Fin n ↪o V :=
  Set.powersetCard.ofFinEmbEquiv.symm s

lemma vertices_mem {n : ℕ} (s : Set.powersetCard V n) (i : Fin n) : vertices s i ∈ s.val :=
  Finset.orderEmbOfFin_mem s.val s.property i

lemma vertices_range {n : ℕ} (s : Set.powersetCard V n) : Set.range (vertices s) = s.val :=
  Finset.range_orderEmbOfFin s.val s.property

def eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    Set.powersetCard V n :=
  ⟨s.val.erase (vertices s i), by simp [Finset.card_erase_of_mem (vertices_mem s i)]⟩

@[simp] lemma eraseFace_val {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    (eraseFace s i).val = s.val.erase (vertices s i) := rfl

lemma vertices_eraseFace {n : ℕ} (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices (eraseFace s i) = i.succAboveOrderEmb.comp (vertices s) := by
  symm
  apply Finset.orderEmbOfFin_unique' (eraseFace s i).property
  intro j
  apply Finset.mem_erase.mpr
  exact ⟨fun h => Fin.succAbove_ne i j ((vertices s).injective h),vertices_mem s _⟩

lemma boundary_basis (n : ℕ) (s : Set.powersetCard V (n+1)) :
    d n (basis (Y := V) (n+1) s) =
      ∑ i : Fin (n+1), (-1 : ℂ)^i.val • basis n (eraseFace s i) := by
  rw [basis_eq_wedge,d_wedge]
  apply Finset.sum_congr rfl
  intro i _
  rw [basis_eq_wedge]
  congr 2
  exact congrArg (fun e : Fin n ↪o V => (e : Fin n → V)) (vertices_eraseFace s i).symm

lemma boundary_basis_coefficient (n : ℕ) (s : Set.powersetCard V (n+1))
    (t : Set.powersetCard V n) :
    (basis n).repr (d n (basis (Y := V) (n+1) s)) t =
      ∑ i : Fin (n+1), if eraseFace s i = t then (-1 : ℂ)^i.val else 0 := by
  simp only [boundary_basis,map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,
    Module.Basis.repr_self,Finsupp.single_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

end

open scoped BigOperators

open Oriented ChainHomotopy

variable {V : Type*} [LinearOrder V] {n : ℕ}

lemma insert_eraseFace (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    insert (vertices s i) (eraseFace s i).val = s.val :=
  Finset.insert_erase (vertices_mem s i)

lemma eraseFace_neq (s : Set.powersetCard V (n+1)) (i : Fin (n+1)) :
    vertices s i ∉ (eraseFace s i).val := Finset.notMem_erase _ _

lemma incidence_pair_injective (t : Set.powersetCard V n)
    {a b : Set.powersetCard V (n+1) × Fin (n+1)}
    (ha : eraseFace a.1 a.2 = t) (hb : eraseFace b.1 b.2 = t)
    (he : vertices a.1 a.2 = vertices b.1 b.2) : a = b := by
  have hs : a.1 = b.1 := by
    apply Subtype.ext
    rw [← insert_eraseFace a.1 a.2,← insert_eraseFace b.1 b.2,ha,hb,he]
  apply Prod.ext hs
  exact (vertices b.1).injective (by simpa only [hs] using he)

def incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) :
    Finset (Set.powersetCard V (n+1) × Fin (n+1)) :=
  (F ×ˢ Finset.univ).filter fun p => eraseFace p.1 p.2 = t

def apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) : Finset V :=
  (incidencePairs F t).image fun p => vertices p.1 p.2

lemma mem_apexes (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n) (u : V) :
    u ∈ apexes F t ↔ u ∉ t.val ∧ ∃ s ∈ F, s.val = insert u t.val := by
  constructor
  · intro h
    obtain ⟨⟨s,i⟩,hp,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hp,ht⟩ := Finset.mem_filter.mp hp
    have hs := (Finset.mem_product.mp hp).1
    refine ⟨ht ▸ eraseFace_neq s i,s,hs,?_⟩
    rw [← insert_eraseFace s i,ht]
  · rintro ⟨hu,s,hs,he⟩
    have hus : u ∈ s.val := he ▸ Finset.mem_insert_self _ _
    obtain ⟨i,rfl⟩ := (show u ∈ Set.range (vertices s) from (vertices_range s).symm ▸ hus)
    apply Finset.mem_image.mpr
    refine ⟨(s,i),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hs,Finset.mem_univ _⟩,?_⟩,rfl⟩
    apply Subtype.ext
    simp only [eraseFace_val,he,Finset.erase_insert hu]

lemma sum_incidencePairs (F : Finset (Set.powersetCard V (n+1))) (t : Set.powersetCard V n)
    {A : Type*} [AddCommMonoid A] (f : V → A) :
    ∑ p ∈ incidencePairs F t, f (vertices p.1 p.2) = ∑ u ∈ apexes F t, f u := by
  symm
  apply Finset.sum_image
  intro a ha b hb he
  exact incidence_pair_injective t (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 he

lemma boundary_sum_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (w : Set.powersetCard V (n+1) → ℂ) (t : Set.powersetCard V n) :
    (basis n).repr (d n (∑ s ∈ F, w s • basis (n+1) s)) t =
      ∑ p ∈ incidencePairs F t, w p.1 * (-1 : ℂ)^p.2.val := by
  simp only [map_sum,map_smul,Finsupp.finsetSum_apply,Finsupp.smul_apply,smul_eq_mul,
    boundary_basis_coefficient,Finset.mul_sum]
  rw [incidencePairs,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

end OrientedIncidence

namespace Sparse.Orientation

section

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

lemma linearIndependent_of_normalized {I : Type*} {v : I → E}
    (hv : AffineIndependent ℝ v) (α : E →ₗ[ℝ] ℝ) (hα : ∀ i, α (v i) = 1) :
    LinearIndependent ℝ v := by
  classical
  rw [linearIndependent_iff']
  intro s w hw
  have hs : ∑ i ∈ s, w i = 0 := by
    have hh := congrArg α hw
    simpa only [map_sum,map_smul,hα,smul_eq_mul,mul_one,map_zero] using hh
  exact hv.eq_zero_of_sum_eq_zero hs hw

lemma det_ne_zero_of_normalized {n : ℕ} {v : Fin n → (Fin n → ℝ)}
    (hv : AffineIndependent ℝ v) (hα : ∀ i, ∑ j, v i j = 1) : Matrix.det v ≠ 0 := by
  let α : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ j, LinearMap.proj j
  have hi := linearIndependent_of_normalized hv α (by intro i; simpa [α] using hα i)
  exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_row hi)

def facetForm (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) : (Fin (n+1) → ℝ) →ₗ[ℝ] ℝ :=
  { toFun := fun x => Matrix.detRowAlternating.curryLeft x v
    map_add' := fun x y => by simp
    map_smul' := fun c x => by simp }

@[simp] lemma facetForm_apply (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ))
    (x : Fin (n+1) → ℝ) : facetForm n v x = Matrix.det (Fin.cons x v) := rfl

lemma facetForm_vertex (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) (j : Fin n) :
    facetForm n v (v j) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_zero_of_row_eq (i := 0) (j := j.succ) (Fin.succ_ne_zero j).symm
  simp

lemma facetForm_convexHull (n : ℕ) (v : Fin n → (Fin (n+1) → ℝ)) :
    ∀ x ∈ convexHull ℝ (Set.range v), facetForm n v x = 0 := by
  apply convexHull_min
  · rintro _ ⟨i,rfl⟩
    exact facetForm_vertex n v i
  · exact (facetForm n v).ker.convex

end

lemma det_cons_delete {n : ℕ} (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) =
      (-1 : ℝ)^i.val * Matrix.det v := by
  have h := Matrix.detRowAlternating.neg_one_pow_smul_map_insertNth i (v i) (i.removeNth v)
  rw [Fin.insertNth_removeNth,Function.update_eq_self] at h
  change (-1 : ℤ) ^ i.val • Matrix.det v =
    Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j))) at h
  simpa only [zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one] using h.symm

lemma realSign_negOnePow_mul (k : ℕ) (a : ℝ) :
    Real.sign ((-1 : ℝ)^k * a) = (-1 : ℝ)^k * Real.sign a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, mul_neg_one,neg_mul,Real.sign_neg,ih,neg_mul]

lemma determinant_deletion_orientation {n : ℕ}
    (v : Fin (n+1) → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (Real.sign (Matrix.det v) : ℂ) * (-1 : ℂ)^i.val =
      (Real.sign (Matrix.det (Fin.cons (v i) (fun j => v (i.succAbove j)))) : ℂ) := by
  rw [det_cons_delete,realSign_negOnePow_mul]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,Complex.ofReal_one]
  exact mul_comm _ _

open scoped BigOperators

lemma det_cons_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    Matrix.det (Fin.cons (Pi.single i 1) v) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) := by
  calc
    _ = ∑ j : Fin (n+1), (-1 : ℝ)^j.val * (if j = i then 1 else 0) *
        Matrix.det (fun a b => v a (j.succAbove b)) :=
      by
        have h := Matrix.det_succ_row_zero (Fin.cons (Pi.single i 1) v)
        change Matrix.det (Fin.cons (Pi.single i 1) v) =
          ∑ j : Fin (n+1), (-1 : ℝ)^j.val *
            (Pi.single i (1 : ℝ) : Fin (n+1) → ℝ) j *
            Matrix.det (fun a b => v a (j.succAbove b)) at h
        simpa only [Pi.single_apply] using h
    _ = _ := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hji
        simp [hji]
      · simp

lemma facetForm_on_unit {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    facetForm n v (Pi.single i 1) =
      (-1 : ℝ)^i.val * Matrix.det (fun j k => v j (i.succAbove k)) :=
  det_cons_unit v i

lemma facetForm_column_zero {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ))
    (i : Fin (n+1)) (hi : ∀ j, v j i = 0) (k : Fin (n+1)) (hki : k ≠ i) :
    facetForm n v (Pi.single k 1) = 0 := by
  rw [facetForm_apply]
  apply Matrix.det_eq_zero_of_column_eq_zero i
  intro j
  cases j using Fin.cases with
  | zero => simp [hki.symm]
  | succ j => exact hi j

lemma linearMap_eq_coord_of_units {n : ℕ} (f : (Fin n → ℝ) →ₗ[ℝ] ℝ)
    (i : Fin n) (hf : ∀ k, k ≠ i → f (Pi.single k 1) = 0) (x : Fin n → ℝ) :
    f x = x i * f (Pi.single i 1) := by
  have hx : x = ∑ k : Fin n, x k • Pi.single k 1 := by
    funext j
    simp [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.single_apply]
  have hh := congrArg f hx
  rw [map_sum] at hh
  simp only [map_smul,smul_eq_mul] at hh
  rw [hh,Finset.sum_eq_single i]
  · intro k _ hki
    simp [hf k hki]
  · simp

lemma facet_boundary_term {n : ℕ} (v : Fin n → (Fin (n+1) → ℝ)) (i : Fin (n+1)) :
    (if ∀ k, k ≠ i → facetForm n v (Pi.single k 1) = 0
       then Real.sign (facetForm n v (Pi.single i 1)) else 0) =
    (if ∀ j, v j i = 0 then
       (-1 : ℝ)^i.val * Real.sign (Matrix.det (fun j k => v j (i.succAbove k))) else 0) := by
  by_cases hi : ∀ j, v j i = 0
  · rw [ite_eq_left hi,ite_eq_left (fun k hki => facetForm_column_zero v i hi k hki),
      facetForm_on_unit,realSign_negOnePow_mul]
  · rw [ite_eq_right hi]
    split_ifs with hf
    · have hz : facetForm n v (Pi.single i 1) = 0 := by
        by_contra hn
        apply hi
        intro j
        have h := linearMap_eq_coord_of_units (facetForm n v) i hf (v j)
        rw [facetForm_vertex] at h
        exact (mul_eq_zero.mp h.symm).resolve_right hn
      simp only [hz,Real.sign_zero]
    · rfl

end Sparse.Orientation

namespace Fundamental

open scoped BigOperators

open OrientedIncidence Oriented ChainHomotopy Sparse.Orientation

variable {V : Type*} [LinearOrder V] {n : ℕ}

def chain (F : Finset (Set.powersetCard V (n+1))) (p : V → (Fin (n+1) → ℝ)) :
    Oriented.Degree V (n+1) :=
  ∑ s ∈ F, (Real.sign (Matrix.det (fun i => p (vertices s i))) : ℂ) • basis (n+1) s

lemma boundary_coefficient (F : Finset (Set.powersetCard V (n+1)))
    (p : V → (Fin (n+1) → ℝ)) (t : Set.powersetCard V n) :
    (basis n).repr (d n (chain F p)) t =
      ∑ u ∈ apexes F t, (Real.sign (facetForm n (fun i => p (vertices t i)) (p u)) : ℂ) := by
  rw [chain,boundary_sum_coefficient]
  rw [← sum_incidencePairs F t]
  apply Finset.sum_congr rfl
  intro a ha
  have ht := (Finset.mem_filter.mp ha).2
  rw [determinant_deletion_orientation]
  congr 2
  rw [facetForm_apply]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
    simp only [Fin.cons_succ]
    have h := congrArg (fun e : Fin n ↪o V => e i) (vertices_eraseFace a.1 a.2)
    rw [ht] at h
    exact congrArg p h.symm

end Fundamental

end BassTrace

end

end OAI
