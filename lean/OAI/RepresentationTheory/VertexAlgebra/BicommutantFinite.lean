import OAI.RepresentationTheory.VertexAlgebra.BicommutantOrbit
import OAI.RepresentationTheory.VertexAlgebra.BoundedIntertwinerFinite

namespace OAI

noncomputable section
namespace StronglyRationalVOA.BicommutantDensity
open BoundedIntertwiner
attribute [local instance] Classical.propDecidable
universe u w
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {ι : Type w} [Fintype ι]

def diagonalHom (ι : Type w) [Fintype ι] : (H →L[ℂ] H) →⋆ₐ[ℂ] (SumSpace ι H →L[ℂ] SumSpace ι H) where
  toFun := diagonal (ι := ι)
  map_zero' := by ext x i; rfl
  map_one' := by ext x i; rfl
  map_add' _ _ := by ext x i; rfl
  map_mul' _ _ := by ext x i; rfl
  commutes' _ := by ext x i; rfl
  map_star' D := by
    change diagonal (ι := ι) D.adjoint = (diagonal (ι := ι) D).adjoint
    apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
    intro x y
    simp only [PiLp.inner_apply, diagonal_apply]
    exact Finset.sum_congr rfl (fun i _ => ContinuousLinearMap.adjoint_inner_left D (y i) (x i))

@[simp] theorem diagonalHom_apply (D : H →L[ℂ] H) (x : SumSpace ι H) (i : ι) :
    diagonalHom (H := H) ι D x i = D (x i) := rfl

def inclusion (i : ι) : H →L[ℂ] SumSpace ι H := by
  classical
  exact (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => if j = i then ContinuousLinearMap.id ℂ H else 0))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem inclusion_apply (i j : ι) (x : H) :
    inclusion i x j = if j = i then x else 0 := by
  classical
  by_cases h : j = i <;> simp [inclusion, h]

omit [CompleteSpace H] in
theorem sum_inclusion (x : SumSpace ι H) : ∑ i, inclusion i (x i) = x := by
  classical
  ext j
  simp [inclusion_apply]

theorem diagonalHom_inclusion (D : H →L[ℂ] H) (i : ι) (x : H) :
    diagonalHom (H := H) ι D (inclusion i x) = inclusion i (D x) := by
  classical
  ext j
  by_cases h : j = i <;> simp [diagonalHom_apply, inclusion_apply, h]

def entry (P : SumSpace ι H →L[ℂ] SumSpace ι H) (i j : ι) : H →L[ℂ] H :=
  (PiLp.proj 2 (fun _ : ι => H) i).comp (P.comp (inclusion j))

omit [CompleteSpace H] [Fintype ι] in
@[simp] theorem entry_apply (P : SumSpace ι H →L[ℂ] SumSpace ι H) (i j : ι) (x : H) :
    entry P i j x = P (inclusion j x) i := rfl

omit [CompleteSpace H] in
theorem apply_eq_sum_entry (P : SumSpace ι H →L[ℂ] SumSpace ι H) (x : SumSpace ι H) (i : ι) :
    P x i = ∑ j, entry P i j (x j) := by
  conv_lhs => rw [← sum_inclusion x]
  simp [entry_apply]

theorem entry_commutes (P : SumSpace ι H →L[ℂ] SumSpace ι H) (D : H →L[ℂ] H)
    (h : Commute (diagonalHom (H := H) ι D) P) (i j : ι) : Commute D (entry P i j) := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun Q : SumSpace ι H →L[ℂ] SumSpace ι H => Q (inclusion j x) i) h.eq
  simpa only [mul_apply_eq_comp, diagonalHom_apply, diagonalHom_inclusion,
    entry_apply] using he

theorem diagonal_commutes_of_entries
    (P : SumSpace ι H →L[ℂ] SumSpace ι H) (D : H →L[ℂ] H)
    (h : ∀ i j, Commute D (entry P i j)) : Commute (diagonalHom (H := H) ι D) P := by
  apply ContinuousLinearMap.ext
  intro x
  ext i
  simp only [mul_apply_eq_comp, diagonalHom_apply]
  rw [apply_eq_sum_entry P x i, map_sum, apply_eq_sum_entry P (diagonalHom (H := H) ι D x) i]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun Q : H →L[ℂ] H => Q (x j)) (h i j).eq

theorem diagonal_bicommutant (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H))) :
    diagonalHom (H := H) ι (D : H →L[ℂ] H) ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (B.map (diagonalHom (H := H) ι) : Set
        (SumSpace ι H →L[ℂ] SumSpace ι H)) : Set (SumSpace ι H →L[ℂ] SumSpace ι H)) := by
  have hc (P : SumSpace ι H →L[ℂ] SumSpace ι H)
      (hP : P ∈ StarSubalgebra.centralizer ℂ (B.map (diagonalHom (H := H) ι) : Set
        (SumSpace ι H →L[ℂ] SumSpace ι H))) : Commute (diagonalHom (H := H) ι D.val) P := by
    apply diagonal_commutes_of_entries
    intro i j
    have he : entry P i j ∈ StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro b hb
      have hb' (b : B) : Commute (diagonalHom (H := H) ι b.val) P :=
        ((StarSubalgebra.mem_centralizer_iff ℂ).mp hP _ ⟨b, b.property, rfl⟩).1
      exact ⟨(entry_commutes P b (hb' ⟨b,hb⟩) i j).eq,
        (entry_commutes P (star b) (hb' (star ⟨b,hb⟩)) i j).eq⟩
    exact (((StarSubalgebra.mem_centralizer_iff ℂ).mp D.property _ he).1).symm
  rw [StarSubalgebra.mem_centralizer_iff]
  intro P hP
  exact ⟨(hc P hP).eq.symm, (hc (star P) (star_mem hP)).eq.symm⟩

 

theorem exists_approx_finite (B : StarSubalgebra ℂ (H →L[ℂ] H))
    (D : StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (B : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H)))
    (x : ι → H) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : B, ∀ i, ‖(b : H →L[ℂ] H) (x i) - (D : H →L[ℂ] H) (x i)‖ < ε := by
  obtain ⟨b, hb⟩ := exists_approx_one (B.map (diagonalHom (H := H) ι))
    ⟨diagonalHom (H := H) ι D.val, diagonal_bicommutant B D⟩ (WithLp.toLp 2 x) hε
  obtain ⟨a, ha, he⟩ := b.property
  refine ⟨⟨a,ha⟩, fun i => ?_⟩
  have hi := PiLp.norm_apply_le (diagonalHom (H := H) ι (a-D.val) (WithLp.toLp 2 x)) i
  have hi' : ‖a (x i) - D.val (x i)‖ ≤
      ‖diagonalHom (H := H) ι a (WithLp.toLp 2 x) - diagonalHom (H := H) ι D.val (WithLp.toLp 2 x)‖ := by
    change ‖a (x i) - D.val (x i)‖ ≤
      ‖diagonalHom (H := H) ι (a-D.val) (WithLp.toLp 2 x)‖ at hi
    simpa only [map_sub, sub_apply] using hi
  apply hi'.trans_lt
  change ‖b.val (WithLp.toLp 2 x) - diagonalHom (H := H) ι D.val (WithLp.toLp 2 x)‖ < ε at hb
  change diagonalHom (H := H) ι a = b.val at he
  rw [← he] at hb
  exact hb
end StronglyRationalVOA.BicommutantDensity

end

end OAI
