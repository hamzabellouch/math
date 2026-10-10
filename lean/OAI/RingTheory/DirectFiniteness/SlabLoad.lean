import OAI.RingTheory.DirectFiniteness.SlabNumerics

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
namespace DirectionFrame
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]

omit [Fintype A] in
lemma slabLoadBound_small (F : DirectionFrame Q A R E)
    (hq : 3305600000 ≤ Fintype.card Q)
    (hR : Fintype.card R ≤ 2*(Fintype.card Q)^100)
    (hE : Fintype.card E=(Fintype.card Q)^119)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p ≤ 2/(Fintype.card Q:ℝ)^117) :
    F.slabLoadBound p ≤ 1/16 := by
  let q : ℝ := Fintype.card Q
  have hqbig : 3305600000 ≤ q := by dsimp [q]; exact_mod_cast hq
  have hq2 : 2 ≤ q := by linarith
  have hq1 : 1 ≤ q := by linarith
  have hq0 : 0 < q := by linarith
  have hr : (Fintype.card R:ℝ) ≤ 2*q^100 := by dsimp [q]; exact_mod_cast hR
  obtain ⟨hhole,htwo,hfour⟩ := slab_weighted_bounds hq2 hp0 hp
  have hterm (i : Fin 3) :
      ((Fintype.card R*(i.val+3)^2*2^(i.val+3)*(100*Fintype.card Q)^2*Fintype.card Q^(i.val+3) : ℕ):ℝ)*p^2 +
      (((Fintype.card R*Fintype.card Q)*(i.val+3)^4*3^(i.val+3)*(Fintype.card Q*Fintype.card E)*
        (Fintype.card Q*Fintype.card E)^2*Fintype.card Q^(i.val+3) : ℕ):ℝ)*p^4
      ≤ 64000000/q+4860000/q := by
    have h2 := slab_two_count_bound hq1 hr (by omega : i.val+3 ≤ 5)
    have h4 := slab_four_count_bound hq1 hr (by omega : i.val+3 ≤ 5)
    have h2' := (mul_le_mul_of_nonneg_right h2 (sq_nonneg p)).trans htwo
    have h4' := (mul_le_mul_of_nonneg_right h4 (pow_nonneg hp0 4)).trans hfour
    rw [hE]
    push_cast at h2' h4' ⊢
    exact add_le_add h2' h4'
  calc
    F.slabLoadBound p ≤ 20000/q + ∑ _i : Fin 3, (64000000/q+4860000/q) := by
      apply add_le_add
      · simpa only [show (100:ℝ)^2=10000 by norm_num] using hhole
      · exact Finset.sum_le_sum (fun i _ => hterm i)
    _ = 206600000/q := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
    _ ≤ 1/16 := (div_le_iff₀ hq0).mpr (by linarith)

lemma exists_successfulSlabs_large (F : DirectionFrame Q A R E) (S O : Finset A)
    (hO : HoleEvents.GoodHoles S F.W F.U (fun r t => F.exc r t) O)
    (hq : 3305600000 ≤ Fintype.card Q)
    (hR : Fintype.card R ≤ 2*(Fintype.card Q)^100)
    (hE : Module.finrank Q E=119) :
    ∃ P : SlabVariable F → Plane Q E, F.SuccessfulSlabs O P := by
  let : Nonempty (Plane Q E) := plane_nonempty (by rw [hE]; decide)
  have hq2 : (2:ℝ) ≤ Fintype.card Q := by exact_mod_cast (by omega : 2 ≤ Fintype.card Q)
  obtain ⟨hp0,hp⟩ := slab_probability_bound hq2
  have he : inclusionProbability Q E = ((Fintype.card Q:ℝ)^2-1)/((Fintype.card Q:ℝ)^119-1) := by
    rw [inclusionProbability,hE]
  rw [← he] at hp0 hp
  refine F.exists_successfulSlabs S O hO hp0 (F.slabLoadBound_small hq hR ?_ hp0 hp)
  rw [Module.card_eq_pow_finrank (K := Q),hE]

end DirectionFrame
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
