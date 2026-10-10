import OAI.RingTheory.DirectFiniteness.PrescribedSlots

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample
open PolynomialPairing FiniteGeometry

/-- The numerical interval for the holes gives exactly the strict rectangular
inequality and the ell-squared packing bound, without rounding assumptions. -/
lemma hole_size_inequalities {N m ℓ : ℕ} (hN : 0 < N) (hmN : m ≤ N)
    (hℓ : 3 ≤ ℓ) (hlo : 2 * N ≤ m * (ℓ+1)^2)
    (hhi : m * (ℓ+1)^2 ≤ 7 * N) :
    0 < m ∧ m < N-m ∧ N-m ≤ m * ℓ^2 := by
  have hm : 0 < m := by
    by_contra hh
    have he : m = 0 := by omega
    rw [he,zero_mul] at hlo
    omega
  have hsq : 16 ≤ (ℓ+1)^2 := by nlinarith
  have hmb : 16*m ≤ 7*N := (by nlinarith : 16*m ≤ m*(ℓ+1)^2).trans hhi
  have hsmall : 2*m < N := by nlinarith
  have hs : (ℓ+1)^2 ≤ 2*(ℓ^2+1) := by nlinarith [sq_nonneg (ℓ-1 : ℤ)]
  have hn : N ≤ m*ℓ^2 + m := by nlinarith
  exact ⟨hm,by omega,by omega⟩

namespace PolynomialPairing
variable {Q K : Type} [Field Q] [Fintype Q] [Field K] [Algebra Q K]
  {q n : ℕ}

def complementMatrix (a : Fin q ≃ Q) (O : Finset (Fin n → Q)) :
    Matrix O {v : Fin n → Q // v ∉ O} K :=
  fun i v => algebraMap Q K (column a ((q-2)/2) O v.val i)

lemma complementMatrix_global (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (hn : 0 < n) (O : Finset (Fin n → Q))
    (hO : O ⊆ simplexPoints a n ((q-2)/2)) :
    complementMatrix (K := K) a O * (complementMatrix (K := K) a O).transpose = -1 := by
  ext i j
  have hh := congrFun (congrFun (sum_complement_gram a hq hn O hO) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.neg_apply,Matrix.one_apply] at hh
  have hs : ∑ v : {v : Fin n → Q // v ∉ O},
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j =
      ∑ v ∈ Finset.univ \ O, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    symm
    exact Finset.sum_subtype _ (by simp) _
  change (∑ v : {v : Fin n → Q // v ∉ O},
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j)) = -(if i = j then 1 else 0)
  simp_rw [← map_mul]
  rw [← map_sum,hs,hh]
  simp

lemma sum_fullLine_gram (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)} (hs : FullLine (Q := Q) s) :
    ∑ v ∈ s, gramColumn a ((q-2)/2) O v = 0 := by
  obtain ⟨x,w,hw,rfl⟩ := hs
  let l : PolynomialPairing.AffineLine Q n := ⟨x,w,hw⟩
  have hl : l.points = linePoints (Q := Q) x w := by
    ext z
    simp only [PolynomialPairing.AffineLine.points,linePoints,Finset.mem_image,
      Finset.mem_univ,true_and]
    rfl
  rw [← hl]
  exact sum_line_gram a hq O l

lemma complementMatrix_local (a : Fin q ≃ Q) (hq : q = Fintype.card Q)
    (O : Finset (Fin n → Q)) {s : Finset (Fin n → Q)}
    (hs : FullLine (Q := Q) s) (ha : ∀ v ∈ s, v ∉ O) (i j : O) :
    ∑ v ∈ s.subtype (fun v => v ∉ O),
      complementMatrix (K := K) a O i v * complementMatrix a O j v = 0 := by
  have hh := congrFun (congrFun (sum_fullLine_gram a hq O hs) i) j
  simp only [Matrix.sum_apply,gramColumn,Matrix.zero_apply] at hh
  change ∑ v ∈ s.subtype (fun v => v ∉ O),
    algebraMap Q K (column a ((q-2)/2) O v.val i) *
    algebraMap Q K (column a ((q-2)/2) O v.val j) = 0
  simp_rw [← map_mul]
  rw [← map_sum]
  have he : (∑ v ∈ s.subtype (fun v => v ∉ O),
      column a ((q-2)/2) O v.val i * column a ((q-2)/2) O v.val j) =
      ∑ v ∈ s, column a ((q-2)/2) O v i * column a ((q-2)/2) O v j := by
    exact Finset.sum_subtype_of_mem (fun v => column a ((q-2)/2) O v i * column a ((q-2)/2) O v j) ha
  rw [he,hh,map_zero]

end PolynomialPairing

end KaplanskyCounterexample
end

end OAI
