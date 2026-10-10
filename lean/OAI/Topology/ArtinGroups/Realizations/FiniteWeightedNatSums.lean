import Mathlib

namespace OAI

namespace HarmonicArtin
open scoped BigOperators

theorem finite_weighted_nat_sums {ι:Type*} [Fintype ι]
    (w:ι→ℝ) (hw:∀ i,0<w i) (B:ℝ) :
    {x:ℝ | x≤B ∧ ∃ n:ι→ℕ,x=∑ i,w i*(n i:ℝ)}.Finite := by
  classical
  choose N hN using fun i=>exists_nat_gt (B / w i)
  have hfinite : {n:ι→ℕ | ∀ i,n i≤N i}.Finite := by
    exact (Set.finite_Iic N)
  apply (hfinite.image (fun n:ι→ℕ=>∑ i,w i*(n i:ℝ))).subset
  rintro x ⟨hB,n,rfl⟩
  refine ⟨n,?_,rfl⟩
  intro i
  have hs:w i*(n i:ℝ)≤∑ j,w j*(n j:ℝ) :=
    Finset.single_le_sum (fun j _=>mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
  have hn:(n i:ℝ)≤B/w i := (le_div_iff₀ (hw i)).mpr (by simpa [mul_comm] using hs.trans hB)
  exact_mod_cast (hn.trans (hN i).le)

theorem finite_normalized_weighted_nat_sums {ι:Type*} [Fintype ι]
    (w:ι→ℝ) (hw:∀ i,0<w i) (a:ℝ) (ha:0<a) (B:ℝ) :
    {x:ℝ | x≤B ∧ ∃ n:ι→ℕ,x=(∑ i,w i*(n i:ℝ))/a}.Finite := by
  have h:=finite_weighted_nat_sums (fun i=>w i/a) (fun i=>div_pos (hw i) ha) B
  convert h using 1
  ext x
  simp only [Set.mem_ofPred_eq]
  apply and_congr_right
  intro hx
  apply exists_congr
  intro n
  have he : (∑ i,w i*(n i:ℝ))/a=∑ i,w i/a*(n i:ℝ) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [he]

end HarmonicArtin

end OAI
