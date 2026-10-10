import Mathlib
import OAI.RingTheory.Multiplicity.ProductSourceCoverRootSigned

namespace OAI

noncomputable section
namespace Lech.ProductSourceCover
open scoped BigOperators

def rootPrefix (n : ℕ) (r : Fin n → ℤ) (h s N : ℕ) : ℝ :=
  ∑ l∈Finset.range N,∏ j,((l:ℝ)-(h:ℝ)*(s:ℝ)-(r j:ℝ))

lemma rootPrefix_split (n : ℕ) (r : Fin n → ℤ) (h s k : ℕ) (hk : k≤h) :
    rootPrefix n r h s (k*s)+rootStripPolynomial n r (h-k) s=rootStripPolynomial n r h s := by
  unfold rootPrefix rootStripPolynomial
  rw [show h*s=k*s+(h-k)*s by rw [←Nat.add_mul]; congr 1; omega,Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  apply Finset.prod_congr rfl
  intro j hj
  rw [Nat.cast_sub hk]
  push_cast
  ring

lemma signed_reverse (h : ℕ) (b : ℤ → ℝ) (f : ℕ → ℝ) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*f (h-k))=
      ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*f i := by
  rw [Finset.mul_sum,←Finset.sum_range_reflect
    (fun i => (-1:ℝ)^i*b (-(i:ℤ))*f i) (h+1)]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k≤h := by have := Finset.mem_range.mp hk; omega
  have he : h+1-1-k=h-k := by omega
  rw [he]
  have hp : -(h:ℤ)+(k:ℤ) = -((h-k:ℕ):ℤ) := by omega
  have hs : (-1:ℝ)^h*(-1:ℝ)^k=(-1:ℝ)^(h-k) := by
    conv_lhs => rw [show h=(h-k)+k by omega,pow_add]
    have hsq : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [←mul_pow]; norm_num
    rw [mul_assoc,hsq,mul_one]
  rw [hp,←mul_assoc,←mul_assoc,hs]

lemma rank_reverse_zero (h : ℕ) (b : ℤ → ℝ)
    (hb : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)=0) :
    ∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))=0 := by
  have he := signed_reverse h b (fun _=>1)
  simpa only [mul_one,hb,mul_zero] using he.symm

lemma complement_euler (n : ℕ) (r : Fin n → ℤ) (h s : ℕ) (b : ℤ → ℝ)
    (hb : ∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)=0) :
    (-1:ℝ)^h*(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*
      rootPrefix n r h s (k*s))=
        -(∑ i∈Finset.range (h+1),(-1:ℝ)^i*b (-(i:ℤ))*rootStripPolynomial n r i s) := by
  have he : (∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*rootPrefix n r h s (k*s))=
      -(∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*rootStripPolynomial n r (h-k) s) := by
    calc
      _=∑ k∈Finset.range (h+1),(-1:ℝ)^k*b (-(h:ℤ)+k)*
          (rootStripPolynomial n r h s-rootStripPolynomial n r (h-k) s) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [eq_sub_iff_add_eq.mpr (rootPrefix_split n r h s k (by have := Finset.mem_range.mp hk; omega))]
      _=_ := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib,←Finset.sum_mul,hb,zero_mul,zero_sub]
  rw [he,mul_neg]
  exact congrArg Neg.neg (signed_reverse h b (fun i => rootStripPolynomial n r i s))
end Lech.ProductSourceCover

end

end OAI
