import Mathlib
import OAI.Topology.ArtinGroups.Quivers.ReversibleQuiver

namespace OAI

namespace HarmonicArtin.GaussianCancellation

variable {R : Type*} [Ring R]

def cornerRemainder (e d h : R) : R := e - d * h - h * d

variable (e d h : R)
  (hee : e * e = e) (hed : e * d = d) (hde : d * e = d)
  (heh : e * h = h) (hhe : h * e = h)
  (hd : d * d = 0) (hh : h * h = 0) (hhdh : h * d * h = h)

include hed hd in
lemma cornerRemainder_mul_d : cornerRemainder e d h * d = d - d * h * d := by
  simp only [cornerRemainder, sub_mul, hed, mul_assoc, hd, mul_zero, sub_zero]

include hde hd in
lemma d_mul_cornerRemainder : d * cornerRemainder e d h = d - d * h * d := by
  simp only [cornerRemainder, mul_sub, hde, ← mul_assoc, hd, zero_mul, sub_zero]

include hed hde hd in
lemma cornerRemainder_commutes :
    cornerRemainder e d h * d = d * cornerRemainder e d h := by
  rw [cornerRemainder_mul_d e d h hed hd, d_mul_cornerRemainder e d h hde hd]

include hhe hh hhdh in
lemma h_mul_cornerRemainder : h * cornerRemainder e d h = 0 := by
  simp only [cornerRemainder, mul_sub, hhe, ← mul_assoc, hh, zero_mul, hhdh]
  abel

include heh hh hhdh in
lemma cornerRemainder_mul_h : cornerRemainder e d h * h = 0 := by
  have hdsh : d * h * h = 0 := by rw [mul_assoc, hh, mul_zero]
  simp only [cornerRemainder, sub_mul, heh, hdsh, hhdh]
  abel

include hee hed heh in
lemma e_mul_cornerRemainder : e * cornerRemainder e d h = cornerRemainder e d h := by
  simp only [cornerRemainder, mul_sub, hee, ← mul_assoc, hed, heh]

include hee hde hhe in
lemma cornerRemainder_mul_e : cornerRemainder e d h * e = cornerRemainder e d h := by
  simp only [cornerRemainder, sub_mul, hee, mul_assoc, hde, hhe]

include hee hed hde heh hhe hd hh hhdh in
lemma cornerRemainder_idempotent :
    cornerRemainder e d h * cornerRemainder e d h = cornerRemainder e d h := by
  calc
    cornerRemainder e d h * cornerRemainder e d h =
      e * cornerRemainder e d h - d * (h * cornerRemainder e d h) -
        h * (d * cornerRemainder e d h) := by
      conv_lhs => lhs; unfold cornerRemainder
      noncomm_ring
    _ = cornerRemainder e d h := by
      rw [e_mul_cornerRemainder e d h hee hed heh,
        h_mul_cornerRemainder e d h hhe hh hhdh, mul_zero, sub_zero,
        ← cornerRemainder_commutes e d h hed hde hd, ← mul_assoc,
        h_mul_cornerRemainder e d h hhe hh hhdh, zero_mul, sub_zero]

include hed hde hd in
lemma cornerReduced_square :
    (cornerRemainder e d h * d) * (cornerRemainder e d h * d) = 0 := by
  rw [mul_assoc, ← mul_assoc d, ← cornerRemainder_commutes e d h hed hde hd,
    mul_assoc _ d d, hd, mul_zero, mul_zero]

lemma cornerRemainder_homotopy :
    cornerRemainder e d h = e + (d * (-h) + (-h) * d) := by
  simp only [cornerRemainder, mul_neg, neg_mul]
  abel

end HarmonicArtin.GaussianCancellation

end OAI
