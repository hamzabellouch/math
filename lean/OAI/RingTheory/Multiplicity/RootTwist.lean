import Mathlib
import OAI.RingTheory.Multiplicity.RootRestriction

namespace OAI

noncomputable section
namespace Lech.ProjectiveRoot
open MvPolynomial HomogeneousLocalization ProductSourceCover
universe u
variable (R : Type u) [CommRing R] (n : ℕ)
attribute [local instance] MvPolynomial.gradedAlgebra

lemma coefficient_grid_mem (k : Fin (n+1))
    (s : Finset (Fin (n+1))) (t : Finset (Chart n)) :
    (targetUnit R n k : GridAmbient R n) ∈ grid R n (fun _ => 1) s t := by
  refine ⟨0,targetCoeff R n k,?_,?_⟩
  · change targetCoeff R n k ∈ ringSections R n (fun _ => 1 + (0:ℤ)*(s.card:ℤ)) t
    simpa only [zero_mul,add_zero] using ringSections_mono R n (fun _ => 1)
      (Finset.empty_subset t) (coefficient_mem R n k)
  · rw [pow_zero,one_mul,targetUnit_val]

lemma coefficient_inverse_grid_mem (k : Fin (n+1))
    (s : Finset (Fin (n+1))) (hk : k ∈ s) (t : Finset (Chart n)) :
    (↑((targetUnit R n k)⁻¹) : GridAmbient R n) ∈ grid R n (fun _ => -1) s t := by
  refine ⟨1,denominator R n (s.erase k),?_,?_⟩
  · have hdeg : (fun _ : Fin n => ((s.erase k).card : ℤ)) =
        levelTwist n (fun _ => -1) s.card 1 := by
      ext i
      simp only [levelTwist,Int.natCast_one,one_mul]
      have hc := Finset.card_erase_add_one hk
      omega
    rw [←hdeg]
    exact ringSections_mono R n _ (Finset.empty_subset t) (coefficient_product_mem R n (s.erase k))
  · have hd : denominator R n s = targetCoeff R n k * denominator R n (s.erase k) :=
      (Finset.mul_prod_erase s (targetCoeff R n) hk).symm
    rw [pow_one,hd,map_mul,←targetUnit_val,mul_right_comm,Units.mul_inv,one_mul]

lemma grid_power_mem (m : Fin n → ℤ) (s : Finset (Fin (n+1))) (t : Finset (Chart n))
    (x : GridAmbient R n) (hx : x ∈ grid R n m s t) (N : ℕ) :
    x^N ∈ grid R n (N • m) s t := by
  induction N with
  | zero => simpa only [pow_zero,zero_smul] using grid_one_mem R n s t
  | succ N ih =>
      simpa only [pow_succ,succ_nsmul] using grid_mul_mem R n (N • m) m s t _ _ ih hx

lemma coefficient_zpow_grid_mem (k : Fin (n+1)) (s : Finset (Fin (n+1)))
    (hk : k ∈ s) (t : Finset (Chart n)) (a : ℤ) :
    ((targetUnit R n k)^a : (GridAmbient R n)ˣ).val ∈ grid R n (fun _ => a) s t := by
  cases a with
  | ofNat N =>
      have hp := grid_power_mem R n (fun _ => 1) s t _ (coefficient_grid_mem R n k s t) N
      change (↑(targetUnit R n k) ^ N : GridAmbient R n) ∈ _
      simpa only [Pi.smul_def,nsmul_eq_mul,mul_one,Int.ofNat_eq_natCast] using hp
  | negSucc N =>
      have hp := grid_power_mem R n (fun _ => -1) s t _
        (coefficient_inverse_grid_mem R n k s hk t) (N+1)
      have he : (N+1) • (fun _ : Fin n => (-1:ℤ)) = fun _ => Int.negSucc N := by
        ext i
        simp only [Pi.smul_apply,nsmul_eq_mul,mul_neg_one]
        omega
      rw [he] at hp
      change (↑(((targetUnit R n k)⁻¹) ^ (N+1)) : GridAmbient R n) ∈ _
      simpa only [Units.val_pow_eq_pow_val] using hp

variable (k : Fin (n+1)) (s : Finset (Fin (n+1))) (hk : k ∈ s) (hs : s.Nonempty)
variable (m l : Fin n → ℤ) (a : ℤ) (hml : ∀ j, l j = m j + a)

include hk hml in
lemma twist_mem (x : GridAmbient R n) (hx : x ∈ grid R n m s ∅) :
    (↑((targetUnit R n k)^a) : GridAmbient R n) * x ∈ grid R n l s ∅ := by
  have he : (fun _ : Fin n => a) + m = l := by ext j; simp only [Pi.add_apply,hml]; ring
  rw [←he]
  exact grid_mul_mem R n _ m s ∅ _ x (coefficient_zpow_grid_mem R n k s hk ∅ a) hx

 

def twistEquiv : Sections R n s hs m ≃ₗ[Ring R n s] Sections R n s hs l where
  toFun x := ⟨_,twist_mem R n k s hk m l a hml x.val x.property⟩
  invFun x := ⟨_,twist_mem R n k s hk l m (-a) (by intro j; rw [hml]; ring) x.val x.property⟩
  left_inv x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^(-a)) : GridAmbient R n) *
      ((↑((targetUnit R n k)^a) : GridAmbient R n) * x.val) = x.val
    rw [←mul_assoc,←Units.val_mul,←zpow_add,neg_add_cancel,zpow_zero,Units.val_one,one_mul]
  right_inv x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^a) : GridAmbient R n) *
      ((↑((targetUnit R n k)^(-a)) : GridAmbient R n) * x.val) = x.val
    rw [←mul_assoc,←Units.val_mul,←zpow_add,add_neg_cancel,zpow_zero,Units.val_one,one_mul]
  map_add' x y := by apply Subtype.ext; exact mul_add _ _ _
  map_smul' b x := by
    apply Subtype.ext
    change (↑((targetUnit R n k)^a) : GridAmbient R n) *
      (scalarMap R n s b * x.val) = scalarMap R n s b * _
    exact mul_left_comm _ _ _

lemma twistEquiv_val (x : Sections R n s hs m) :
    (twistEquiv R n k s hk hs m l a hml x : GridAmbient R n) =
      (↑((targetUnit R n k)^a) : GridAmbient R n) * x := rfl

 

lemma twistEquiv_restriction {t : Finset (Fin (n+1))} (ht : t.Nonempty) (hst : s ⊆ t)
    (x : Sections R n s hs m) :
    sectionsRestriction R n hs ht l hst (twistEquiv R n k s hk hs m l a hml x) =
      twistEquiv R n k t (hst hk) ht m l a hml (sectionsRestriction R n hs ht m hst x) := rfl

end Lech.ProjectiveRoot

end

end OAI
