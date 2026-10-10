import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.ColumnCertificates
import OAI.RepresentationTheory.UniversalSquare.Support.NumericalSupport

namespace OAI

/-! Factored Certificates. -/

section

namespace Saxl.Columns

def integralWedge (r : ℕ) (L : ℕ → Fin r → ℤ) : ℤ :=
  ∑ π : Equiv.Perm (Fin r), (Equiv.Perm.sign π : ℤ) * ∏ i, L (π i).val i

def integralBlocks : (rs : List ℕ) → (ℕ → Fin rs.sum → ℤ) → ℤ
  | [], _ => 1
  | r :: rs, L => integralWedge r (fun a i => L a (Fin.castAdd rs.sum i)) *
      integralBlocks rs (fun a i => L a (Fin.natAdd r i))

lemma integralBlocks_eq (rs : List ℕ) (L : ℕ → Fin rs.sum → ℤ) :
    integralBlocks rs L = ∑ π : Perms rs, sgInteger π *
      ∏ i, L (row (perm π (enumerate rs i))) i := by
  induction rs with
  | nil =>
    change 1 = ∑ π : PUnit, sgInteger (rs := []) π * ∏ i : Fin 0,
      L (row (perm (rs := []) π (enumerate [] i))) i
    simp [sgInteger]
  | cons r rs ih =>
    change ℕ → Fin (r + rs.sum) → ℤ at L
    simp only [integralBlocks, ih, integralWedge, Perms, Fintype.sum_prod_type,
      sgInteger, Finset.sum_mul_sum, List.sum_cons]
    apply Finset.sum_congr rfl
    intro π hπ
    apply Finset.sum_congr rfl
    intro σ hσ
    have hprod : (∏ i : Fin (r + rs.sum), L (row (perm (rs := r::rs) (π,σ)
        (enumerate (r::rs) i))) i) =
        (∏ i : Fin r, L (row (perm (rs := r::rs) (π,σ)
          (enumerate (r::rs) (Fin.castAdd rs.sum i)))) (Fin.castAdd rs.sum i)) *
        ∏ i : Fin rs.sum, L (row (perm (rs := r::rs) (π,σ)
          (enumerate (r::rs) (Fin.natAdd r i)))) (Fin.natAdd r i) :=
      Fin.prod_univ_add _
    erw [hprod]
    have hl : (∏ i : Fin r, L (row (perm (rs := r::rs) (π,σ)
        (enumerate (r::rs) (Fin.castAdd rs.sum i)))) (Fin.castAdd rs.sum i)) =
        ∏ i : Fin r, L (π i).val (Fin.castAdd rs.sum i) := by
      apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_left r rs i]
      rfl
    have hr : (∏ i : Fin rs.sum, L (row (perm (rs := r::rs) (π,σ)
        (enumerate (r::rs) (Fin.natAdd r i)))) (Fin.natAdd r i)) =
        ∏ i : Fin rs.sum, L (row (perm σ (enumerate rs i))) (Fin.natAdd r i) := by
      apply Finset.prod_congr rfl
      intro i hi
      erw [enumerate_right r rs i]
      rfl
    erw [hl, hr]
    ring_nf
    rfl

def factoredContraction {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) : ℤ :=
  ∑ σ : Perms rsA, ∑ τ : Perms rsB, sgInteger σ * sgInteger τ *
    integralBlocks rsT (fun r i =>
      L r (row (perm σ (enumerate rsA (ea (et.symm i)))))
        (row (perm τ (enumerate rsB (eb (et.symm i))))))

lemma contractionInteger_eq_factored {n : ℕ} (rsA rsB rsT : List ℕ)
    (ea : Fin n ≃ Fin rsA.sum) (eb : Fin n ≃ Fin rsB.sum) (et : Fin n ≃ Fin rsT.sum)
    (L : ℕ → ℕ → ℕ → ℤ) :
    contractionInteger rsA rsB rsT ea eb et L =
      factoredContraction rsA rsB rsT ea eb et L := by
  unfold contractionInteger factoredContraction
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [integralBlocks_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π hπ
  have he : (∏ i, L (row (perm π (enumerate rsT (et i))))
      (row (perm σ (enumerate rsA (ea i))))
      (row (perm τ (enumerate rsB (eb i))))) =
      ∏ i, L (row (perm π (enumerate rsT i)))
        (row (perm σ (enumerate rsA (ea (et.symm i)))))
        (row (perm τ (enumerate rsB (eb (et.symm i))))) := by
    apply Fintype.prod_equiv et
    intro i
    simp only [Equiv.symm_apply_apply]
  rw [he]
  ring

end Saxl.Columns
end

end OAI
