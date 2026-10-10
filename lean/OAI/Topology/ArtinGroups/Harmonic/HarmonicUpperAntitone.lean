import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.HarmonicExtension

namespace OAI

namespace HarmonicArtin
open Matrix

theorem harmonic_upper_antitone {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (hOff:∀i j,i≠j→C i j≤0) (U:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hExt:∀i∉U,q i=p i) (hHarm:∀i:U,(C *ᵥ q) i=0)
    (hrow:∀i:U,0≤(C *ᵥ p) i) : q≤p := by
  classical
  have hv:∀i:U,0≤((C.submatrix Subtype.val Subtype.val:Matrix U U ℝ)⁻¹ *ᵥ
      (fun i:U=>(C *ᵥ p) i)) i :=
    harmonic_extension_nonneg _ hU
      (fun i j hij=>hOff i j (fun he=>hij (Subtype.ext he))) _ hrow
  have hc:=harmonic_upper_change C U hU p q hExt hHarm
  intro i
  by_cases hi:i∈U
  · have hh:=congrFun hc ⟨i,hi⟩
    have hh0:=hv ⟨i,hi⟩
    simp only [Pi.neg_apply] at hh
    linarith
  · exact le_of_eq (hExt i hi)

theorem harmonic_upper_monotone {ι:Type*} [Fintype ι]
    (C:Matrix ι ι ℝ) (hOff:∀i j,i≠j→C i j≤0) (U:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hExt:∀i∉U,q i=p i) (hHarm:∀i:U,(C *ᵥ q) i=0)
    (hrow:∀i:U,(C *ᵥ p) i≤0) : p≤q := by
  have h:=harmonic_upper_antitone C hOff U hU (-p) (-q)
    (fun i hi=>by simp only [Pi.neg_apply,hExt i hi])
    (fun i=>by rw [Matrix.mulVec_neg]; simp only [Pi.neg_apply,hHarm i,neg_zero])
    (fun i=>by rw [Matrix.mulVec_neg]; exact neg_nonneg.mpr (hrow i))
  intro i
  exact neg_le_neg_iff.mp (h i)

lemma harmonic_sum_lt_of_lt {ι:Type*} [Fintype ι] (p q:ι→ℝ)
    (h:p≤q) (hne:p≠q) : (∑i,p i)<∑i,q i := by
  classical
  apply Finset.sum_lt_sum (fun i _=>h i)
  by_contra hn
  apply hne
  funext i
  exact le_antisymm (h i) (le_of_not_gt (fun hi=>hn ⟨i,Finset.mem_univ _,hi⟩))

end HarmonicArtin

end OAI
