import Mathlib
import OAI.Topology.ArtinGroups.Complexes.PureTotalHomEuler
import OAI.Topology.ArtinGroups.Complexes.CornerPath

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev EqualColorPair (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :=
  {ij : I × J // (E.placement ij.1).color = (F.placement ij.2).color}

abbrev ArrowPair (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) :=
  {t : I × J × A // Q.source t.2.2 = (E.placement t.1).color ∧
    Q.target t.2.2 = (F.placement t.2.1).color}

noncomputable def zeroCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 0 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · exact hs.symm.trans ht
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inl (E.placement x.val.1).color),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · dsimp only [Path.source] at hs
      subst p
      rfl
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

noncomputable def tokenCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 2 ≃ EqualColorPair Q E F where
  toFun x := ⟨(x.val.1,x.val.2.1), by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · exact hs.symm.trans ht⟩
  invFun x := ⟨(x.val.1,x.val.2,Sum.inr (Sum.inr (E.placement x.val.1).color)),rfl,x.property,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    dsimp only
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · simp only [Path.length] at hl; omega
    · dsimp only [Path.source] at hs
      subst p
      rfl
  right_inv x := by rfl

noncomputable def arrowCornerEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) : CornerPath Q E F 1 ≃ ArrowPair Q E F where
  toFun x := by
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · exact ⟨(i,j,p),hs,ht⟩
    · simp only [Path.length] at hl; omega
  invFun x := ⟨(x.val.1,x.val.2.1,Sum.inr (Sum.inl x.val.2.2)),x.property.1,x.property.2,rfl⟩
  left_inv x := by
    apply Subtype.ext
    rcases x with ⟨⟨i,j,p⟩,hs,ht,hl⟩
    rcases p with p | p | p
    · simp only [Path.length] at hl; omega
    · rfl
    · simp only [Path.length] at hl; omega
  right_inv x := by rfl

lemma pure_generator_euler (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) :
    2 * Nat.card (EqualColorPair Q E F) + totalHomDimension Q E F (k-l+1) =
      Nat.card (ArrowPair Q E F) + totalHomDimension Q E F (k-l) +
        totalHomDimension Q F E (l-k) := by
  have hh := pure_total_hom_euler Q E F hE hF
  have h₀ := totalChainDimension_eq_card Q E F hE hF 0
  have h₁ := totalChainDimension_eq_card Q E F hE hF 1
  have h₂ := totalChainDimension_eq_card Q E F hE hF 2
  rw [Nat.card_congr (zeroCornerEquiv Q E F)] at h₀
  rw [Nat.card_congr (arrowCornerEquiv Q E F)] at h₁
  rw [Nat.card_congr (tokenCornerEquiv Q E F)] at h₂
  simp only [add_zero] at h₀
  rw [h₀,h₁,h₂] at hh
  omega

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
