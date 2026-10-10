import Mathlib
import OAI.Topology.ArtinGroups.Complexes.HomPath
import OAI.Topology.ArtinGroups.Complexes.HomInternalSupport

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
variable {V A K : Type*} (Q : ReversibleQuiver V A) [Field K]
  [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]
variable {I J : Type*} [Fintype I] [Fintype J]

abbrev CornerPath (E : BasedComplex Q (K := K) I) (F : BasedComplex Q (K := K) J) (r : ℤ) :=
  {t : I × J × Path V A //
    Path.source Q t.2.2 = (E.placement t.1).color ∧
    Path.target Q t.2.2 = (F.placement t.2.1).color ∧ Path.length t.2.2 = r}

noncomputable def purePathForget (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) →
      CornerPath Q E F r := fun x => ⟨x.2.val, x.2.property.1, x.2.property.2.1, by
        have hh := x.2.property.2.2
        have he := hE x.2.val.1
        have hf := hF x.2.val.2.1
        dsimp only [GeneratorPlacement.level] at he hf
        omega⟩

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_injective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Injective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨a,ha⟩,⟨ta,hta⟩⟩ ⟨⟨b,hb⟩,⟨tb,htb⟩⟩ hh
  have ht : ta=tb := congrArg Subtype.val hh
  subst tb
  have hab : a=b := by
    have h₁ := hta.2.2.2
    have h₂ := htb.2.2.2
    dsimp only at h₁ h₂
    omega
  subst b
  rfl

omit [Fintype V] [DecidableEq A] in
lemma purePathForget_surjective (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    Function.Surjective (purePathForget Q E F hE hF r) := by
  rintro ⟨⟨i,j,p⟩,hpt⟩
  let v := (F.placement j).internal - (E.placement i).internal + Path.length p
  have hv : v ∈ homInternalSupport Q E F := by
    rw [mem_homInternalSupport]
    rcases p with p | p | p
    · exact ⟨i,j,0,rfl⟩
    · exact ⟨i,j,1,rfl⟩
    · exact ⟨i,j,2,rfl⟩
  refine ⟨⟨⟨v,hv⟩, ⟨(i,j,p),hpt.1,hpt.2.1,?_,?check⟩⟩, rfl⟩
  · have he := hE i
    have hf := hF j
    have hp := hpt.2.2
    dsimp only [GeneratorPlacement.level] at he hf
    dsimp only at hp ⊢
    dsimp only [v]
    omega
  case check =>
    dsimp only [v]
    omega

noncomputable def purePathEquiv (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    (Σ v : {v // v ∈ homInternalSupport Q E F}, HomPath Q E F (k-l+r-v.val) v.val) ≃
      CornerPath Q E F r := Equiv.ofBijective (purePathForget Q E F hE hF r)
        ⟨purePathForget_injective Q E F hE hF r, purePathForget_surjective Q E F hE hF r⟩

lemma totalChainDimension_eq_card (E : BasedComplex Q (K := K) I)
    (F : BasedComplex Q (K := K) J) {l k : ℤ}
    (hE : ∀ i, (E.placement i).level = l) (hF : ∀ j, (F.placement j).level = k) (r : ℤ) :
    totalChainDimension Q E F (k-l+r) = Nat.card (CornerPath Q E F r) := by
  classical
  unfold totalChainDimension
  simp_rw [homSpace_finrank, Nat.card_eq_fintype_card]
  rw [← Finset.sum_coe_sort, ← Fintype.card_sigma]
  exact Fintype.card_congr (purePathEquiv Q E F hE hF r)

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
