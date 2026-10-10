import Mathlib
import OAI.Topology.ArtinGroups.Complexes.LevelArrayComplexMinimal
import OAI.Topology.ArtinGroups.Quivers.ClosedNeighborhood

namespace OAI

namespace HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex
universe u
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V A:Type u} {K:Type*} (Q:ReversibleQuiver V A)
  [Field K] [Fintype A] [DecidableEq V]

lemma classLevelArray_minimal_apply (x:FiniteHomotopyClass Q (K:=K)) (α:V) (k:ℤ) :
    classLevelArray Q x (α,k)=Nat.card {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=k} := by
  have h:=classLevelArray_complex_minimal Q (minimalClassModel Q x).complex
    (minimalClassModel_minimal Q x)
  have hx:classOfComplex Q (minimalClassModel Q x).complex=x:=minimalClassModel_class Q x
  rw [hx] at h
  rw [h,levelArray_apply]

lemma classCapOn_iff_level_zero (x:FiniteHomotopyClass Q (K:=K)) (U:Set V) (q:ℤ) :
    ClassCapOn Q x U q ↔ ∀ α∈U,∀ k,q<k→classLevelArray Q x (α,k)=0 := by
  constructor
  · intro h α hα k hk
    rw [classLevelArray_minimal_apply]
    let :IsEmpty {i:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement i).color=α ∧
      ((minimalClassModel Q x).complex.placement i).level=k}:=⟨by
        rintro ⟨i,hi,he⟩
        have hh:=h i (hi ▸ hα)
        omega⟩
    exact Nat.card_of_isEmpty
  · intro h i hi
    by_contra hn
    have hh:=h _ hi _ (lt_of_not_ge hn)
    rw [classLevelArray_minimal_apply] at hh
    have hp:0<Nat.card {j:(minimalClassModel Q x).Index //
      ((minimalClassModel Q x).complex.placement j).color=
        ((minimalClassModel Q x).complex.placement i).color ∧
      ((minimalClassModel Q x).complex.placement j).level=
        ((minimalClassModel Q x).complex.placement i).level} := by
      let :Nonempty {j:(minimalClassModel Q x).Index //
        ((minimalClassModel Q x).complex.placement j).color=
          ((minimalClassModel Q x).complex.placement i).color ∧
        ((minimalClassModel Q x).complex.placement j).level=
          ((minimalClassModel Q x).complex.placement i).level}:=⟨⟨i,rfl,rfl⟩⟩
      exact Nat.card_pos
    omega

lemma classCapOn_of_level_eq {x y:FiniteHomotopyClass Q (K:=K)} (U:Set V) (q:ℤ)
    (he:∀ α∈U,∀ k,classLevelArray Q y (α,k)=classLevelArray Q x (α,k))
    (hx:ClassCapOn Q x U q) : ClassCapOn Q y U q := by
  rw [classCapOn_iff_level_zero] at hx ⊢
  intro α hα k hk
  rw [he α hα k]
  exact hx α hα k hk

lemma classLayerTopDimension_below (x:FiniteHomotopyClass Q (K:=K)) (b k:ℤ)
    (hb:ClassLowerBound Q b x) (hk:k<b) (α:V) (c:ℤ) :
    classLayerTopDimension Q k α c x=0 := by
  change Module.finrank K (coefficientTopDual Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c)=0
  have hz:coefficientTopDual Q
      ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c=⊥ := by
    apply eq_bot_iff.mpr
    intro functional _
    change functional=0
    funext i
    have hi:=hb i
    have he:=i.property
    change ((minimalClassModel Q x).complex.placement i.val).level=k at he
    omega
  rw [hz,finrank_bot]

lemma classLayerSocleDimension_below (x:FiniteHomotopyClass Q (K:=K)) (b k:ℤ)
    (hb:ClassLowerBound Q b x) (hk:k<b) (α:V) (c:ℤ) :
    classLayerSocleDimension Q k α c x=0 := by
  change Module.finrank K (coefficientSocle Q
    ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c)=0
  have hz:coefficientSocle Q
      ((minimalClassModel Q x).complex.pureLayer Q (minimalClassModel_minimal Q x) k) α c=⊥ := by
    apply eq_bot_iff.mpr
    intro functional _
    change functional=0
    funext i
    have hi:=hb i
    have he:=i.property
    change ((minimalClassModel Q x).complex.placement i.val).level=k at he
    omega
  rw [hz,finrank_bot]

lemma finiteFamily_lowerBound {R:Type*} [Finite R]
    (x:R→FiniteHomotopyClass Q (K:=K)) : ∃ b:ℤ,∀ r,ClassLowerBound Q b (x r) := by
  obtain ⟨b,hb⟩:=Finite.exists_ge
    (fun z:Σ r:R,(minimalClassModel Q (x r)).Index=>
      ((minimalClassModel Q (x z.1)).complex.placement z.2).level)
  exact ⟨b,fun r i=>hb ⟨r,i⟩⟩

end HarmonicArtin.ReversibleQuiver.Zigzag.BasedComplex

end OAI
