import Mathlib
import OAI.Topology.ArtinGroups.Quivers.OrthogonalVertices
import OAI.Topology.ArtinGroups.Quivers.ExtArrow
import OAI.Topology.ArtinGroups.Harmonic.FusionLabel

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E)

abbrev FusionVertex := V × FusionLabel m

abbrev FusionQuiverArrow := Σ st : FusionVertex (V := V) m × FusionVertex (V := V) m,
  Fin ((d st.1.1 st.2.1).multiplicity m st.1.2 st.2.2)

noncomputable def fusionArrowReverse (hd : ∀ s t, d s t = d t s) :
    FusionQuiverArrow m d → FusionQuiverArrow m d := fun a =>
  ⟨(a.1.2,a.1.1), Fin.cast (by rw [hd a.1.1.1 a.1.2.1, FusionEdge.multiplicity_symm]) a.2⟩

omit [Fintype V] [DecidableEq V] in
lemma fusionArrowReverse_twice (hd : ∀ s t, d s t = d t s) (a : FusionQuiverArrow m d) :
    fusionArrowReverse m d hd (fusionArrowReverse m d hd a) = a := by
  rcases a with ⟨⟨α,β⟩,k⟩
  rfl

noncomputable def fusionQuiver (hd : ∀ s t, d s t = d t s) :
    ReversibleQuiver (FusionVertex (V := V) m) (FusionQuiverArrow m d) where
  source a := a.1.1
  target a := a.1.2
  reverse :=
    { toFun := fusionArrowReverse m d hd
      invFun := fusionArrowReverse m d hd
      left_inv := fusionArrowReverse_twice m d hd
      right_inv := fusionArrowReverse_twice m d hd }
  reverse_reverse := fusionArrowReverse_twice m d hd
  source_reverse _ := rfl
  target_reverse _ := rfl

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_no_loops (hd : ∀ s t, d s t = d t s)
    (hdiag : ∀ s, d s s = .units 0) :
    ∀ a, (fusionQuiver m d hd).source a ≠ (fusionQuiver m d hd).target a := by
  rintro ⟨⟨α,β⟩,k⟩ h
  change α = β at h
  subst β
  have hk := k.isLt
  simp only [hdiag, FusionEdge.multiplicity, ite_true] at hk
  omega

noncomputable def fusionArrowAtEquiv (hd : ∀ s t, d s t = d t s)
    (α β : FusionVertex (V := V) m) :
    {a : FusionQuiverArrow m d // (fusionQuiver m d hd).source a = α ∧
      (fusionQuiver m d hd).target a = β} ≃
      Fin ((d α.1 β.1).multiplicity m α.2 β.2) where
  toFun a := Fin.cast (congrArg₂ (fun (i j : FusionVertex (V := V) m) =>
    (d i.1 j.1).multiplicity m i.2 j.2) a.property.1 a.property.2) a.val.2
  invFun k := ⟨⟨(α,β),k⟩,rfl,rfl⟩
  left_inv := by
    rintro ⟨⟨⟨α',β'⟩,k⟩,hα,hβ⟩
    change α'=α at hα
    change β'=β at hβ
    subst α'; subst β'; rfl
  right_inv _ := rfl

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_arrow_count (hd : ∀ s t, d s t = d t s)
    (α β : FusionVertex (V := V) m) :
    Nat.card {a : FusionQuiverArrow m d // (fusionQuiver m d hd).source a = α ∧
      (fusionQuiver m d hd).target a = β} = (d α.1 β.1).multiplicity m α.2 β.2 := by
  rw [Nat.card_congr (fusionArrowAtEquiv m d hd α β), Nat.card_fin]

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_same_color (hd : ∀ s t, d s t = d t s)
    (hdiag : ∀ s, d s s = .units 0) (s : V) (L L' : FusionLabel m) (h : L ≠ L') :
    ReversibleQuiver.Zigzag.OrthogonalVertices (fusionQuiver m d hd) (s,L) (s,L') := by
  constructor
  · exact fun hh => h (congrArg Prod.snd hh)
  · intro a ha hb
    have hk := a.2.isLt
    change a.1.1 = (s,L) at ha
    change a.1.2 = (s,L') at hb
    simp only [ha,hb,hdiag,FusionEdge.multiplicity, ite_eq_right h] at hk
    omega

end HarmonicArtin

end OAI
