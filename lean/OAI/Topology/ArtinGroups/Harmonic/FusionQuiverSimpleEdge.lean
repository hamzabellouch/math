import Mathlib
import OAI.Topology.ArtinGroups.Complexes.UnfoldedPresentation
import OAI.Topology.ArtinGroups.Harmonic.FusionVertex

namespace OAI

namespace HarmonicArtin

variable {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V] [DecidableEq V]
  (m : E → ℕ) (d : V → V → FusionEdge E) (hd : ∀ s t, d s t = d t s)

omit [Fintype V] [DecidableEq V] in
lemma fusionQuiver_orthogonal (α β : FusionVertex (V := V) m) (hne : α ≠ β)
    (h0 : (d α.1 β.1).multiplicity m α.2 β.2 = 0) :
    ReversibleQuiver.Zigzag.OrthogonalVertices (fusionQuiver m d hd) α β := by
  refine ⟨hne, ?_⟩
  intro a hs ht
  change a.1.1 = α at hs
  change a.1.2 = β at ht
  obtain ⟨⟨α',β'⟩, k⟩ := a
  dsimp only at hs ht
  subst α'; subst β'
  have hh := k.isLt
  dsimp only at hh
  exact Nat.not_lt_zero k.val (h0 ▸ hh)

noncomputable def fusionQuiver_simpleEdge (α β : FusionVertex (V := V) m) (hne : α ≠ β)
    (h1 : (d α.1 β.1).multiplicity m α.2 β.2 = 1) :
    ReversibleQuiver.Zigzag.SimpleEdge (fusionQuiver m d hd) α β where
  arrow := ⟨(α,β), ⟨0, by simpa only [h1] using Nat.zero_lt_one⟩⟩
  source := rfl
  target := rfl
  distinct := hne
  unique := by
    rintro ⟨⟨α',β'⟩,k⟩ hs ht
    change α'=α at hs
    change β'=β at ht
    subst α'; subst β'
    congr 1
    apply Fin.ext
    have hh := k.isLt
    dsimp only at hh ⊢
    have hh' : k.val < 1 := h1 ▸ hh
    omega

noncomputable def fusionOrdinaryMatrix : CoxeterMatrix (FusionVertex (V := V) m) where
  M α β := if α=β then 1 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else
    if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0
  isSymm := by
    apply Matrix.ext
    intro α β
    change (if β = α then 1 else if (d β.1 α.1).multiplicity m β.2 α.2 = 0 then 2 else if (d β.1 α.1).multiplicity m β.2 α.2 = 1 then 3 else 0) = (if α = β then 1 else if (d α.1 β.1).multiplicity m α.2 β.2 = 0 then 2 else if (d α.1 β.1).multiplicity m α.2 β.2 = 1 then 3 else 0)
    rw [hd β.1 α.1, FusionEdge.multiplicity_symm m _ β.2 α.2]
    by_cases h : α = β <;> simp only [h, eq_comm, ite_true, ite_false]
  diagonal α := by simp
  off_diagonal α β h := by
    simp only [ite_eq_right h]
    split_ifs <;> norm_num

omit [Fintype V] in
lemma fusionOrdinaryPresentation :
    ReversibleQuiver.Zigzag.BasedComplex.UnfoldedPresentation (fusionQuiver m d hd)
      (fusionOrdinaryMatrix m d hd) := by
  constructor
  intro α β
  by_cases hne : α=β
  · exact Or.inl hne
  by_cases h0 : (d α.1 β.1).multiplicity m α.2 β.2 = 0
  · exact Or.inr (Or.inr (Or.inl ⟨by simp [fusionOrdinaryMatrix, hne,h0],
      fusionQuiver_orthogonal m d hd α β hne h0⟩))
  by_cases h1 : (d α.1 β.1).multiplicity m α.2 β.2 = 1
  · exact Or.inr (Or.inr (Or.inr ⟨by simp [fusionOrdinaryMatrix, hne,h1],
      ⟨fusionQuiver_simpleEdge m d hd α β hne h1⟩⟩))
  exact Or.inr (Or.inl (by simp [fusionOrdinaryMatrix, hne,h0,h1]))

noncomputable def fusionOrdinaryAction {K : Type*} [Field K]
    (hdiag : ∀ s, d s s = .units 0) :
    Artin (fusionOrdinaryMatrix m d hd) →*
      Equiv.Perm (ReversibleQuiver.Zigzag.BasedComplex.FiniteHomotopyClass
        (fusionQuiver m d hd) (K := K)) :=
  ReversibleQuiver.Zigzag.BasedComplex.unfoldedArtinAction (fusionQuiver m d hd)
    (fusionQuiver_no_loops m d hd hdiag) (fusionOrdinaryMatrix m d hd)
    (fusionOrdinaryPresentation m d hd)

end HarmonicArtin

end OAI
