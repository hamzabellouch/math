import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.HarmonicExtension
import OAI.Topology.ArtinGroups.Harmonic.FusionFold

namespace OAI

namespace HarmonicArtin

variable {S : Type*} [LinearOrder S]

abbrev FiniteFusionEdge (M : CoxeterMatrix S) :=
  {st : S × S // st.1 < st.2 ∧ 4 ≤ M st.1 st.2}

def fusionLabelSize (M : CoxeterMatrix S) (e : FiniteFusionEdge M) : ℕ := M e.val.1 e.val.2

lemma fusionLabelSize_ge_four (M : CoxeterMatrix S) (e : FiniteFusionEdge M) :
    4 ≤ fusionLabelSize M e := e.property.2

noncomputable def sortedFusionEdge (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) : FiniteFusionEdge M :=
  if h : s<t then ⟨(s,t), h, hm⟩ else
    ⟨(t,s), lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hst), by simpa only [M.symmetric t s] using hm⟩

lemma sortedFusionEdge_size (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) :
    fusionLabelSize M (sortedFusionEdge M s t hst hm) = M s t := by
  unfold sortedFusionEdge
  split_ifs <;> simp only [fusionLabelSize, M.symmetric t s]

lemma sortedFusionEdge_symm (M : CoxeterMatrix S) (s t : S)
    (hst : s ≠ t) (hm : 4 ≤ M s t) (hmt : 4 ≤ M t s) :
    sortedFusionEdge M s t hst hm = sortedFusionEdge M t s hst.symm hmt := by
  apply Subtype.ext
  unfold sortedFusionEdge
  by_cases h : s < t
  · have ht : ¬t < s := not_lt.mpr (le_of_lt h)
    simp only [dite_eq_left h, dite_eq_right ht]
  · have ht : t < s := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hst)
    simp only [dite_eq_right h, dite_eq_left ht]

noncomputable def coxeterFusionEdge (M : CoxeterMatrix S) :
    (S ⊕ Unit) → (S ⊕ Unit) → FusionEdge (FiniteFusionEdge M)
  | .inl s, .inl t =>
    if hst : s=t then .units 0 else
    if h0 : M s t=0 then .units 2 else
    if h2 : M s t=2 then .units 0 else
    if h3 : M s t=3 then .units 1 else
      .string (sortedFusionEdge M s t hst (by have := M.off_diagonal s t hst; omega))
  | .inl _, .inr _ => .units 1
  | .inr _, .inl _ => .units 1
  | .inr _, .inr _ => .units 0

lemma coxeterFusionEdge_symm (M : CoxeterMatrix S) (s t : S ⊕ Unit) :
    coxeterFusionEdge M s t = coxeterFusionEdge M t s := by
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      by_cases hst : s=t
      · subst t; rfl
      by_cases h0 : M s t=0
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h0, ← M.symmetric s t, ↓reduceDIte]
      by_cases h2 : M s t=2
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h2, ← M.symmetric s t, ↓reduceDIte]
      by_cases h3 : M s t=3
      · simp only [coxeterFusionEdge, hst, Ne.symm hst, h3, ← M.symmetric s t, ↓reduceDIte]
      simp only [coxeterFusionEdge, hst, Ne.symm hst, h0, h2, h3, ← M.symmetric s t, ↓reduceDIte]
      congr 1
      exact sortedFusionEdge_symm M s t hst _ _
    | inr t => rfl
  | inr s => cases t <;> rfl

lemma coxeterFusionEdge_diag (M : CoxeterMatrix S) (s : S ⊕ Unit) :
    coxeterFusionEdge M s s = .units 0 := by
  cases s <;> simp [coxeterFusionEdge]

lemma fusionFoldedCartan_eq_framedCartan (M : CoxeterMatrix S) :
    fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) = framedCartan M := by
  ext s t
  simp only [fusionFoldedCartan, Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply]
  cases s with
  | inl s =>
    cases t with
    | inl t =>
      by_cases hst : s=t
      · subst t; simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
      have hSum : (Sum.inl s : S ⊕ Unit) ≠ Sum.inl t := by simpa only [ne_eq, Sum.inl.injEq] using hst
      simp only [ite_eq_right hSum, zero_sub, framedCartan, ite_eq_right hst]
      by_cases h0 : M s t=0
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      by_cases h2 : M s t=2
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      by_cases h3 : M s t=3
      · simp_all [coxeterFusionEdge, FusionEdge.dimension]
      simp only [coxeterFusionEdge, hst, h0, h2, h3, ↓reduceDIte, ↓reduceIte, FusionEdge.dimension,
        sortedFusionEdge_size]
      ring
    | inr t => simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
  | inr s =>
    cases t with
    | inl t => simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]
    | inr t => cases s; cases t; simp [coxeterFusionEdge, framedCartan, FusionEdge.dimension]

end HarmonicArtin

end OAI
