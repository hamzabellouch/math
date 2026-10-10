import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.NeighborhoodProject

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)
local notation "m" => fusionLabelSize M
local notation "Q" => fusionQuiver m (coxeterFusionEdge M) (coxeterFusionEdge_symm M)

omit [Fintype S] [LinearOrder S] in
lemma sourcePositiveComponent_boundary_zero (p:S⊕Unit→ℝ) (hp:∀v,0≤p v)
    (i:S⊕Unit) (hi:0<p i) (v:S⊕Unit) (ho:v∉sourcePositiveComponent M p i)
    (hn:∃u∈sourcePositiveComponent M p i,framedCartan M v u<0) : p v=0 := by
  by_contra hz
  have hv:0<p v:=lt_of_le_of_ne (hp v) (Ne.symm hz)
  obtain ⟨u,hu,huv⟩:=hn
  exact ho (hu.tail ⟨sourcePositiveComponent_positive M p i hi u hu,
    by rwa [framedCartan_symm],hv⟩)

lemma sourceNullSign_image (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) :
    Sum.inl '' {j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}=
      sourcePositiveComponent M (sourceCosetVector M P q) i := by
  ext v
  constructor
  · rintro ⟨j,hj,rfl⟩;exact hj
  · intro hv
    rcases v with j|u
    · exact ⟨j,hv,rfl⟩
    · cases u;exact (hn.2.1 hv).elim

lemma sourceNullSign_peak (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (j:S) (hj:j∈P.val.1)
    (hjI:(.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    sourcePeak M P j=q := by
  apply le_antisymm
  · by_contra h
    have hh:q<sourcePeak M P j:=lt_of_not_ge h
    have hz:=hn.2.2.2 (.inl j) (Or.inl hjI) (sourcePeak M P j) hh
    exact (ne_of_gt (sourcePeak_positive M P j hj)) hz
  · exact sourcePeak_bound M P j q (ne_of_gt (sourcePositiveComponent_positive M _ i hi _ hjI))

lemma sourceNullSign_sign (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    sourceCosetSign M P q v=1 := by
  have he:=sourcePositiveComponent_eq M (sourceCosetVector M P q) v
    (sourcePositiveComponent M (sourceCosetVector M P q) i)
    (sourcePositiveComponent_spec M _ i hi) hv
  have hnv:SourceNullSign M (fun d=>sourceCosetVector M P d) q v:=by
    unfold SourceNullSign
    rw [he]
    exact hn
  change sourceSignAt M _ q v=1
  rw [sourceSignAt,ite_eq_right (ne_of_gt (sourcePositiveComponent_positive M _ i hi v hv)),ite_eq_left hnv]

noncomputable def sourceNullPatch (P:Deligne M) (q:ℕ) (i:S⊕Unit) (v:S⊕Unit) : ℝ :=
  if v∈sourcePositiveComponent M (sourceCosetVector M P q) i then sourceCosetVector M P q v else 0

lemma sourceNullPatch_nonneg (P:Deligne M) (q:ℕ) (i v:S⊕Unit) : 0 ≤ sourceNullPatch M P q i v := by
  unfold sourceNullPatch
  split_ifs
  · exact sourceCosetVector_nonneg M P q v
  · rfl

lemma sourceNullPatch_row (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i)
    (v:S⊕Unit) (hv:v∈sourcePositiveComponent M (sourceCosetVector M P q) i) :
    (framedCartan M *ᵥ sourceNullPatch M P q i) v=0 := by
  trans (framedCartan M *ᵥ sourceCosetVector M P q) v
  · apply Finset.sum_congr rfl
    intro u _
    by_cases hu:u∈sourcePositiveComponent M (sourceCosetVector M P q) i
    · simp only [sourceNullPatch,ite_eq_left hu]
    · simp only [sourceNullPatch,ite_eq_right hu,MulZeroClass.mul_zero]
      by_cases hh:framedCartan M v u<0
      · rw [sourcePositiveComponent_boundary_zero M _ (sourceCosetVector_nonneg M P q) i hi u hu
          ⟨v,hv,by rwa [framedCartan_symm]⟩,MulZeroClass.mul_zero]
      · have he:framedCartan M v u=0:=le_antisymm (framedCartan_off M v u
          (by rintro rfl;exact hu hv)) (le_of_not_gt hh)
        rw [he,MulZeroClass.zero_mul]
  · exact hn.2.2.1 v hv

lemma sourcePositive_exterior (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i) (v:S⊕Unit)
    (hv:v∈sourceClosedRegion M (sourcePositiveComponent M (sourceCosetVector M P q) i))
    (ho:v∉Sum.inl '' (P.val.1∩{j:S | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i})) :
    v∉Sum.inl '' P.val.1 := by
  rintro ⟨j,hj,rfl⟩
  apply ho
  refine ⟨j,⟨hj,?_⟩,rfl⟩
  rcases hv with hv|⟨u,hu,huj⟩
  · exact hv
  · exact sourcePositiveComponent_type_neighbor M P q i hi u hu j hj (by rwa [framedCartan_symm])

lemma sourcePositive_block_cap (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}
    ∀H,ClassCapOn Q (sourceFrameFamily M x H)
      (closedNeighborhood Q (fusionColorRegion m (Sum.inl '' I)) \
        fusionColorRegion m (Sum.inl '' (P.val.1∩I))) q := by
  intro I H
  rw [classCapOn_iff_level_zero]
  intro α hα k hk
  have hv:=sourceNeighborhood_project M (Sum.inl '' I) hα.1
  rw [sourceNullSign_image M P q i hn] at hv
  have hout:=sourcePositive_exterior M P q i hi α.1 hv hα.2
  have he:(k.toNat:ℤ)=k:=Int.toNat_of_nonneg (by omega)
  have hz:=hn.2.2.2 α.1 hv k.toNat (by omega)
  dsimp only at hz
  rw [he,sourceCosetVector_open_at M P x hx α.1 hout] at hz
  exact (sourceMultiplicity_zero_iff M x k α.1).mp hz H α.2

lemma sourcePositive_block_values (P:Deligne M) (q:ℕ) (i:S⊕Unit)
    (hi:0<sourceCosetVector M P q i)
    (hn:SourceNullSign M (fun d=>sourceCosetVector M P d) q i) (x:Artin M) (hx:x∈P.val.2) :
    let I:Set S:={j | (.inl j:S⊕Unit)∈sourcePositiveComponent M (sourceCosetVector M P q) i}
    ∀v,(v∈Sum.inl '' I ∧ v∉Sum.inl '' (P.val.1∩I)) ∨
      (v∉Sum.inl '' I ∧ ∃u∈Sum.inl '' I,framedCartan M v u<0)→
      sourceMultiplicity M x q v=sourceNullPatch M P q i v := by
  intro I v hv
  have hI:Sum.inl '' I=sourcePositiveComponent M (sourceCosetVector M P q) i:=sourceNullSign_image M P q i hn
  rw [hI] at hv
  rcases hv with ⟨hv,ho⟩|⟨ho,hv⟩
  · rw [←sourceCosetVector_open_at M P x hx v (sourcePositive_exterior M P q i hi v (Or.inl hv) ho)]
    simp only [sourceNullPatch,ite_eq_left hv]
  · have hoB:v∉Sum.inl '' (P.val.1∩I):=by
      intro h
      exact ho (hI ▸ Set.image_mono Set.inter_subset_right h)
    rw [←sourceCosetVector_open_at M P x hx v (sourcePositive_exterior M P q i hi v (Or.inr hv) hoB)]
    rw [sourceNullPatch,ite_eq_right ho]
    exact sourcePositiveComponent_boundary_zero M _ (sourceCosetVector_nonneg M P q) i hi v ho hv

end HarmonicArtin

end OAI
