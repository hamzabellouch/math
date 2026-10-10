import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Coset

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

def SourceResidueAllowed (strict:Bool) (P Q:Deligne M) (q:ℤ) : Prop :=
  Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→
    (∀d:ℤ,q<d→sourceCosetVector M Q d (.inl i)=0) ∧
    (if strict then sourceCosetVector M Q q (.inl i)<sourceCosetVector M P q (.inl i)
      else sourceCosetVector M Q q (.inl i)≤ sourceCosetVector M P q (.inl i))

abbrev SourceResidue (strict:Bool) (P:Deligne M) (q:ℤ) :=
  {Q:Deligne M // SourceResidueAllowed M strict P Q q}

noncomputable def sourceResidueHeight (P Q:Deligne M) (q:ℤ) : ℝ :=
  ∑i∈P.val.1.toFinset,(sourceCosetVector M Q q (.inl i)-sourceCosetVector M P q (.inl i))

lemma sourceCosetVector_lower_compare_int {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M Q k (.inl i)≤ sourceCosetVector M P k (.inl i)) :
    sourceCosetVector M Q k≤ sourceCosetVector M P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M Q k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).symm.le

lemma sourceCosetVector_lower_compare_int_rev {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→sourceCosetVector M P k (.inl i)≤ sourceCosetVector M Q k (.inl i)) :
    sourceCosetVector M P k≤ sourceCosetVector M Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (sourceCosetVector M P k) (sourceCosetVector M Q k)
    (fun i=>sourceCosetVector_harmonic M P k ⟨i,Set.image_mono h.1 i.property⟩)
    (sourceCosetVector_harmonic M Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (sourceCosetVector_upper_outside M h k i hp).le

lemma sourceResidueAllowed_le {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) : sourceCosetVector M Q q≤ sourceCosetVector M P q := by
  apply sourceCosetVector_lower_compare_int M h.1.le q
  intro i hi hn
  have hh:=(h.2 i hi hn).2
  cases strict with
  | false => exact hh
  | true => exact hh.le

lemma sourceResidueHeight_nonpos {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) : sourceResidueHeight M P Q q≤0 := by
  exact Finset.sum_nonpos (fun i _=>sub_nonpos.mpr (sourceResidueAllowed_le M h (.inl i)))

lemma sourceResidueHeight_strict {P Q:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M true P Q q) : sourceResidueHeight M P Q q<0 := by
  have ht:=deligne_lt_type M h.1
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset ht
  apply Finset.sum_neg' (fun i _=>sub_nonpos.mpr (sourceResidueAllowed_le M h (.inl i)))
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_neg.mpr (by simpa only [↓reduceIte] using (h.2 i hi hn).2)⟩

lemma sourceResidueHeight_mono {P Q R:Deligne M} {q:ℤ}
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q) :
    sourceResidueHeight M P Q q≤ sourceResidueHeight M P R q :=
  Finset.sum_le_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)

lemma sourceResidueHeight_lt {P Q R:Deligne M} {q:ℤ}
    (h:sourceCosetVector M Q q≤ sourceCosetVector M R q)
    (hn:∃i∈P.val.1,sourceCosetVector M Q q (.inl i)<sourceCosetVector M R q (.inl i)) :
    sourceResidueHeight M P Q q<sourceResidueHeight M P R q := by
  apply Finset.sum_lt_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)
  obtain ⟨i,hi,hl⟩:=hn
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_lt_sub_right hl _⟩

lemma sourceResidueAllowed_upper {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (h:SourceResidueAllowed M strict P Q q) (hr:Q≤R) (hp:R<P) :
    SourceResidueAllowed M strict P R q := by
  refine ⟨hp,?_⟩
  intro i hi hn
  have hq:i∉Q.val.1:=fun hh=>hn (hr.1 hh)
  have he(d:ℤ):sourceCosetVector M R d (.inl i)=sourceCosetVector M Q d (.inl i):=
    sourceCosetVector_upper_outside M hr d _ (by
      rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
  simp only [he]
  exact h.2 i hi hq

end HarmonicArtin

end OAI
