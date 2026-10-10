import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetGeometry
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedProfile
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCap
import OAI.Topology.ArtinGroups.Harmonic.ResidueAllowed
import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Coset

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

def PointedResidueAllowed (strict:Bool) (P Q:Deligne M) (q:ℤ) : Prop :=
  Q<P ∧ ∀i∈P.val.1,i∉Q.val.1→
    (∀d:ℤ,q<d→pointedCosetVector M f Q d (.inl i)=0) ∧
    (if strict then pointedCosetVector M f Q q (.inl i)<pointedCosetVector M f P q (.inl i)
      else pointedCosetVector M f Q q (.inl i)≤ pointedCosetVector M f P q (.inl i))

abbrev PointedResidue (strict:Bool) (P:Deligne M) (q:ℤ) :=
  {Q:Deligne M // PointedResidueAllowed M f strict P Q q}

noncomputable def pointedResidueHeight (P Q:Deligne M) (q:ℤ) : ℝ :=
  ∑i∈P.val.1.toFinset,(pointedCosetVector M f Q q (.inl i)-pointedCosetVector M f P q (.inl i))

lemma pointedCosetVector_lower_compare_int {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedCosetVector M f Q k (.inl i)≤ pointedCosetVector M f P k (.inl i)) :
    pointedCosetVector M f Q k≤ pointedCosetVector M f P k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedCosetVector M f Q k) (pointedCosetVector M f P k)
    (pointedCosetVector_harmonic M f Q k)
    (fun i=>pointedCosetVector_harmonic M f P k ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h k i hp).symm.le

lemma pointedCosetVector_lower_compare_int_rev {P Q:Deligne M} (h:Q≤P) (k:ℤ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedCosetVector M f P k (.inl i)≤ pointedCosetVector M f Q k (.inl i)) :
    pointedCosetVector M f P k≤ pointedCosetVector M f Q k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedCosetVector M f P k) (pointedCosetVector M f Q k)
    (fun i=>pointedCosetVector_harmonic M f P k ⟨i,Set.image_mono h.1 i.property⟩)
    (pointedCosetVector_harmonic M f Q k)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h k i hp).le

lemma pointedResidueAllowed_le {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) : pointedCosetVector M f Q q≤ pointedCosetVector M f P q := by
  apply pointedCosetVector_lower_compare_int M f h.1.le q
  intro i hi hn
  have hh:=(h.2 i hi hn).2
  cases strict with
  | false => exact hh
  | true => exact hh.le

lemma pointedResidueHeight_nonpos {strict:Bool} {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) : pointedResidueHeight M f P Q q≤0 := by
  exact Finset.sum_nonpos (fun i _=>sub_nonpos.mpr (pointedResidueAllowed_le M f h (.inl i)))

lemma pointedResidueHeight_strict {P Q:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f true P Q q) : pointedResidueHeight M f P Q q<0 := by
  have ht:=deligne_lt_type M h.1
  obtain ⟨i,hi,hn⟩:=Set.exists_of_ssubset ht
  apply Finset.sum_neg' (fun i _=>sub_nonpos.mpr (pointedResidueAllowed_le M f h (.inl i)))
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_neg.mpr (by simpa only [↓reduceIte] using (h.2 i hi hn).2)⟩

lemma pointedResidueHeight_mono {P Q R:Deligne M} {q:ℤ}
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q) :
    pointedResidueHeight M f P Q q≤ pointedResidueHeight M f P R q :=
  Finset.sum_le_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)

lemma pointedResidueHeight_lt {P Q R:Deligne M} {q:ℤ}
    (h:pointedCosetVector M f Q q≤ pointedCosetVector M f R q)
    (hn:∃i∈P.val.1,pointedCosetVector M f Q q (.inl i)<pointedCosetVector M f R q (.inl i)) :
    pointedResidueHeight M f P Q q<pointedResidueHeight M f P R q := by
  apply Finset.sum_lt_sum (fun i _=>sub_le_sub_right (h (.inl i)) _)
  obtain ⟨i,hi,hl⟩:=hn
  exact ⟨i,Set.mem_toFinset.mpr hi,sub_lt_sub_right hl _⟩

lemma pointedResidueAllowed_upper {strict:Bool} {P Q R:Deligne M} {q:ℤ}
    (h:PointedResidueAllowed M f strict P Q q) (hr:Q≤R) (hp:R<P) :
    PointedResidueAllowed M f strict P R q := by
  refine ⟨hp,?_⟩
  intro i hi hn
  have hq:i∉Q.val.1:=fun hh=>hn (hr.1 hh)
  have he(d:ℤ):pointedCosetVector M f R d (.inl i)=pointedCosetVector M f Q d (.inl i):=
    pointedCosetVector_upper_outside M f hr d _ (by
      rintro ⟨j,hj,hh⟩;exact hn ((Sum.inl_injective hh) ▸ hj))
  simp only [he]
  exact h.2 i hi hq

end HarmonicArtin.ParabolicIntersections

end OAI
