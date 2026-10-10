import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativePeaks
import OAI.Topology.ArtinGroups.Harmonic.TypeComponent

namespace OAI

/-! Peaks and signs on connected components of a spherical closed type. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma pointedProfile_positive_neighbor (P:Deligne M) (k:ℕ) (i:S) (hi:i∈P.val.1)
    (j:S ⊕ Unit) (hij:framedCartan M (.inl i) j<0)
    (hj:0<pointedProfile M f P cutoff k j) : 0<pointedProfile M f P cutoff k (.inl i) := by
  apply harmonic_positive_neighbor_at (framedCartan M) (framedCartan_off M)
    _ (pointedCosetVector_nonneg M f P (cutoff+k)) _ hij hj
  exact (pointedCosetVector_harmonic M f P (cutoff+k) ⟨.inl i,⟨i,hi,rfl⟩⟩).ge

lemma relativePeak_neighbor (P:Deligne M) (i j:S) (hi:i∈P.val.1) (hj:j∈P.val.1)
    (hij:framedCartan M (.inl i) (.inl j)<0) :
    relativePeak M f cutoff P i = relativePeak M f cutoff P j := by
  have he : relativePeakSupport M f cutoff P i = relativePeakSupport M f cutoff P j := by
    ext k
    rw [relativePeakSupport_mem,relativePeakSupport_mem]
    constructor
    · intro hn
      exact ne_of_gt (pointedProfile_positive_neighbor M f cutoff P k j hj (.inl i)
        (by rwa [framedCartan_symm])
        (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)))
    · intro hn
      exact ne_of_gt (pointedProfile_positive_neighbor M f cutoff P k i hi (.inl j) hij
        (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)))
  exact congrArg (fun F:Finset ℕ => F.sup id) he

lemma pointedTypeComponent_peak (P:Deligne M) (i:S) (hi:i∈P.val.1)
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    relativePeak M f cutoff P j = relativePeak M f cutoff P i := by
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      relativePeak M f cutoff P a = relativePeak M f cutoff P i := by
    intro a ha
    induction ha with
    | refl => rfl
    | @tail b c _ hbc ih =>
      exact (relativePeak_neighbor M f cutoff P c b c.property b.property
        (by rwa [framedCartan_symm])).trans ih
  exact hgen ⟨j,hj⟩ h

lemma pointedTypeComponent_positive (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    0<pointedProfile M f P cutoff k (.inl j) := by
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      0<pointedProfile M f P cutoff k (.inl a.val) := by
    intro a ha
    induction ha with
    | refl => exact hp
    | @tail b c _ hbc ih =>
      exact pointedProfile_positive_neighbor M f cutoff P k c c.property (.inl b)
        (by rwa [framedCartan_symm]) ih
  exact hgen ⟨j,hj⟩ h

lemma pointedTypeComponent_positiveComponent (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl j) =
      sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl i) := by
  apply sourcePositiveComponent_eq M _ _ _ (sourcePositiveComponent_spec M _ _ hp)
  obtain ⟨hj,h⟩ := hj
  have hgen : ∀ a:P.val.1, Relation.ReflTransGen
      (fun a b:P.val.1 => framedCartan M (.inl a.val) (.inl b.val)<0) ⟨i,hi⟩ a →
      (.inl a.val:S ⊕ Unit) ∈ sourcePositiveComponent M (pointedProfile M f P cutoff k) (.inl i) := by
    intro a ha
    induction ha with
    | refl => exact .refl
    | @tail b c hb hbc ih =>
      exact ih.tail ⟨pointedTypeComponent_positive M f cutoff P i hi k hp b ⟨b.property,hb⟩,
        hbc,pointedTypeComponent_positive M f cutoff P i hi k hp c ⟨c.property,hb.tail hbc⟩⟩
  exact hgen ⟨j,hj⟩ h

omit [LinearOrder S] in
lemma relativePositiveSign_component_iff (p:ℕ →₀ (S ⊕ Unit → ℝ)) (k:ℕ) (i:S ⊕ Unit)
    (hp:0<p k i) :
    relativePositiveSign (framedCartan M) U p k i ↔
      sourcePositiveComponent M (p k) i ⊆ U ∧
      (∀ j ∈ sourcePositiveComponent M (p k) i, (framedCartan M *ᵥ p k) j = 0) ∧
      ∀ d, k<d → ∀ j, (j ∈ sourcePositiveComponent M (p k) i ∨
        ∃ a ∈ sourcePositiveComponent M (p k) i, framedCartan M a j<0) → p d j=0 := by
  constructor
  · rintro ⟨I,hi,hU,hI,hr,hh⟩
    have he := sourcePositiveComponent_eq M (p k) i I hI hi
    simpa only [he] using And.intro hU (And.intro hr hh)
  · rintro ⟨hU,hr,hh⟩
    exact ⟨_,.refl,hU,sourcePositiveComponent_spec M _ _ hp,hr,hh⟩

lemma pointedTypeComponent_sign (P:Deligne M) (i:S) (hi:i∈P.val.1) (k:ℕ)
    (hp:0<pointedProfile M f P cutoff k (.inl i))
    (j:S) (hj:j∈sourceTypeComponent M P i hi) :
    relativeSign M U (pointedProfile M f P cutoff) k (.inl j) =
      relativeSign M U (pointedProfile M f P cutoff) k (.inl i) := by
  have hjp := pointedTypeComponent_positive M f cutoff P i hi k hp j hj
  have he := pointedTypeComponent_positiveComponent M f cutoff P i hi k hp j hj
  have hs : relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl j) ↔
      relativePositiveSign (framedCartan M) U (pointedProfile M f P cutoff) k (.inl i) := by
    rw [relativePositiveSign_component_iff M U _ _ _ hjp,
      relativePositiveSign_component_iff M U _ _ _ hp,he]
  simp only [relativeSign,ne_of_gt hp,ne_of_gt hjp,↓reduceIte,hs]

lemma pointedBlock_above_boundary (P:Deligne M) (B:Set S) (hB:B⊆P.val.1) (q:ℕ)
    (hq:∀i∈B,relativePeak M f cutoff P i=q) (v:S ⊕ Unit)
    (hv:∃i∈B,framedCartan M (.inl i) v<0) (d:ℕ) (hd:q<d) :
    pointedProfile M f P cutoff d v=0 := by
  obtain ⟨i,hi,hiv⟩ := hv
  by_contra hn
  have hp := pointedProfile_positive_neighbor M f cutoff P d i (hB hi) v hiv
    (lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn))
  exact (ne_of_gt hp) (relativePeak_above M f cutoff P i (by rwa [hq i hi]))

end HarmonicArtin.ParabolicIntersections

end OAI
