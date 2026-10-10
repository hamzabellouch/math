import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperBasics

namespace OAI

/-! Last occupied levels and lower-edge harmonic comparisons for the pointed family. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S) (cutoff:ℤ)

noncomputable def relativePeakSupport (P:Deligne M) (i:S) : Finset ℕ :=
  (pointedProfile M f P cutoff).support.filter (fun k=>pointedProfile M f P cutoff k (.inl i)≠0)

noncomputable def relativePeak (P:Deligne M) (i:S) : ℕ :=
  (relativePeakSupport M f cutoff P i).sup id

lemma relativePeakSupport_mem (P:Deligne M) (i:S) (k:ℕ) :
    k∈relativePeakSupport M f cutoff P i ↔ pointedProfile M f P cutoff k (.inl i)≠0 := by
  unfold relativePeakSupport
  rw [Finset.mem_filter, Finsupp.mem_support_iff]
  constructor
  · exact And.right
  · intro h
    exact ⟨fun he=>h (congrFun he (.inl i)),h⟩

lemma relativePeak_bound (P:Deligne M) (i:S) (k:ℕ)
    (h:pointedProfile M f P cutoff k (.inl i)≠0) : k≤ relativePeak M f cutoff P i :=
  Finset.le_sup (f:=id) ((relativePeakSupport_mem M f cutoff P i k).mpr h)

lemma relativePeak_above (P:Deligne M) (i:S) {k:ℕ} (h:relativePeak M f cutoff P i<k) :
    pointedProfile M f P cutoff k (.inl i)=0 := by
  by_contra hn
  exact Nat.not_lt_of_ge (relativePeak_bound M f cutoff P i k hn) h

lemma relativePeak_nonzero (P:Deligne M) (i:S)
    (h:(relativePeakSupport M f cutoff P i).Nonempty) :
    pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i)≠0 := by
  apply (relativePeakSupport_mem M f cutoff P i _).mp
  obtain ⟨k,hk,he⟩:=Finset.exists_mem_eq_sup _ h id
  change (relativePeakSupport M f cutoff P i).sup id∈relativePeakSupport M f cutoff P i
  rw [he]
  exact hk

lemma relativePeak_positive (P:Deligne M) (i:S)
    (hi : ∃ k, 0 < pointedProfile M f P cutoff k (.inl i)) :
    0 < pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i) := by
  obtain ⟨k,hk⟩ := hi
  have hn := relativePeak_nonzero M f cutoff P i
    ⟨k,(relativePeakSupport_mem M f cutoff P i k).mpr (ne_of_gt hk)⟩
  exact lt_of_le_of_ne (pointedCosetVector_nonneg M f P _ _) (Ne.symm hn)

lemma relativePeak_nonzero_of_pos (P:Deligne M) (i:S) (h:0<relativePeak M f cutoff P i) :
    pointedProfile M f P cutoff (relativePeak M f cutoff P i) (.inl i)≠0 := by
  apply relativePeak_nonzero M f cutoff P i
  by_contra hn
  have he:relativePeakSupport M f cutoff P i=∅:=Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [relativePeak,he,Finset.sup_empty] at h
  exact Nat.not_lt_zero _ h

noncomputable def relativeLowerLevel (P Q:Deligne M) : ℕ :=
  (P.val.1.toFinset \ Q.val.1.toFinset).sup (fun i=>max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))

lemma relativePeak_le_lowerLevel (P Q:Deligne M) (i:S) (hi:i∈P.val.1) (hq:i∉Q.val.1) :
    relativePeak M f cutoff P i≤ relativeLowerLevel M f cutoff P Q ∧ relativePeak M f cutoff Q i≤ relativeLowerLevel M f cutoff P Q := by
  have hh:=Finset.le_sup (f:=fun i=>max (relativePeak M f cutoff P i) (relativePeak M f cutoff Q i))
    (show i∈P.val.1.toFinset \ Q.val.1.toFinset by simp [hi,hq])
  exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩

lemma relativeProfile_eq_of_lower_open {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f Q cutoff k (.inl i)=pointedProfile M f P cutoff k (.inl i)) :
    pointedProfile M f Q cutoff k=pointedProfile M f P cutoff k := by
  have hext(i:S⊕Unit)(hi:i∉(Sum.inl:S→S⊕Unit) '' Q.val.1):
      pointedProfile M f Q cutoff k i=pointedProfile M f P cutoff k i:=by
    by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
    · obtain ⟨j,hj,rfl⟩:=hp
      exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
    · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).symm
  have hq:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (pointedProfile M f P cutoff k)
    (pointedProfile M f Q cutoff k) hext (pointedCosetVector_harmonic M f Q (cutoff+k))
  have hp:=harmonicExtension_unique (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (pointedProfile M f P cutoff k)
    (pointedProfile M f P cutoff k) (fun _ _=>rfl)
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
  exact hq.trans hp.symm

lemma relativeProfile_lower_comparison {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f P cutoff k (.inl i)≤ pointedProfile M f Q cutoff k (.inl i)) :
    pointedProfile M f P cutoff k≤ pointedProfile M f Q cutoff k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedProfile M f P cutoff k) (pointedProfile M f Q cutoff k)
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
    (pointedCosetVector_harmonic M f Q (cutoff+k))
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).le

lemma relativeProfile_lower_comparison_rev {P Q:Deligne M} (h:Q≤P) (k:ℕ)
    (ho:∀i∈P.val.1,i∉Q.val.1→pointedProfile M f Q cutoff k (.inl i)≤ pointedProfile M f P cutoff k (.inl i)) :
    pointedProfile M f Q cutoff k≤ pointedProfile M f P cutoff k := by
  apply harmonic_boundary_comparison (framedCartan M) ((Sum.inl:S→S⊕Unit) '' Q.val.1)
    (framed_spherical_posDef M Q.val.1 Q.property.1) (framedCartan_off M)
    (pointedProfile M f Q cutoff k) (pointedProfile M f P cutoff k)
    (pointedCosetVector_harmonic M f Q (cutoff+k))
    (fun i=>pointedCosetVector_harmonic M f P (cutoff+k) ⟨i,Set.image_mono h.1 i.property⟩)
  intro i hi
  by_cases hp:i∈(Sum.inl:S→S⊕Unit) '' P.val.1
  · obtain ⟨j,hj,rfl⟩:=hp
    exact ho j hj (fun hq=>hi ⟨j,hq,rfl⟩)
  · exact (pointedCosetVector_upper_outside M f h (cutoff+k) i hp).symm.le

lemma relativeProfile_eq_above_lower {P Q:Deligne M} (h:Q≤P) {k:ℕ}
    (hk:relativeLowerLevel M f cutoff P Q<k) : pointedProfile M f Q cutoff k=pointedProfile M f P cutoff k := by
  apply relativeProfile_eq_of_lower_open M f cutoff h k
  intro i hi hq
  have hb:=relativePeak_le_lowerLevel M f cutoff P Q i hi hq
  rw [relativePeak_above M f cutoff Q i (hb.2.trans_lt hk),relativePeak_above M f cutoff P i (hb.1.trans_lt hk)]


end HarmonicArtin.ParabolicIntersections

end OAI
