import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeUpperComparison
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativePoset
import OAI.Topology.ArtinGroups.ParabolicIntersections.ConnectedMinima

namespace OAI

/-! Connected descending upper neighborhoods, using their common active-color extension. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S) (f : S)
  (U : Set (S ⊕ Unit)) (cutoff : ℤ) (Y : Set S) (x : Artin M)

noncomputable def relativeUpperTop (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) : RelativeVertex M Y x :=
  relativeVertex M Y (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val)
    (relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU)
    (fun _ hi => hi.elim (fun h => P.property.1 h) (fun h => h.1))
    x (sourceCosetRepresentative M P.val) (P.property.2 (sourceCosetRepresentative_mem M P.val))

noncomputable def relativeUpperClip (P R : RelativeVertex M Y x) : RelativeVertex M Y x :=
  relativeVertex M Y (R.val.val.1 ∩ (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val))
    (source_spherical_mono M Set.inter_subset_left R.val.property.1)
    (fun _ hi => R.property.1 hi.1)
    x (sourceCosetRepresentative M P.val) (P.property.2 (sourceCosetRepresentative_mem M P.val))

lemma relative_le_upperClip {P R : RelativeVertex M Y x} (h : P ≤ R) :
    P ≤ relativeUpperClip M f U cutoff Y x P R := by
  change P.val ≤ (relativeUpperClip M f U cutoff Y x P R).val
  change P.val ≤ sourceCoset M _ (source_spherical_mono M Set.inter_subset_left R.val.property.1) _
  nth_rw 1 [←sourceCoset_eq M P.val _ (sourceCosetRepresentative_mem M P.val)]
  exact sourceCoset_le M (show P.val.val.1 ⊆ R.val.val.1 ∩
    (P.val.val.1 ∪ relativeActiveSet M f U cutoff Y P.val) from
      fun _ hi => ⟨h.1 hi, Or.inl hi⟩) _

lemma relative_upperClip_le {P R : RelativeVertex M Y x} (h : P ≤ R) :
    relativeUpperClip M f U cutoff Y x P R ≤ R := by
  change sourceCoset M _ (source_spherical_mono M Set.inter_subset_left R.val.property.1) _ ≤ R.val
  rw [←sourceCoset_eq M R.val _ (h.2 (sourceCosetRepresentative_mem M P.val))]
  exact sourceCoset_le M Set.inter_subset_left _

lemma relative_upperClip_le_top (P R : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U) :
    relativeUpperClip M f U cutoff Y x P R ≤ relativeUpperTop M f U cutoff Y x P hYU := by
  exact sourceCoset_le M (hT := source_spherical_mono M Set.inter_subset_left R.val.property.1)
    (hU := relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU) Set.inter_subset_right _

def RelativeDescendingUpper (P R : RelativeVertex M Y x) : Prop :=
  P < R ∧ relativeHeight M f U cutoff R.val < relativeHeight M f U cutoff P.val

lemma relative_upperClip_descending {P R : RelativeVertex M Y x}
    (h : RelativeDescendingUpper M f U cutoff Y x P R) :
    RelativeDescendingUpper M f U cutoff Y x P (relativeUpperClip M f U cutoff Y x P R) := by
  obtain ⟨i,hi,ht,ha⟩ := relativeUpper_descending_has_active M f U cutoff h.1 h.2
  have hl : P < relativeUpperClip M f U cutoff Y x P R := by
    apply lt_of_le_of_ne (relative_le_upperClip M f U cutoff Y x h.1.le)
    intro he
    have hiC : i ∈ (relativeUpperClip M f U cutoff Y x P R).val.val.1 :=
      ⟨hi, Or.inr ⟨R.property.1 hi,ht,ha⟩⟩
    rw [←he] at hiC
    exact ht hiC
  refine ⟨hl, relativeUpper_active_descending M f U cutoff hl ?_⟩
  intro j hj hn
  exact (hj.2.resolve_left hn).2.2

lemma relative_upperTop_descending (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U)
    (ha : (relativeActiveSet M f U cutoff Y P.val).Nonempty) :
    RelativeDescendingUpper M f U cutoff Y x P (relativeUpperTop M f U cutoff Y x P hYU) := by
  have hp : P ≤ relativeUpperTop M f U cutoff Y x P hYU := by
    change P.val ≤ sourceCoset M _
      (relativeActiveSet_spherical M f U cutoff Y P.val P.property.1 hYU) _
    nth_rw 1 [←sourceCoset_eq M P.val _ (sourceCosetRepresentative_mem M P.val)]
    exact sourceCoset_le M Set.subset_union_left _
  have hl : P < relativeUpperTop M f U cutoff Y x P hYU := by
    apply lt_of_le_of_ne hp
    intro he
    obtain ⟨i,hi⟩ := ha
    have hm : i ∈ (relativeUpperTop M f U cutoff Y x P hYU).val.val.1 := Or.inr hi
    rw [←he] at hm
    exact hi.2.1 hm
  exact ⟨hl,relativeUpper_active_descending M f U cutoff hl (fun _ hi hn => (hi.resolve_left hn).2.2)⟩

private lemma within_symm {V : Type*} {adj : V → V → Prop} {p : V → Prop}
    (hs : ∀ a b, adj a b → adj b a) {a b : V} (h : PathWithin adj p a b) :
    PathWithin adj p b a := by
  induction h with
  | refl => exact .refl
  | @tail c d h he ih =>
    exact (Relation.ReflTransGen.single (r := fun u v => p u ∧ p v ∧ adj u v)
      ⟨he.2.1, he.1, hs c d he.2.2⟩).trans ih

/-- Descending upper neighbors are connected through descending upper neighbors. -/
theorem relative_descending_upper_connected (P : RelativeVertex M Y x)
    (hYU : ∀ i ∈ Y, (.inl i : S ⊕ Unit) ∈ U)
    (R Q : RelativeVertex M Y x)
    (hR : RelativeDescendingUpper M f U cutoff Y x P R)
    (hQ : RelativeDescendingUpper M f U cutoff Y x P Q) :
    PathWithin (relativeAdjacent M) (RelativeDescendingUpper M f U cutoff Y x P) R Q := by
  obtain ⟨i,hi,ht,ha⟩ := relativeUpper_descending_has_active M f U cutoff hR.1 hR.2
  have hTop := relative_upperTop_descending M f U cutoff Y x P hYU
    ⟨i,R.property.1 hi,ht,ha⟩
  have pathToTop (V : RelativeVertex M Y x) (hV : RelativeDescendingUpper M f U cutoff Y x P V) :
      PathWithin (relativeAdjacent M) (RelativeDescendingUpper M f U cutoff Y x P)
        V (relativeUpperTop M f U cutoff Y x P hYU) := by
    have hC := relative_upperClip_descending M f U cutoff Y x hV
    exact (Relation.ReflTransGen.single (r := fun a b =>
      RelativeDescendingUpper M f U cutoff Y x P a ∧
      RelativeDescendingUpper M f U cutoff Y x P b ∧ relativeAdjacent M a b)
      ⟨hV,hC,Or.inr (relative_upperClip_le M f U cutoff Y x hV.1.le)⟩).tail
      ⟨hC,hTop,Or.inl (relative_upperClip_le_top M f U cutoff Y x P V hYU)⟩
  exact (pathToTop R hR).trans (within_symm (fun _ _ h => h.elim Or.inr Or.inl) (pathToTop Q hQ))

end HarmonicArtin.ParabolicIntersections

end OAI
