import OAI.Topology.ArtinGroups.ParabolicIntersections.CosetContainment
import OAI.Topology.ArtinGroups.Harmonic.SignedLetter

namespace OAI

/-! The connected poset of actual spherical cosets inside a fixed standard coset. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} (M : CoxeterMatrix S)

abbrev RelativeVertex (Y : Set S) (x : Artin M) :=
  {P : Deligne M // P.val.1 ⊆ Y ∧ P.val.2 ⊆ rightCoset M Y x}

def relativeAdjacent {Y : Set S} {x : Artin M} (P R : RelativeVertex M Y x) : Prop :=
  P ≤ R ∨ R ≤ P

abbrev RelativePath {Y : Set S} {x : Artin M} (P R : RelativeVertex M Y x) :=
  Relation.ReflTransGen (relativeAdjacent M) P R

noncomputable def relativeVertex (Y T : Set S) (hT : IsSpherical M T) (hTY : T ⊆ Y)
    (x z : Artin M) (hz : z ∈ rightCoset M Y x) : RelativeVertex M Y x :=
  ⟨sourceCoset M T hT z, hTY, rightCoset_subset_of_point M hTY hz⟩

noncomputable def relativeElement (Y : Set S) (x z : Artin M)
    (hz : z ∈ rightCoset M Y x) : RelativeVertex M Y x :=
  relativeVertex M Y ∅ (spherical_empty M) (Set.empty_subset _) x z hz

lemma relativeElement_le (Y : Set S) (x : Artin M) (P : RelativeVertex M Y x)
    (z : Artin M) (hz : z ∈ P.val.val.2) :
    relativeElement M Y x z (P.property.2 hz) ≤ P := by
  refine ⟨Set.empty_subset _, ?_⟩
  change rightCoset M ∅ z ⊆ P.val.val.2
  rw [rightCoset_empty]
  exact Set.singleton_subset_iff.mpr hz

lemma relativePath_symm {Y : Set S} {x : Artin M} {P R : RelativeVertex M Y x}
    (h : RelativePath M P R) : RelativePath M R P := by
  induction h with
  | refl => exact .refl
  | @tail A B h edge ih =>
    exact (Relation.ReflTransGen.single (r := relativeAdjacent M) (edge.elim Or.inr Or.inl)).trans ih

lemma relative_generator_step (Y : Set S) (x z : Artin M)
    (hz : z ∈ rightCoset M Y x) (s : S) (hs : s ∈ Y) :
    RelativePath M (relativeElement M Y x z hz)
      (relativeElement M Y x (generator M s*z) (by
        change (generator M s*z)*x⁻¹ ∈ artinParabolic M Y
        rw [_root_.mul_assoc]
        exact (artinParabolic M Y).mul_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩) hz)) := by
  have hg : generator M s*z ∈ rightCoset M Y x := by
    change (generator M s*z)*x⁻¹ ∈ artinParabolic M Y
    rw [_root_.mul_assoc]
    exact (artinParabolic M Y).mul_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩) hz
  let R := relativeVertex M Y {s} (spherical_singleton M s)
    (Set.singleton_subset_iff.mpr hs) x z hz
  have hzr : z ∈ R.val.val.2 := rightCoset_self M {s} z
  have hgr : generator M s*z ∈ R.val.val.2 := by
    change (generator M s*z)*z⁻¹ ∈ artinParabolic M {s}
    simp only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one]
    exact Subgroup.subset_closure ⟨s,rfl,rfl⟩
  exact (Relation.ReflTransGen.single (r := relativeAdjacent M) (Or.inl (relativeElement_le M Y x R z hzr))).tail
    (Or.inr (relativeElement_le M Y x R _ hgr))

/-- Left multiplication by a word in the ambient standard subgroup gives
an explicit comparability path through rank-one cosets. -/
lemma relative_element_connected (Y : Set S) (x g : Artin M)
    (hg : g ∈ artinParabolic M Y) :
    RelativePath M (relativeElement M Y x x (rightCoset_self M Y x))
      (relativeElement M Y x (g*x) (by
        change (g*x)*x⁻¹ ∈ artinParabolic M Y
        simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using hg)) := by
  induction hg using Subgroup.closure_induction_left with
  | one => simpa only [_root_.one_mul] using (Relation.ReflTransGen.refl
      (a := relativeElement M Y x x (rightCoset_self M Y x)))
  | mul_left a ha g hg ih =>
    obtain ⟨s, hs, rfl⟩ := ha
    have h := relative_generator_step M Y x (g*x) (by
      change (g*x)*x⁻¹ ∈ artinParabolic M Y
      simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using (show g ∈ artinParabolic M Y from hg)) s hs
    simpa only [_root_.mul_assoc] using ih.trans h
  | inv_mul_cancel a ha g hg ih =>
    obtain ⟨s, hs, rfl⟩ := ha
    have hg' : (generator M s)⁻¹*g ∈ artinParabolic M Y :=
      (artinParabolic M Y).mul_mem
        ((artinParabolic M Y).inv_mem (Subgroup.subset_closure ⟨s,hs,rfl⟩)) hg
    have h := relative_generator_step M Y x (((generator M s)⁻¹*g)*x) (by
      change (((generator M s)⁻¹*g)*x)*x⁻¹ ∈ artinParabolic M Y
      simpa only [_root_.mul_assoc, mul_inv_cancel, _root_.mul_one] using hg') s hs
    have he : generator M s * (((generator M s)⁻¹*g)*x) = g*x := by group
    simp only [he] at h
    exact ih.trans (relativePath_symm M h)

/-- The relative spherical-coset poset is connected, without assuming that
its ambient type is spherical. -/
theorem relative_poset_connected (Y : Set S) (x : Artin M)
    (P R : RelativeVertex M Y x) : RelativePath M P R := by
  have base (P : RelativeVertex M Y x) :
      RelativePath M (relativeElement M Y x x (rightCoset_self M Y x)) P := by
    let z := sourceCosetRepresentative M P.val
    have hz : z ∈ P.val.val.2 := sourceCosetRepresentative_mem M P.val
    have hzx : z ∈ rightCoset M Y x := P.property.2 hz
    have h := relative_element_connected M Y x (z*x⁻¹) hzx
    have he : (z*x⁻¹)*x = z := by group
    simp only [he] at h
    exact h.tail (Or.inl (relativeElement_le M Y x P z hz))
  exact (relativePath_symm M (base P)).trans (base R)

end HarmonicArtin.ParabolicIntersections

end OAI
