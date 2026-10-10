import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedWeighted
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativePoset
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTies

namespace OAI

/-! Right translation of the relative coset poset by a transported stabilizer. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S : Type} [Fintype S] [LinearOrder S] (M : CoxeterMatrix S)

noncomputable def deligneRightTranslate (P : Deligne M) (r : Artin M) : Deligne M :=
  sourceCoset M P.val.1 P.property.1 (sourceCosetRepresentative M P*r)

omit [Fintype S] [LinearOrder S] in
@[simp] lemma deligneRightTranslate_type (P : Deligne M) (r : Artin M) :
    (deligneRightTranslate M P r).val.1 = P.val.1 := rfl

omit [Fintype S] [LinearOrder S] in
lemma mem_deligneRightTranslate (P : Deligne M) (r z : Artin M) :
    z ∈ (deligneRightTranslate M P r).val.2 ↔ z*r⁻¹ ∈ P.val.2 := by
  rw [sourceCosetRepresentative_spec M P]
  change z*(sourceCosetRepresentative M P*r)⁻¹ ∈ artinParabolic M P.val.1 ↔
    (z*r⁻¹)*(sourceCosetRepresentative M P)⁻¹ ∈ artinParabolic M P.val.1
  simp only [mul_inv_rev, _root_.mul_assoc]

omit [Fintype S] [LinearOrder S] in
lemma deligneRightTranslate_mono (r : Artin M) : Monotone (fun P => deligneRightTranslate M P r) := by
  intro P R h
  refine ⟨h.1, ?_⟩
  intro z hz
  exact (mem_deligneRightTranslate M R r z).mpr (h.2 ((mem_deligneRightTranslate M P r z).mp hz))

omit [Fintype S] [LinearOrder S] in
lemma deligneRightTranslate_inv (P : Deligne M) (r : Artin M) :
    deligneRightTranslate M (deligneRightTranslate M P r) r⁻¹ = P := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext z
    simp only [mem_deligneRightTranslate, inv_inv, _root_.mul_assoc, mul_inv_cancel, _root_.mul_one]

lemma pointedFamily_transport_fixed (f : S) (x a : Artin M)
    (ha : pointedFamily M f (a*x) = pointedFamily M f x) (z : Artin M) :
    pointedFamily M f (z*(x⁻¹*a*x)) = pointedFamily M f z := by
  have h1 : z*(x⁻¹*a*x) = (z*x⁻¹)*(a*x) := by group
  have h2 : (z*x⁻¹)*x = z := by group
  funext L
  rw [h1, pointedFamily_mul, congrFun ha L, ←pointedFamily_mul, h2]

lemma pointedCosetVector_translate_fixed (f : S) (x a : Artin M)
    (ha : pointedFamily M f (a*x) = pointedFamily M f x) (P : Deligne M) (k : ℤ) :
    pointedCosetVector M f (deligneRightTranslate M P (x⁻¹*a*x)) k =
      pointedCosetVector M f P k := by
  let z := sourceCosetRepresentative M P
  have hz : z*(x⁻¹*a*x) ∈ (deligneRightTranslate M P (x⁻¹*a*x)).val.2 :=
    rightCoset_self M _ _
  rw [pointedCosetVector_eq M f _ _ hz k]
  change pointedHarmonicAt M f P.val.1 (z*(x⁻¹*a*x)) k = pointedHarmonicAt M f P.val.1 z k
  unfold pointedHarmonicAt
  congr 1
  unfold pointedMultiplicity
  rw [pointedFamily_transport_fixed M f x a ha z]

lemma relativeHeight_congr (f : S) (U : Set (S ⊕ Unit)) (cutoff : ℤ)
    (P R : Deligne M) (ht : P.val.1 = R.val.1)
    (hv : ∀ k, pointedCosetVector M f P k = pointedCosetVector M f R k) :
    relativeHeight M f U cutoff P = relativeHeight M f U cutoff R := by
  have hp : pointedProfile M f P cutoff = pointedProfile M f R cutoff := by
    ext k i
    exact congrFun (hv (cutoff+k)) i
  have hm (k : ℕ) : relativeSignMask M f U cutoff P k = relativeSignMask M f U cutoff R k := by
    unfold relativeSignMask
    rw [ht, hp]
  have hb (k : ℕ) : relativeBlock M f U cutoff P k = relativeBlock M f U cutoff R k := by
    unfold relativeBlock pointedCosetSum
    rw [hv, hp, hm]
  apply congrArg toColex
  ext k
  change relativeBlockRank M f U cutoff (relativeBlock M f U cutoff P k) =
    relativeBlockRank M f U cutoff (relativeBlock M f U cutoff R k)
  rw [hb]

/-- A transported stabilizer preserves the complete relative height,
including every sign-mask coordinate. -/
lemma relativeHeight_translate_fixed (f : S) (U : Set (S ⊕ Unit)) (cutoff : ℤ)
    (x a : Artin M) (ha : pointedFamily M f (a*x) = pointedFamily M f x) (P : Deligne M) :
    relativeHeight M f U cutoff (deligneRightTranslate M P (x⁻¹*a*x)) =
      relativeHeight M f U cutoff P :=
  relativeHeight_congr M f U cutoff _ _ rfl (pointedCosetVector_translate_fixed M f x a ha P)

omit [Fintype S] [LinearOrder S] in
lemma deligneRightTranslate_relative (Y : Set S) (x a : Artin M)
    (ha : a ∈ artinParabolic M Y) (P : RelativeVertex M Y x) :
    (deligneRightTranslate M P.val (x⁻¹*a*x)).val.1 ⊆ Y ∧
      (deligneRightTranslate M P.val (x⁻¹*a*x)).val.2 ⊆ rightCoset M Y x := by
  refine ⟨P.property.1, ?_⟩
  apply rightCoset_subset_of_point M P.property.1
  let z := sourceCosetRepresentative M P.val
  have hz : z*x⁻¹ ∈ artinParabolic M Y :=
    P.property.2 (sourceCosetRepresentative_mem M P.val)
  have he : (z*(x⁻¹*a*x))*x⁻¹ = (z*x⁻¹)*a := by group
  change (z*(x⁻¹*a*x))*x⁻¹ ∈ artinParabolic M Y
  rw [he]
  exact (artinParabolic M Y).mul_mem hz ha

noncomputable def relativeTranslate (Y : Set S) (x a : Artin M)
    (ha : a ∈ artinParabolic M Y) (P : RelativeVertex M Y x) : RelativeVertex M Y x :=
  ⟨deligneRightTranslate M P.val (x⁻¹*a*x), deligneRightTranslate_relative M Y x a ha P⟩

end HarmonicArtin.ParabolicIntersections

end OAI
