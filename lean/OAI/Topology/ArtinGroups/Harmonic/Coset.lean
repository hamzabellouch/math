import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Candidate

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceCoset (T:Set S) (hT:IsSpherical M T) (x:Artin M) : Deligne M :=
  ⟨(T,rightCoset M T x),hT,⟨x,rfl⟩⟩

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_mono {T U:Set S} (h:T⊆U) (x:Artin M) : rightCoset M T x⊆rightCoset M U x :=
  fun _ hy=>artinParabolic_mono M h hy

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_eq_of_mem (T:Set S) (x y:Artin M) (hy:y∈rightCoset M T x) :
    rightCoset M T y=rightCoset M T x := by
  have h:=rightCoset_mul_eq M T (y*x⁻¹) x hy
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_le {T U:Set S} {hT:IsSpherical M T} {hU:IsSpherical M U}
    (h:T⊆U) (x:Artin M) : sourceCoset M T hT x ≤ sourceCoset M U hU x :=
  ⟨h,rightCoset_mono M h x⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_mem (P:Deligne M) : sourceCosetRepresentative M P∈P.val.2 := by
  rw [sourceCosetRepresentative_spec]
  exact rightCoset_self M _ _

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_eq (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) :
    sourceCoset M P.val.1 P.property.1 x=P := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change rightCoset M P.val.1 x=P.val.2
    rw [sourceCosetRepresentative_spec] at hx ⊢
    exact rightCoset_eq_of_mem M _ _ _ hx

omit [Fintype S] [LinearOrder S] in
lemma deligne_eq_of_le_type_eq {P R:Deligne M} (h:P≤R) (ht:P.val.1=R.val.1) : P=R := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  have hr:=sourceCoset_eq M R x (h.2 hx)
  have hp:=sourceCoset_eq M P x hx
  rw [←hr,←hp]
  apply Subtype.ext
  simp only [sourceCoset,ht]

omit [Fintype S] [LinearOrder S] in
lemma deligne_lt_type {P R:Deligne M} (h:P<R) : P.val.1⊂R.val.1 := by
  exact lt_of_le_of_ne h.le.1 (fun he=>h.ne (deligne_eq_of_le_type_eq M h.le he))

lemma sourceCosetVector_harmonic (P:Deligne M) (k:ℤ)
    (i:(Sum.inl:S→S⊕Unit) '' P.val.1) :
    (framedCartan M *ᵥ sourceCosetVector M P k) i=0 :=
  sourceHarmonicAt_harmonic M P.val.1 P.property.1 _ k i

lemma sourceCosetVector_upper_outside {P R:Deligne M} (h:P≤R) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl:S→S⊕Unit) '' R.val.1) :
    sourceCosetVector M R k i=sourceCosetVector M P k i := by
  let x:=sourceCosetRepresentative M P
  have hx:=sourceCosetRepresentative_mem M P
  rw [sourceCosetVector_eq M R x (h.2 hx),sourceCosetVector_eq M P x hx,
    sourceHarmonicAt_outside M R.val.1 x k i hi,
    sourceHarmonicAt_outside M P.val.1 x k i (fun he=>hi (Set.image_mono h.1 he))]

lemma sourceCosetVector_upper_harmonize {P R:Deligne M} (h:P≤R) (k:ℤ) :
    sourceCosetVector M R k=harmonicExtension (framedCartan M)
      ((Sum.inl:S→S⊕Unit) '' R.val.1) (sourceCosetVector M P k) :=
  harmonicExtension_unique _ _ (framed_spherical_posDef M R.val.1 R.property.1) _ _
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k)

theorem sourceCosetVector_upper_change {P R:Deligne M} (h:P≤R) (k:ℤ) :
    (fun vertex : (Sum.inl:S→S⊕Unit) '' R.val.1 =>
      sourceCosetVector M R k vertex-sourceCosetVector M P k vertex) =
      -(((framedCartan M).submatrix Subtype.val Subtype.val :
          Matrix ((Sum.inl:S→S⊕Unit) '' R.val.1) ((Sum.inl:S→S⊕Unit) '' R.val.1) ℝ)⁻¹ *ᵥ
        fun vertex : (Sum.inl:S→S⊕Unit) '' R.val.1 =>
          (framedCartan M *ᵥ sourceCosetVector M P k) vertex) := by
  convert harmonic_upper_change (framedCartan M)
    ((Sum.inl:S→S⊕Unit) '' R.val.1)
    (framed_spherical_posDef M R.val.1 R.property.1)
    (sourceCosetVector M P k) (sourceCosetVector M R k)
    (sourceCosetVector_upper_outside M h k) (sourceCosetVector_harmonic M R k) using 1
  congr! (postTransparency := .reducible)

end HarmonicArtin

end OAI
