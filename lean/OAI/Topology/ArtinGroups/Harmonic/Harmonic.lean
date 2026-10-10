import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.FrameFamily

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [LinearOrder S] in
lemma framed_spherical_posDef (T:Set S) (hT:IsSpherical M T) :
    ((framedCartan M).submatrix ((↑):((Sum.inl : S→S⊕Unit) '' T)→S⊕Unit) Subtype.val).PosDef := by
  let e:((Sum.inl : S→S⊕Unit) '' T)→T:=fun i=>⟨(Classical.choose i.property),
    (Classical.choose_spec i.property).1⟩
  have he:∀ i:((Sum.inl : S→S⊕Unit) '' T),Sum.inl (e i:S)=(i:S⊕Unit):=
    fun i=>(Classical.choose_spec i.property).2
  have hi:Function.Injective e:=by
    intro i j hij
    apply Subtype.ext
    rw [←he i,←he j,hij]
  have h:((Geometric.cartan M).submatrix ((↑):T→S) Subtype.val).PosDef:=
    Geometric.spherical_cartan_posDef M T hT
  convert h.submatrix hi using 1
  ext i j
  change framedCartan M (i:S⊕Unit) (j:S⊕Unit)=Geometric.cartan M (e i) (e j)
  rw [←he i,←he j]
  rfl

noncomputable def sourceHarmonicAt (T:Set S) (x:Artin M) (k:ℤ) : S⊕Unit→ℝ :=
  harmonicExtension (framedCartan M) ((Sum.inl : S→S⊕Unit) '' T) (sourceMultiplicity M x k)

lemma sourceHarmonicAt_outside (T:Set S) (x:Artin M) (k:ℤ) (i:S⊕Unit)
    (hi:i∉(Sum.inl : S→S⊕Unit) '' T) : sourceHarmonicAt M T x k i=sourceMultiplicity M x k i :=
  harmonicExtension_outside _ _ _ hi

lemma sourceHarmonicAt_nonneg (T:Set S) (hT:IsSpherical M T) (x:Artin M) (k:ℤ) :
    ∀ i,0 ≤ sourceHarmonicAt M T x k i :=
  harmonicExtension_nonneg _ _ (framed_spherical_posDef M T hT)
    (framedCartan_off M) _ (sourceMultiplicity_nonneg M x k)

lemma sourceHarmonicAt_harmonic (T:Set S) (hT:IsSpherical M T)
    (x:Artin M) (k:ℤ) (i:(Sum.inl : S→S⊕Unit) '' T) :
    (framedCartan M *ᵥ sourceHarmonicAt M T x k) i=0 :=
  harmonicExtension_harmonic _ _ (framed_spherical_posDef M T hT) _ i

lemma sourceHarmonicAt_frame (T:Set S) (x:Artin M) (k:ℤ) :
    sourceHarmonicAt M T x k (.inr ())=if k=0 then 1 else 0 := by
  rw [sourceHarmonicAt_outside M T x k _ (by
    rintro ⟨_,_,he⟩; exact Sum.inl_ne_inr he)]
  exact sourceMultiplicity_frame M x k

lemma sourceHarmonicAt_invariant (T:Set S) (hT:IsSpherical M T)
    (g x:Artin M) (hg:g∈artinParabolic M T) (k:ℤ) :
    sourceHarmonicAt M T (g*x) k=sourceHarmonicAt M T x k := by
  apply harmonicExtension_unique _ _ (framed_spherical_posDef M T hT)
  · intro i hi
    rw [sourceHarmonicAt_outside _ _ _ _ _ hi]
    exact sourceMultiplicity_exterior M T g hg x i hi k
  · exact sourceHarmonicAt_harmonic M T hT (g*x) k

omit [Fintype S] [LinearOrder S] in
lemma rightCoset_self (T:Set S) (x:Artin M) : x∈rightCoset M T x := by
  change x*x⁻¹∈artinParabolic M T
  simp only [mul_inv_cancel]
  exact Subgroup.one_mem _

lemma sourceHarmonicAt_of_mem (T:Set S) (hT:IsSpherical M T) (x y:Artin M)
    (hy:y∈rightCoset M T x) (k:ℤ) :
    sourceHarmonicAt M T y k=sourceHarmonicAt M T x k := by
  have h:=sourceHarmonicAt_invariant M T hT (y*x⁻¹) x hy k
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using h

noncomputable def sourceCosetRepresentative (P:Deligne M) : Artin M :=
  P.property.2.choose

omit [Fintype S] [LinearOrder S] in
lemma sourceCosetRepresentative_spec (P:Deligne M) :
    P.val.2=rightCoset M P.val.1 (sourceCosetRepresentative M P) :=
  P.property.2.choose_spec

noncomputable def sourceCosetVector (P:Deligne M) (k:ℤ) : S⊕Unit→ℝ :=
  sourceHarmonicAt M P.val.1 (sourceCosetRepresentative M P) k

lemma sourceCosetVector_eq (P:Deligne M) (x:Artin M) (hx:x∈P.val.2) (k:ℤ) :
    sourceCosetVector M P k=sourceHarmonicAt M P.val.1 x k := by
  rw [sourceCosetRepresentative_spec] at hx
  exact (sourceHarmonicAt_of_mem M P.val.1 P.property.1 _ x hx k).symm

lemma sourceCosetVector_nonneg (P:Deligne M) (k:ℤ) :
    ∀ i,0 ≤ sourceCosetVector M P k i :=
  sourceHarmonicAt_nonneg M P.val.1 P.property.1 _ k

lemma sourceCosetVector_frame (P:Deligne M) (k:ℤ) :
    sourceCosetVector M P k (.inr ())=if k=0 then 1 else 0 :=
  sourceHarmonicAt_frame M P.val.1 _ k

end HarmonicArtin

end OAI
