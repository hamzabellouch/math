import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTiedDescent
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeTranslation

namespace OAI

/-! Confinement of the actual categorical stabilizer from a harmonic minimum. -/
namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ) {Y:Set S} {x:Artin M}

def RelativeMinimum (P:RelativeVertex M Y x) : Prop :=
  ∀ V:RelativeVertex M Y x,relativeHeight M f U cutoff P.val≤relativeHeight M f U cutoff V.val

noncomputable def relativeContainingType (Y:Set S) (P:Deligne M) : Set S :=
  relativeVisible M f cutoff Y P ∪ relativeInvisible M f cutoff Y P

lemma relative_type_subset_containing (Y:Set S) (P:Deligne M) :
    P.val.1⊆relativeContainingType M f cutoff Y P := by
  intro i hi
  by_cases hn:i∈relativeInvisible M f cutoff Y P
  · exact Or.inr hn
  · exact Or.inl ⟨hi,hn⟩

lemma relative_containing_subset (P:RelativeVertex M Y x) :
    relativeContainingType M f cutoff Y P.val⊆Y :=
  fun _ hi=>hi.elim (fun h=>P.property.1 h.1) (fun h=>h.1)

theorem relative_minimum_exists : ∃ P:RelativeVertex M Y x,RelativeMinimum M f U cutoff P := by
  let P₀:=relativeElement M Y x x (rightCoset_self M Y x)
  obtain ⟨h,⟨P,rfl⟩,hmin⟩:=wellFounded_lt.has_min
    (Set.range (fun V:RelativeVertex M Y x=>relativeHeight M f U cutoff V.val))
    ⟨relativeHeight M f U cutoff P₀.val,P₀,rfl⟩
  exact ⟨P,fun V=>le_of_not_gt (hmin _ ⟨V,rfl⟩)⟩

lemma relative_minimum_path_confined {P Q:RelativeVertex M Y x}
    (path:PathWithin (relativeAdjacent M) (RelativeMinimum M f U cutoff) P Q) :
    relativeVisible M f cutoff Y Q.val=relativeVisible M f cutoff Y P.val ∧
    relativeInvisible M f cutoff Y Q.val=relativeInvisible M f cutoff Y P.val ∧
    Relation.ReflTransGen (fun A B:Deligne M=>
      A.val.1⊆relativeContainingType M f cutoff Y P.val ∧
      B.val.1⊆relativeContainingType M f cutoff Y P.val ∧ (A≤B ∨ B≤A)) P.val Q.val := by
  induction path with
  | refl => exact ⟨rfl,rfl,.refl⟩
  | @tail A B path he ih =>
    have ht:relativeHeight M f U cutoff A.val=relativeHeight M f U cutoff B.val:=
      le_antisymm (he.1 B) (he.2.1 A)
    have hI:=relativeInvisible_eq_of_height_eq M f U cutoff Y ht
    have hV:relativeVisible M f cutoff Y A.val=relativeVisible M f cutoff Y B.val:=by
      rcases he.2.2 with hAB|hBA
      · exact relativeVisible_eq_of_tie M f U cutoff Y hAB B.property.1 ht
      · exact (relativeVisible_eq_of_tie M f U cutoff Y hBA A.property.1 ht.symm).symm
    have hBV:=hV.symm.trans ih.1
    have hBI:=hI.symm.trans ih.2.1
    have hA:A.val.val.1⊆relativeContainingType M f cutoff Y P.val:=by
      have h:=relative_type_subset_containing M f cutoff Y A.val
      simpa only [relativeContainingType,ih.1,ih.2.1] using h
    have hB:B.val.val.1⊆relativeContainingType M f cutoff Y P.val:=by
      have h:=relative_type_subset_containing M f cutoff Y B.val
      simpa only [relativeContainingType,hBV,hBI] using h
    exact ⟨hBV,hBI,ih.2.2.tail ⟨hA,hB,he.2.2⟩⟩

/-- Proposition 6.9: the stabilizer lies in the conjugate standard subgroup
specified by the visible and invisible colors at a minimum. -/
theorem relative_minimum_stabilizer_containment
    (hYU:∀i∈Y,(.inl i:S⊕Unit)∈U)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hx:x∈artinParabolic M {f}ᶜ) (P:RelativeVertex M Y x)
    (hP:RelativeMinimum M f U cutoff P)
    (a:Artin M) (ha:a∈artinParabolic M Y)
    (hfix:pointedFamily M f (a*x)=pointedFamily M f x) :
    a∈conjugate (sourceCosetRepresentative M P.val*x⁻¹)⁻¹
      (artinParabolic M (relativeContainingType M f cutoff Y P.val)) := by
  let R:=relativeTranslate M Y x a ha P
  have he:relativeHeight M f U cutoff R.val=relativeHeight M f U cutoff P.val:=
    relativeHeight_translate_fixed M f U cutoff x a hfix P.val
  have hR:RelativeMinimum M f U cutoff R:=fun V=>he.trans_le (hP V)
  have hp:=relative_minimum_path M f U cutoff hYU hU hf hx P R hP hR
  have hconf:=(relative_minimum_path_confined M f U cutoff hp).2.2
  let z:=sourceCosetRepresentative M P.val
  let r:=x⁻¹*a*x
  have hz:z*r∈R.val.val.2:=by
    change z*r∈(deligneRightTranslate M P.val r).val.2
    apply (mem_deligneRightTranslate M P.val r (z*r)).mpr
    simpa only [_root_.mul_assoc,mul_inv_cancel,_root_.mul_one] using sourceCosetRepresentative_mem M P.val
  have hm:=conjugate_membership_of_coset_path M (relativeContainingType M f cutoff Y P.val)
    z r (sourceCosetRepresentative_mem M P.val)
    (relative_type_subset_containing M f cutoff Y P.val) hz hconf
  rw [mem_conjugate,inv_inv] at hm ⊢
  convert hm using 1
  dsimp only [z,r]
  group

end HarmonicArtin.ParabolicIntersections

end OAI
