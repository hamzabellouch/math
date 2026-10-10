import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Eligible
import OAI.Topology.ArtinGroups.Harmonic.CosetExteriorCap
import OAI.Topology.ArtinGroups.Harmonic.CosetBelow

namespace OAI

namespace HarmonicArtin
open _root_.Matrix _root_.OAI.Matrix

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceCartan_commuting_zero (s t:S) (h:M s t=2) :
    framedCartan M (.inl s) (.inl t)=0 := by
  have hn:s≠t:=by rintro rfl;have hh:=M.diagonal s;omega
  simp [framedCartan,hn,h,Real.cos_pi_div_two]

lemma harmonic_block_eq {ι:Type*} [Fintype ι] (C:Matrix ι ι ℝ) (U V:Set ι)
    (hU:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ).PosDef)
    (p q:ι→ℝ) (hp:∀i:U,(C *ᵥ p) i=0) (hq:∀i:U,(C *ᵥ q) i=0)
    (hzero:∀i∈U,∀j∈V,C i j=0) (hext:∀j,j∉U→j∉V→p j=q j) :
    ∀i∈U,p i=q i := by
  have he:(C.submatrix Subtype.val Subtype.val:Matrix U U ℝ) *ᵥ
      (fun i:U=>p i-q i)=0:=by
    funext i
    have hr:(C *ᵥ (p-q)) i=0:=by rw [Matrix.mulVec_sub,Pi.sub_apply,hp i,hq i,sub_self]
    rw [harmonic_row_split C U] at hr
    have hz:(∑j:↥(Uᶜ),C i j*(p-q) j)=0:=by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hv:j.val∈V
      · rw [hzero i i.property j hv,zero_mul]
      · simp only [Pi.sub_apply,hext j j.property hv,sub_self,mul_zero]
    rw [hz,add_zero] at hr
    exact hr
  have hh:=harmonic_solve_left (C.submatrix Subtype.val Subtype.val:Matrix U U ℝ) hU
    (fun i:U=>p i-q i)
  rw [he,Matrix.mulVec_zero] at hh
  intro i hi
  exact sub_eq_zero.mp (congrFun hh.symm ⟨i,hi⟩)

lemma sourceCosetVector_block (B C:Set S) (hT:IsSpherical M (B∪C))
    (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) (k:ℤ) (i:S) (hi:i∈B) :
    sourceCosetVector M (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) k (.inl i)=
      sourceCosetVector M (sourceCoset M (B∪C) hT x) k (.inl i) := by
  let P:=sourceCoset M (B∪C) hT x
  let R:=sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x
  apply harmonic_block_eq (framedCartan M) (Sum.inl '' B) (Sum.inl '' C)
    (framed_spherical_posDef M B (source_spherical_mono M Set.subset_union_left hT))
    (sourceCosetVector M R k) (sourceCosetVector M P k)
    (sourceCosetVector_harmonic M R k)
    (fun j=>sourceCosetVector_harmonic M P k ⟨j,Set.image_mono Set.subset_union_left j.property⟩)
    ?_ ?_ (.inl i) ⟨i,hi,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    exact sourceCartan_commuting_zero M s t (hc s hs t ht)
  · intro j hjB hjC
    rw [sourceCosetVector_open_at M R x (rightCoset_self M B x) j hjB,
      sourceCosetVector_open_at M P x (rightCoset_self M (B∪C) x) j (by
        rintro ⟨s,hs,rfl⟩
        rcases hs with hs|hs
        · exact hjB ⟨s,hs,rfl⟩
        · exact hjC ⟨s,hs,rfl⟩)]

lemma sourceCosetProduct_open_left (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) (ho:i∉P.1.val.val.1) (k:ℤ) :
    sourceCosetVector M (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      sourceCosetVector M P.1.val k (.inl i) := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  have hnot:i∉(sourceCosetProductFun M B C hT x P).val.val.1:=by
    rintro (h|h)
    · exact ho h
    · exact Set.disjoint_left.mp hd hi (P.2.property.1 h)
  have hrep:(b:Artin M)*c*x∈(sourceCosetProductFun M B C hT x P).val.val.2:=
    rightCoset_self M _ _
  have hr:(b:Artin M)*x∈P.1.val.val.2:=by
    rw [show (b:Artin M)*x=sourceCosetRepresentative M P.1.val from sourceBelowOffset_rep M B _ x P.1]
    exact sourceCosetRepresentative_mem M P.1.val
  rw [sourceCosetVector_open M _ i hnot _ hrep,
    sourceCosetVector_open M P.1.val i ho _ hr]
  have he:((b:Artin M)*c)*x=(c:Artin M)*((b:Artin M)*x):=by
    rw [(sourceParabolics_commute M B C hc b c b.property c.property).eq,mul_assoc]
  rw [he]
  apply sourceMultiplicity_exterior M C c c.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hi hs

lemma sourceCosetProduct_open_right (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) (ho:i∉P.2.val.val.1) (k:ℤ) :
    sourceCosetVector M (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      sourceCosetVector M P.2.val k (.inl i) := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  have hnot:i∉(sourceCosetProductFun M B C hT x P).val.val.1:=by
    rintro (h|h)
    · exact Set.disjoint_left.mp hd (P.1.property.1 h) hi
    · exact ho h
  have hrep:(b:Artin M)*c*x∈(sourceCosetProductFun M B C hT x P).val.val.2:=
    rightCoset_self M _ _
  have hr:(c:Artin M)*x∈P.2.val.val.2:=by
    rw [show (c:Artin M)*x=sourceCosetRepresentative M P.2.val from sourceBelowOffset_rep M C _ x P.2]
    exact sourceCosetRepresentative_mem M P.2.val
  rw [sourceCosetVector_open M _ i hnot _ hrep,
    sourceCosetVector_open M P.2.val i ho _ hr,mul_assoc]
  apply sourceMultiplicity_exterior M B b b.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hs hi

end HarmonicArtin

end OAI
