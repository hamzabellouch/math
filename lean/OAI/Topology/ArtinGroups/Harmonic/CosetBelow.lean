import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Coset
import OAI.Topology.ArtinGroups.Coxeter.ParabolicProductMap

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_le_iff {T U:Set S} {hT:IsSpherical M T} {hU:IsSpherical M U} (x y:Artin M) :
    sourceCoset M T hT x ≤ sourceCoset M U hU y ↔ T⊆U ∧ x*y⁻¹∈artinParabolic M U := by
  constructor
  · intro h
    exact ⟨h.1,h.2 (rightCoset_self M T x)⟩
  · rintro ⟨hT,hxy⟩
    refine ⟨hT,?_⟩
    intro z hz
    change z*y⁻¹∈artinParabolic M U
    have he:z*y⁻¹=(z*x⁻¹)*(x*y⁻¹):=by group
    rw [he]
    exact Subgroup.mul_mem _ (artinParabolic_mono M hT hz) hxy

omit [Fintype S] [LinearOrder S] in
lemma sourceCoset_representative_le_iff {P R:Deligne M} (x y:Artin M) (hx:x∈P.val.2) (hy:y∈R.val.2) :
    P ≤ R ↔ P.val.1⊆R.val.1 ∧ x*y⁻¹∈artinParabolic M R.val.1 := by
  conv_lhs => rw [←sourceCoset_eq M P x hx,←sourceCoset_eq M R y hy]
  exact sourceCoset_le_iff M x y

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_types {B C R V R' V':Set S} (hd:Disjoint B C)
    (hR:R⊆B) (hV:V⊆C) (hR':R'⊆B) (hV':V'⊆C) :
    R∪V⊆R'∪V' ↔ R⊆R' ∧ V⊆V' := by
  constructor
  · intro h
    constructor
    · intro s hs
      rcases h (Or.inl hs) with hp|hp
      · exact hp
      · exact False.elim (Set.disjoint_left.mp hd (hR hs) (hV' hp))
    · intro s hs
      rcases h (Or.inr hs) with hp|hp
      · exact False.elim (Set.disjoint_left.mp hd (hR' hp) (hV hs))
      · exact hp
  · rintro ⟨h,h'⟩ s (hs|hs)
    · exact Or.inl (h hs)
    · exact Or.inr (h' hs)

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_inter {B C R V:Set S} (hd:Disjoint B C) (hR:R⊆B) (hV:V⊆C) :
    (R∪V)∩B=R ∧ (R∪V)∩C=V := by
  constructor
  · ext s
    constructor
    · rintro ⟨hs,hb⟩
      rcases hs with hs|hs
      · exact hs
      · exact False.elim (Set.disjoint_left.mp hd hb (hV hs))
    · intro hs;exact ⟨Or.inl hs,hR hs⟩
  · ext s
    constructor
    · rintro ⟨hs,hc⟩
      rcases hs with hs|hs
      · exact False.elim (Set.disjoint_left.mp hd (hR hs) hc)
      · exact hs
    · intro hs;exact ⟨Or.inr hs,hV hs⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceSplit_difference (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2)
    (b b':artinParabolic M B) (c c':artinParabolic M C) (x:Artin M) :
    ((b:Artin M)*c*x)*((b':Artin M)*c'*x)⁻¹=
      ((b:Artin M)*(b':Artin M)⁻¹)*((c:Artin M)*(c':Artin M)⁻¹) := by
  have he:=sourceParabolics_commute M B C hc ((b':Artin M)⁻¹) ((c:Artin M)*(c':Artin M)⁻¹)
    (Subgroup.inv_mem _ b'.property) (Subgroup.mul_mem _ c.property (Subgroup.inv_mem _ c'.property))
  calc
    _=(b:Artin M)*(((c:Artin M)*(c':Artin M)⁻¹)*(b':Artin M)⁻¹):=by group
    _=(b:Artin M)*((b':Artin M)⁻¹*((c:Artin M)*(c':Artin M)⁻¹)):=by rw [he.eq]
    _=_:=by group

lemma sourceSplit_coset_le (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (R V R' V':Set S) (hR:R⊆B) (hV:V⊆C) (hR':R'⊆B) (hV':V'⊆C)
    (b b':artinParabolic M B) (c c':artinParabolic M C) :
    sourceCoset M (R∪V) (source_spherical_mono M (Set.union_subset_union hR hV) hT) ((b:Artin M)*c*x) ≤
      sourceCoset M (R'∪V') (source_spherical_mono M (Set.union_subset_union hR' hV') hT) ((b':Artin M)*c'*x) ↔
    (sourceCoset M R (source_spherical_mono M (hR.trans Set.subset_union_left) hT) ((b:Artin M)*x) ≤
      sourceCoset M R' (source_spherical_mono M (hR'.trans Set.subset_union_left) hT) ((b':Artin M)*x)) ∧
    (sourceCoset M V (source_spherical_mono M (hV.trans Set.subset_union_right) hT) ((c:Artin M)*x) ≤
      sourceCoset M V' (source_spherical_mono M (hV'.trans Set.subset_union_right) hT) ((c':Artin M)*x)) := by
  rw [sourceCoset_le_iff,sourceCoset_le_iff,sourceCoset_le_iff,
    sourceSplit_types hd hR hV hR' hV',sourceSplit_difference M B C hc b b' c c' x]
  have hf:=sourceParabolicProduct_mem M B C hT hd hc (R'∪V')
    (Set.union_subset_union hR' hV') (b*b'⁻¹) (c*c'⁻¹)
  have hi:=sourceSplit_inter hd hR' hV'
  rw [hi.1,hi.2] at hf
  simp only [Subgroup.coe_mul,Subgroup.coe_inv] at hf
  have hb:((b:Artin M)*x)*((b':Artin M)*x)⁻¹=(b:Artin M)*(b':Artin M)⁻¹:=by group
  have hh:((c:Artin M)*x)*((c':Artin M)*x)⁻¹=(c:Artin M)*(c':Artin M)⁻¹:=by group
  rw [hb,hh]
  rw [hf]
  tauto

abbrev SourceCosetBelow (B:Set S) (hB:IsSpherical M B) (x:Artin M) :=
  Set.Iic (sourceCoset M B hB x)

noncomputable def sourceBelowOffset (B:Set S) (hB:IsSpherical M B) (x:Artin M)
    (P:SourceCosetBelow M B hB x) : artinParabolic M B :=
  ⟨sourceCosetRepresentative M P.val*x⁻¹,P.property.2 (sourceCosetRepresentative_mem M P.val)⟩

omit [Fintype S] [LinearOrder S] in
lemma sourceBelowOffset_rep (B:Set S) (hB:IsSpherical M B) (x:Artin M)
    (P:SourceCosetBelow M B hB x) : (sourceBelowOffset M B hB x P:Artin M)*x=sourceCosetRepresentative M P.val := by
  simp [sourceBelowOffset,mul_assoc]

noncomputable def sourceCosetProductFun (B C:Set S) (hT:IsSpherical M (B∪C)) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    SourceCosetBelow M (B∪C) hT x := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  let R:=P.1.val.val.1∪P.2.val.val.1
  have hR:R⊆B∪C:=Set.union_subset_union P.1.property.1 P.2.property.1
  refine ⟨sourceCoset M R (source_spherical_mono M hR hT) ((b:Artin M)*c*x),?_⟩
  apply (sourceCoset_le_iff M _ _).mpr
  refine ⟨hR,?_⟩
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using
    Subgroup.mul_mem (artinParabolic M (B∪C))
      (artinParabolic_mono M Set.subset_union_left b.property)
      (artinParabolic_mono M Set.subset_union_right c.property)

lemma sourceCosetProductFun_le_iff (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P R:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) :
    sourceCosetProductFun M B C hT x P ≤ sourceCosetProductFun M B C hT x R ↔ P≤R := by
  let b:=sourceBelowOffset M B _ x P.1
  let c:=sourceBelowOffset M C _ x P.2
  let b':=sourceBelowOffset M B _ x R.1
  let c':=sourceBelowOffset M C _ x R.2
  change sourceCoset M _ (source_spherical_mono M (Set.union_subset_union P.1.property.1 P.2.property.1) hT) ((b:Artin M)*c*x) ≤ sourceCoset M _ (source_spherical_mono M (Set.union_subset_union R.1.property.1 R.2.property.1) hT) ((b':Artin M)*c'*x) ↔ _
  rw [sourceCoset_le_iff,sourceSplit_types hd P.1.property.1 P.2.property.1 R.1.property.1 R.2.property.1,
    sourceSplit_difference M B C hc b b' c c' x]
  have hf:=sourceParabolicProduct_mem M B C hT hd hc (R.1.val.val.1∪R.2.val.val.1)
    (Set.union_subset_union R.1.property.1 R.2.property.1)
    (b*b'⁻¹) (c*c'⁻¹)
  have hi:=sourceSplit_inter hd R.1.property.1 R.2.property.1
  rw [hi.1,hi.2] at hf
  simp only [Subgroup.coe_mul,Subgroup.coe_inv] at hf
  change ((P.1.val.val.1⊆R.1.val.val.1 ∧ P.2.val.val.1⊆R.2.val.val.1) ∧ _) ↔ _
  rw [hf]
  have hb:((b:Artin M)*(b':Artin M)⁻¹)=sourceCosetRepresentative M P.1.val*(sourceCosetRepresentative M R.1.val)⁻¹:=by
    dsimp [b,b',sourceBelowOffset];group
  have hc':((c:Artin M)*(c':Artin M)⁻¹)=sourceCosetRepresentative M P.2.val*(sourceCosetRepresentative M R.2.val)⁻¹:=by
    dsimp [c,c',sourceBelowOffset];group
  rw [hb,hc']
  change _ ↔ P.1.val ≤ R.1.val ∧ P.2.val ≤ R.2.val
  rw [sourceCoset_representative_le_iff M _ _ (sourceCosetRepresentative_mem M _) (sourceCosetRepresentative_mem M _),
    sourceCoset_representative_le_iff M _ _ (sourceCosetRepresentative_mem M _) (sourceCosetRepresentative_mem M _)]
  tauto

lemma sourceCosetProductFun_eq_of_reps (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (b:artinParabolic M B) (c:artinParabolic M C)
    (hb:(b:Artin M)*x∈P.1.val.val.2) (hcc:(c:Artin M)*x∈P.2.val.val.2) :
    (sourceCosetProductFun M B C hT x P).val=
      sourceCoset M (P.1.val.val.1∪P.2.val.val.1)
        (source_spherical_mono M (Set.union_subset_union P.1.property.1 P.2.property.1) hT) ((b:Artin M)*c*x) := by
  let a:=sourceBelowOffset M B _ x P.1
  let d:=sourceBelowOffset M C _ x P.2
  have h₁:sourceCoset M P.1.val.val.1 P.1.val.property.1 ((a:Artin M)*x)=
      sourceCoset M P.1.val.val.1 P.1.val.property.1 ((b:Artin M)*x):=by
    rw [sourceBelowOffset_rep M B _ x P.1,
      sourceCoset_eq M P.1.val _ (sourceCosetRepresentative_mem M P.1.val),sourceCoset_eq M P.1.val _ hb]
  have h₂:sourceCoset M P.2.val.val.1 P.2.val.property.1 ((d:Artin M)*x)=
      sourceCoset M P.2.val.val.1 P.2.val.property.1 ((c:Artin M)*x):=by
    rw [sourceBelowOffset_rep M C _ x P.2,
      sourceCoset_eq M P.2.val _ (sourceCosetRepresentative_mem M P.2.val),sourceCoset_eq M P.2.val _ hcc]
  apply le_antisymm
  · exact (sourceSplit_coset_le M B C hT hd hc x _ _ _ _ P.1.property.1 P.2.property.1
      P.1.property.1 P.2.property.1 a b d c).mpr ⟨h₁.le,h₂.le⟩
  · exact (sourceSplit_coset_le M B C hT hd hc x _ _ _ _ P.1.property.1 P.2.property.1
      P.1.property.1 P.2.property.1 b a c d).mpr ⟨h₁.ge,h₂.ge⟩

lemma sourceCosetProductFun_surjective (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    Function.Surjective (sourceCosetProductFun M B C hT x) := by
  intro P
  let z:=sourceCosetRepresentative M P.val
  have hz:=sourceCosetRepresentative_mem M P.val
  have hg:z*x⁻¹∈artinParabolic M (B∪C):=P.property.2 hz
  rw [←sourceParabolicProductMap_range M B C hc] at hg
  obtain ⟨⟨b,c⟩,he⟩:=hg
  change (b:Artin M)*c=z*x⁻¹ at he
  have he':(b:Artin M)*c*x=z:=by rw [he];group
  let R:=P.val.val.1∩B
  let V:=P.val.val.1∩C
  have hR:R⊆B:=Set.inter_subset_right
  have hV:V⊆C:=Set.inter_subset_right
  have hRV:R∪V=P.val.val.1:=by
    ext s
    constructor
    · rintro (⟨hs,_⟩|⟨hs,_⟩) <;> exact hs
    · intro hs
      rcases P.property.1 hs with hb|hc
      · exact Or.inl ⟨hs,hb⟩
      · exact Or.inr ⟨hs,hc⟩
  let PB:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x:=
    ⟨sourceCoset M R (source_spherical_mono M (hR.trans Set.subset_union_left) hT) ((b:Artin M)*x),
      (sourceCoset_le_iff M _ _).mpr ⟨hR,by simpa only [mul_assoc,mul_inv_cancel,mul_one] using b.property⟩⟩
  let PC:SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x:=
    ⟨sourceCoset M V (source_spherical_mono M (hV.trans Set.subset_union_right) hT) ((c:Artin M)*x),
      (sourceCoset_le_iff M _ _).mpr ⟨hV,by simpa only [mul_assoc,mul_inv_cancel,mul_one] using c.property⟩⟩
  refine ⟨(PB,PC),Subtype.ext ?_⟩
  rw [sourceCosetProductFun_eq_of_reps M B C hT hd hc x (PB,PC) b c
    (rightCoset_self M R _) (rightCoset_self M V _)]
  change sourceCoset M (R∪V) _ ((b:Artin M)*c*x)=P.val
  simp only [hRV,he']
  exact sourceCoset_eq M P.val z hz

noncomputable def sourceCosetProduct (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    (SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x) ≃o
      SourceCosetBelow M (B∪C) hT x :=
  OrderIso.ofSurjective
    (OrderEmbedding.ofMapLEIff (sourceCosetProductFun M B C hT x)
      (sourceCosetProductFun_le_iff M B C hT hd hc x))
    (sourceCosetProductFun_surjective M B C hT hd hc x)

end HarmonicArtin

end OAI
