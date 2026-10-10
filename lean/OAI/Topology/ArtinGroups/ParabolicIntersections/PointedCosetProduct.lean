import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedCosetExteriorCap
import OAI.Topology.ArtinGroups.Harmonic.CartanCommutingZero

namespace OAI

/-! Pointed multiplicities on products of commuting standard cosets. -/
namespace HarmonicArtin.ParabolicIntersections
open _root_.Matrix _root_.OAI.Matrix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)

lemma pointedCosetVector_open (P:Deligne M) (i:S) (hi:i∉P.val.1)
    (x:Artin M) (hx:x∈P.val.2) (k:ℤ) :
    pointedCosetVector M f P k (.inl i) = pointedMultiplicity M f x k (.inl i) :=
  pointedCosetVector_open_at M f P x hx (.inl i) (by
    rintro ⟨j,hj,he⟩; exact hi (Sum.inl.inj he ▸ hj)) k

lemma pointedCosetVector_block (B C:Set S) (hT:IsSpherical M (B∪C))
    (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) (k:ℤ) (i:S) (hi:i∈B) :
    pointedCosetVector M f (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) k (.inl i)=
      pointedCosetVector M f (sourceCoset M (B∪C) hT x) k (.inl i) := by
  let P:=sourceCoset M (B∪C) hT x
  let R:=sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x
  apply harmonic_block_eq (framedCartan M) (Sum.inl '' B) (Sum.inl '' C)
    (framed_spherical_posDef M B (source_spherical_mono M Set.subset_union_left hT))
    (pointedCosetVector M f R k) (pointedCosetVector M f P k)
    (pointedCosetVector_harmonic M f R k)
    (fun j=>pointedCosetVector_harmonic M f P k ⟨j,Set.image_mono Set.subset_union_left j.property⟩)
    ?_ ?_ (.inl i) ⟨i,hi,rfl⟩
  · rintro _ ⟨s,hs,rfl⟩ _ ⟨t,ht,rfl⟩
    exact sourceCartan_commuting_zero M s t (hc s hs t ht)
  · intro j hjB hjC
    rw [pointedCosetVector_open_at M f R x (rightCoset_self M B x) j hjB k,
      pointedCosetVector_open_at M f P x (rightCoset_self M (B∪C) x) j (by
        rintro ⟨s,hs,rfl⟩
        rcases hs with hs|hs
        · exact hjB ⟨s,hs,rfl⟩
        · exact hjC ⟨s,hs,rfl⟩) k]

lemma pointedCosetProduct_open_left (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈B) (ho:i∉P.1.val.val.1) (k:ℤ) :
    pointedCosetVector M f (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      pointedCosetVector M f P.1.val k (.inl i) := by
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
  rw [pointedCosetVector_open M f _ i hnot _ hrep,
    pointedCosetVector_open M f P.1.val i ho _ hr]
  have he:((b:Artin M)*c)*x=(c:Artin M)*((b:Artin M)*x):=by
    rw [(sourceParabolics_commute M B C hc b c b.property c.property).eq,_root_.mul_assoc]
  rw [he]
  apply pointedMultiplicity_exterior_ordered M f C c c.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hi hs

lemma pointedCosetProduct_open_right (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (x:Artin M)
    (P:SourceCosetBelow M B (source_spherical_mono M Set.subset_union_left hT) x ×
      SourceCosetBelow M C (source_spherical_mono M Set.subset_union_right hT) x)
    (i:S) (hi:i∈C) (ho:i∉P.2.val.val.1) (k:ℤ) :
    pointedCosetVector M f (sourceCosetProductFun M B C hT x P).val k (.inl i)=
      pointedCosetVector M f P.2.val k (.inl i) := by
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
  rw [pointedCosetVector_open M f _ i hnot _ hrep,
    pointedCosetVector_open M f P.2.val i ho _ hr,_root_.mul_assoc]
  apply pointedMultiplicity_exterior_ordered M f B b b.property
  rintro ⟨s,hs,he⟩
  cases Sum.inl_injective he
  exact Set.disjoint_left.mp hd hs hi


end HarmonicArtin.ParabolicIntersections

end OAI
