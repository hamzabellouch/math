import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ArtinReindex
import OAI.Topology.ArtinGroups.Harmonic.LiftedDeck
import OAI.Topology.ArtinGroups.Realizations.OrderWeightsContractibleLower2

namespace OAI

namespace HarmonicArtin
universe u
variable {S:Type u} (M:CoxeterMatrix S)

def typedRightCoset (T:Set S) (hT:IsSpherical M T) (x:Artin M) : Deligne M :=
  ⟨(T,rightCoset M T x),hT,x,rfl⟩

lemma cellToDeligne_le_typedRightCoset (a:LiftedCell M) (T:Set S)
    (hT:IsSpherical M T) (x:Artin M) :
    cellToDeligne M a≤typedRightCoset M T hT x ↔
      a.2.val⊆T ∧ x*a.1∈artinParabolic M T := by
  change (a.2.val⊆T ∧ rightCoset M a.2.val a.1⁻¹⊆rightCoset M T x) ↔ _
  constructor
  · rintro ⟨ht,hc⟩
    refine ⟨ht,?_⟩
    have ha:a.1⁻¹∈rightCoset M a.2.val a.1⁻¹:=by
      change a.1⁻¹*(a.1⁻¹)⁻¹∈artinParabolic M a.2.val
      simp
    have hi: a.1⁻¹*x⁻¹∈artinParabolic M T:=hc ha
    simpa using (artinParabolic M T).inv_mem hi
  · rintro ⟨ht,hx⟩
    refine ⟨ht,?_⟩
    intro g hg
    change g*(a.1⁻¹)⁻¹∈artinParabolic M a.2.val at hg
    change g*x⁻¹∈artinParabolic M T
    have hga: g*a.1∈artinParabolic M T:=artinParabolic_mono M ht (by simpa using hg)
    have hh:=(artinParabolic M T).mul_mem hga ((artinParabolic M T).inv_mem hx)
    simpa only [mul_inv_rev,mul_assoc,mul_inv_cancel_left] using hh

def liftedLowerFiberIso (T:Set S) (hT:IsSpherical M T) (x:Artin M) :
    {a:LiftedCell M // cellToDeligneOrderHom M a≤typedRightCoset M T hT x} ≃o
      SphericalLiftedFiber M T where
  toFun a:=⟨liftedDeck M x a.val,(cellToDeligne_le_typedRightCoset M a.val T hT x).mp a.property⟩
  invFun a:=⟨liftedDeck M x⁻¹ a.val,by
    apply (cellToDeligne_le_typedRightCoset M _ T hT x).mpr
    exact ⟨a.property.1,by simpa [liftedDeck,mul_assoc] using a.property.2⟩⟩
  left_inv:=by intro a;apply Subtype.ext;ext <;> simp [liftedDeck]
  right_inv:=by intro a;apply Subtype.ext;ext <;> simp [liftedDeck]
  map_rel_iff':=by intro a b;exact (liftedDeck M x).map_rel_iff

lemma deligne_same_type_eq {P Q:Deligne M} (h:P≤Q) (ht:P.val.1=Q.val.1) : P=Q := by
  obtain ⟨x,hx⟩:=P.property.2
  obtain ⟨y,hy⟩:=Q.property.2
  have hxm:x∈P.val.2:=by rw [hx];change x*x⁻¹∈artinParabolic M P.val.1;simp
  have hxy:x*y⁻¹∈artinParabolic M Q.val.1:=by simpa [hy,rightCoset] using h.2 hxm
  apply Subtype.ext
  apply Prod.ext ht
  apply Set.Subset.antisymm h.2
  intro z hz
  rw [hx]
  change z*x⁻¹∈artinParabolic M P.val.1
  rw [ht]
  have hzy:z*y⁻¹∈artinParabolic M Q.val.1:=by simpa [hy,rightCoset] using hz
  have hh:=(artinParabolic M Q.val.1).mul_mem hzy ((artinParabolic M Q.val.1).inv_mem hxy)
  simpa only [mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel_left] using hh

lemma deligne_type_strict {P Q:Deligne M} (h:P<Q) : P.val.1⊂Q.val.1 :=
  lt_of_le_of_ne h.le.1 (fun he=>h.ne (deligne_same_type_eq M h.le he))

lemma deligne_card_strict [Finite S] : StrictMono (fun P:Deligne M=>P.val.1.ncard) := by
  intro P Q h
  exact Set.ncard_lt_ncard (deligne_type_strict M h) (Set.toFinite _)

theorem salvetti_cover_contractible_of_spherical_fibers [Finite S]
    (h:∀T:Set S,IsSpherical M T → ContractibleSpace (OrderWeights (SphericalLiftedFiber M T))) :
    ContractibleSpace (SalvettiCover M) := by
  have hd:ContractibleSpace (OrderWeights (Deligne M)):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (deligne_contractible M)
  have hf:∀P:Deligne M,ContractibleSpace (OrderWeights {a:LiftedCell M // cellToDeligneOrderHom M a≤P}):=by
    intro P
    obtain ⟨x,hx⟩:=P.property.2
    have he:P=typedRightCoset M P.val.1 P.property.1 x:=by apply Subtype.ext;exact Prod.ext rfl hx
    rw [he]
    exact (weightHomeomorph (liftedLowerFiberIso M _ _ x)).contractibleSpace_iff.mpr (h _ P.property.1)
  have hc:ContractibleSpace (OrderWeights (LiftedCell M)):=
    orderWeights_contractible_of_lower_preimages (cellToDeligneOrderHom M)
      (fun a=>a.2.val.ncard) (fun P=>P.val.1.ncard) (Nat.card S) (Nat.card S)
      (lifted_rank_bound M) (fun _=>Set.ncard_le_card _) (lifted_rank_strict M)
      (deligne_card_strict M) hd hf
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr hc

end HarmonicArtin

end OAI
