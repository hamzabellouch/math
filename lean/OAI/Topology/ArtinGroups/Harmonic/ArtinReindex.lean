import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.EarlierLowerOrderIso

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
universe u v
variable {S:Type u} {T:Type v} (M:CoxeterMatrix S) (e:S≃T)

lemma alternating_reindex (s t:S) (n:ℕ) :
    FreeGroup.freeGroupCongr e (alternating s t n)=alternating (e s) (e t) n := by
  induction n generalizing s t with
  | zero=>simp [alternating]
  | succ n ih=>
    simp only [alternating,map_mul]
    change FreeGroup.of (e s)*FreeGroup.freeGroupCongr e (alternating t s n)=_
    rw [ih]

lemma braidRelators_reindex :
    FreeGroup.freeGroupCongr e '' braidRelators M=braidRelators (M.reindex e) := by
  ext z
  constructor
  · rintro ⟨r,⟨⟨s,t⟩,rfl⟩,rfl⟩
    refine ⟨(e s,e t),?_⟩
    simp only [CoxeterMatrix.reindex_apply,e.symm_apply_apply,map_mul,map_inv,alternating_reindex]
  · rintro ⟨⟨s,t⟩,rfl⟩
    refine ⟨alternating (e.symm s) (e.symm t) (M (e.symm s) (e.symm t))*
      (alternating (e.symm t) (e.symm s) (M (e.symm s) (e.symm t)))⁻¹,
      ⟨(e.symm s,e.symm t),rfl⟩,?_⟩
    simp only [CoxeterMatrix.reindex_apply,map_mul,map_inv,alternating_reindex,e.apply_symm_apply]

noncomputable def artinReindex : Artin M≃*Artin (M.reindex e) :=
  QuotientGroup.congr (Subgroup.normalClosure (braidRelators M))
    (Subgroup.normalClosure (braidRelators (M.reindex e))) (FreeGroup.freeGroupCongr e)
    (by
      rw [← braidRelators_reindex M e]
      exact Subgroup.map_normalClosure _ _ (FreeGroup.freeGroupCongr e).surjective)

lemma artinReindex_generator (s:S) : artinReindex M e (generator M s)=generator (M.reindex e) (e s) :=rfl

lemma artinParabolic_reindex (A:Set S) :
    (artinParabolic M A).map (artinReindex M e).toMonoidHom=artinParabolic (M.reindex e) (e '' A) := by
  rw [artinParabolic,artinParabolic,MonoidHom.map_closure,Set.image_image,Set.image_image]
  congr 1

lemma coxeterParabolic_reindex (A:Set S) :
    (coxeterParabolic M A).map (M.reindexGroupEquiv e).symm.toMonoidHom=
      coxeterParabolic (M.reindex e) (e '' A) := by
  rw [coxeterParabolic,coxeterParabolic,MonoidHom.map_closure,Set.image_image,Set.image_image]
  congr 1

lemma spherical_reindex (A:Set S) : IsSpherical (M.reindex e) (e '' A) ↔ IsSpherical M A := by
  let f:coxeterParabolic M A≃*coxeterParabolic (M.reindex e) (e '' A):=
    ((M.reindexGroupEquiv e).symm.subgroupMap (coxeterParabolic M A)).trans
      (MulEquiv.subgroupCongr (coxeterParabolic_reindex M e A))
  constructor
  · intro h
    let :Finite (coxeterParabolic (M.reindex e) (e '' A)):=h
    exact Finite.of_equiv _ f.toEquiv.symm
  · intro h
    let :Finite (coxeterParabolic M A):=h
    exact Finite.of_equiv _ f.toEquiv

lemma artinParabolic_reindex_mem (A:Set S) (x:Artin M) :
    artinReindex M e x∈artinParabolic (M.reindex e) (e '' A) ↔ x∈artinParabolic M A := by
  rw [← artinParabolic_reindex]
  exact Subgroup.mem_map_iff_mem (artinReindex M e).injective

lemma rightCoset_reindex (A:Set S) (x:Artin M) :
    artinReindex M e '' rightCoset M A x=rightCoset (M.reindex e) (e '' A) (artinReindex M e x) := by
  ext y
  obtain ⟨z,rfl⟩:=(artinReindex M e).surjective y
  have he:(artinReindex M e z∈artinReindex M e '' rightCoset M A x) ↔ z∈rightCoset M A x:=by
    constructor
    · rintro ⟨a,ha,he⟩
      exact (artinReindex M e).injective he ▸ ha
    · intro h
      exact ⟨z,h,rfl⟩
  rw [he]
  change (z*x⁻¹∈artinParabolic M A) ↔ _
  rw [rightCoset,Set.mem_ofPred_eq,← map_inv,← map_mul,artinParabolic_reindex_mem]

noncomputable def deligneReindexMap : Deligne M →o Deligne (M.reindex e) where
  toFun P:=⟨(e '' P.val.1,artinReindex M e '' P.val.2),(spherical_reindex M e P.val.1).mpr P.property.1,by
    obtain ⟨x,hx⟩:=P.property.2
    exact ⟨artinReindex M e x,by rw [hx,rightCoset_reindex]⟩⟩
  monotone':=fun _ _ h=>⟨Set.image_mono h.1,Set.image_mono h.2⟩

lemma deligneReindex_le_iff (P Q:Deligne M) :
    deligneReindexMap M e P≤deligneReindexMap M e Q ↔ P≤Q := by
  change (e '' P.val.1⊆e '' Q.val.1 ∧ artinReindex M e '' P.val.2⊆artinReindex M e '' Q.val.2) ↔ _
  rw [Set.image_subset_image_iff e.injective,Set.image_subset_image_iff (artinReindex M e).injective]
  rfl

lemma deligneReindex_surjective : Function.Surjective (deligneReindexMap M e) := by
  intro Q
  let A:=e ⁻¹' Q.val.1
  have hA:e '' A=Q.val.1:=Set.image_preimage_eq _ e.surjective
  have hsp:IsSpherical M A:=(spherical_reindex M e A).mp (by rw [hA];exact Q.property.1)
  obtain ⟨y,hy⟩:=Q.property.2
  obtain ⟨x,rfl⟩:=(artinReindex M e).surjective y
  refine ⟨⟨(A,rightCoset M A x),hsp,x,rfl⟩,?_⟩
  apply Subtype.ext
  change (e '' A,artinReindex M e '' rightCoset M A x)=Q.val
  rw [rightCoset_reindex,hA,← hy]

noncomputable def deligneReindex : Deligne M≃oDeligne (M.reindex e) where
  toEquiv:=Equiv.ofBijective (deligneReindexMap M e) ⟨by
    intro P Q h
    exact le_antisymm ((deligneReindex_le_iff M e P Q).mp (le_of_eq h))
      ((deligneReindex_le_iff M e Q P).mp (le_of_eq h.symm)),deligneReindex_surjective M e⟩
  map_rel_iff':=deligneReindex_le_iff M e _ _

theorem deligne_contractible [Finite S] : ContractibleSpace (DeligneRealization M) := by
  let :=Fintype.ofFinite S
  let e:=Fintype.equivFin S
  have hc:ContractibleSpace (OrderWeights (Deligne (M.reindex e))):=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (sourceDeligne_contractible (M.reindex e))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mpr
    ((weightHomeomorph (deligneReindex M e)).contractibleSpace_iff.mpr hc)

end HarmonicArtin

end OAI
