import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.ProbeFixedOutside

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

omit [Fintype S] [LinearOrder S] in
lemma sourceGenerators_commute {s t:S} (h:M s t=2) : Commute (generator M s) (generator M t) := by
  have he:=wordArtin_braid M s t
  change generator M s * generator M t = generator M t * generator M s
  simpa [h,CoxeterExchange.altList,wordArtin] using he

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolics_commute (B C:Set S) (h:∀s∈B,∀t∈C,M s t=2)
    (b c:Artin M) (hb:b∈artinParabolic M B) (hc:c∈artinParabolic M C) : Commute b c := by
  have hh:artinParabolic M B≤Subgroup.centralizer (artinParabolic M C:Set (Artin M)):=by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨s,hs,rfl⟩
    change generator M s∈Subgroup.centralizer (Subgroup.closure ((generator M) '' C):Set (Artin M))
    rw [Subgroup.centralizer_closure]
    rintro _ ⟨t,ht,rfl⟩
    exact (sourceGenerators_commute M (h s hs t ht)).symm.eq
  exact (hh hb c hc).symm

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolic_union (B C:Set S) :
    artinParabolic M (B∪C)=artinParabolic M B⊔artinParabolic M C := by
  simp only [artinParabolic,Set.image_union,Subgroup.closure_union]

noncomputable def sourceParabolicProductMap (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2) :
    artinParabolic M B × artinParabolic M C →* Artin M :=
  (artinParabolic M B).subtype.noncommCoprod (artinParabolic M C).subtype
    (fun b c=>sourceParabolics_commute M B C hc b c b.property c.property)

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolicProductMap_apply (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2)
    (x:artinParabolic M B × artinParabolic M C) :
    sourceParabolicProductMap M B C hc x=(x.1:Artin M)*x.2 :=rfl

omit [Fintype S] [LinearOrder S] in
lemma sourceParabolicProductMap_range (B C:Set S) (hc:∀s∈B,∀t∈C,M s t=2) :
    (sourceParabolicProductMap M B C hc).range=artinParabolic M (B∪C) := by
  rw [sourceParabolic_union]
  apply le_antisymm
  · rintro g ⟨⟨b,c⟩,rfl⟩
    exact Subgroup.mul_mem _
      ((show artinParabolic M B ≤ artinParabolic M B ⊔ artinParabolic M C from le_sup_left) b.property)
      ((show artinParabolic M C ≤ artinParabolic M B ⊔ artinParabolic M C from le_sup_right) c.property)
  · apply sup_le
    · intro b hb
      exact ⟨(⟨b,hb⟩,1),by simp [sourceParabolicProductMap_apply]⟩
    · intro c hc'
      exact ⟨(1,⟨c,hc'⟩),by simp [sourceParabolicProductMap_apply]⟩

lemma sourceParabolicProductMap_injective (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) :
    Function.Injective (sourceParabolicProductMap M B C hc) := by
  intro a b he
  change (a.1:Artin M)*a.2=(b.1:Artin M)*b.2 at he
  have hx:((b.1:Artin M)⁻¹*a.1)=(b.2:Artin M)*(a.2:Artin M)⁻¹ := by
    calc
      _=(b.1:Artin M)⁻¹*((a.1:Artin M)*a.2)*(a.2:Artin M)⁻¹:=by group
      _=(b.2:Artin M)*(a.2:Artin M)⁻¹:=by rw [he];group
  have hm:((b.1:Artin M)⁻¹*a.1)∈artinParabolic M B⊓artinParabolic M C:=
    ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ b.1.property) a.1.property,
      hx ▸ Subgroup.mul_mem _ b.2.property (Subgroup.inv_mem _ a.2.property)⟩
  rw [sourceParabolic_inter M (B∪C) B C hT Set.subset_union_left Set.subset_union_right,
    Set.disjoint_iff_inter_eq_empty.mp hd,sourceParabolic_empty] at hm
  have hab:(a.1:Artin M)=(b.1:Artin M):=(inv_mul_eq_one.mp (Subgroup.mem_bot.mp hm)).symm
  have hcd:(a.2:Artin M)=(b.2:Artin M):=by rw [hab] at he;exact mul_left_cancel he
  exact Prod.ext (Subtype.ext hab) (Subtype.ext hcd)

noncomputable def sourceParabolicProduct (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) :
    artinParabolic M B × artinParabolic M C ≃* artinParabolic M (B∪C) := by
  let f:=sourceParabolicProductMap M B C hc
  let g:=f.codRestrict (artinParabolic M (B∪C)) (fun x=>by
    rw [←sourceParabolicProductMap_range M B C hc];exact ⟨x,rfl⟩)
  apply MulEquiv.ofBijective g
  constructor
  · intro x y h
    exact sourceParabolicProductMap_injective M B C hT hd hc (congrArg Subtype.val h)
  · intro x
    have hx:x.val∈f.range:=by rw [sourceParabolicProductMap_range M B C hc];exact x.property
    obtain ⟨a,ha⟩:=hx
    exact ⟨a,Subtype.ext ha⟩

lemma sourceParabolicProduct_mem (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2)
    (R:Set S) (hR:R⊆B∪C) (b:artinParabolic M B) (c:artinParabolic M C) :
    (b:Artin M)*c∈artinParabolic M R ↔
      (b:Artin M)∈artinParabolic M (R∩B) ∧ (c:Artin M)∈artinParabolic M (R∩C) := by
  have hc':∀s∈R∩B,∀t∈R∩C,M s t=2:=fun s hs t ht=>hc s hs.2 t ht.2
  have he:(R∩B)∪(R∩C)=R:=by
    ext s
    constructor
    · rintro (⟨hs,_⟩|⟨hs,_⟩) <;> exact hs
    · intro hs
      rcases hR hs with h|h
      · exact Or.inl ⟨hs,h⟩
      · exact Or.inr ⟨hs,h⟩
  constructor
  · intro hh
    rw [←he,←sourceParabolicProductMap_range M (R∩B) (R∩C) hc'] at hh
    obtain ⟨⟨p,q⟩,hpq⟩:=hh
    let p':artinParabolic M B:=⟨p.val,artinParabolic_mono M Set.inter_subset_right p.property⟩
    let q':artinParabolic M C:=⟨q.val,artinParabolic_mono M Set.inter_subset_right q.property⟩
    have hh:(p',q')=(b,c):=sourceParabolicProductMap_injective M B C hT hd hc hpq
    have hpb:(p:Artin M)=(b:Artin M):=congrArg (fun z:artinParabolic M B × artinParabolic M C=>(z.1:Artin M)) hh
    have hqc:(q:Artin M)=(c:Artin M):=congrArg (fun z:artinParabolic M B × artinParabolic M C=>(z.2:Artin M)) hh
    exact ⟨hpb ▸ p.property,hqc ▸ q.property⟩
  · rintro ⟨hb,hc⟩
    exact Subgroup.mul_mem _ (artinParabolic_mono M Set.inter_subset_left hb)
      (artinParabolic_mono M Set.inter_subset_left hc)

end HarmonicArtin

end OAI
