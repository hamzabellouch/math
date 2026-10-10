import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeEligibleWithin
import OAI.Topology.ArtinGroups.ParabolicIntersections.PointedResidueAllowed
import OAI.Topology.ArtinGroups.Realizations.DeligneRankBound
import OAI.Topology.ArtinGroups.Harmonic.BinaryProductBoundary

namespace OAI

namespace HarmonicArtin.ParabolicIntersections
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

lemma relativeEligible_factor_iff (P R V:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,relativePeak M f cutoff P i=q)
    (hs:∀i∈R.val.1,relativeSign M U (pointedProfile M f P cutoff) q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,pointedProfile M f R cutoff q (.inl i)=pointedProfile M f P cutoff q (.inl i))
    (i:S) (hi:i∈R.val.1) (ho:i∉V.val.1) :
    RelativeEligible M f U cutoff P V i ↔
      (∀d:ℤ,cutoff+(q:ℤ)<d→pointedCosetVector M f V d (.inl i)=0) ∧
      (if strict then pointedProfile M f V cutoff q (.inl i)<pointedProfile M f R cutoff q (.inl i)
        else pointedProfile M f V cutoff q (.inl i) ≤ pointedProfile M f R cutoff q (.inl i)) := by
  have hcap:(∀d:ℕ,q<d→pointedProfile M f V cutoff d (.inl i)=0) ↔
      (∀d:ℤ,cutoff+(q:ℤ)<d→pointedCosetVector M f V d (.inl i)=0):=by
    constructor
    · intro h d hd
      have hn:0≤d-cutoff:=by omega
      have he:cutoff+((d-cutoff).toNat:ℤ)=d:=by rw [Int.toNat_of_nonneg hn];omega
      rw [←he]
      exact h (d-cutoff).toNat (by omega)
    · intro h d hd
      have hh : (q:ℤ) < d := by exact_mod_cast hd
      exact h (cutoff+d) (by omega)
  simp only [RelativeEligible,hRP hi,ho,true_and,hp i hi,hcap,hs i hi,←hv i hi]
  cases strict <;> simp only [Bool.false_eq_true,↓reduceIte,Int.reduceNeg,Int.reduceEq,not_false_eq_true,true_and,and_true,
    and_false,or_false]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,hb.elim le_of_lt le_of_eq⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,lt_or_eq_of_le hb⟩

noncomputable def relativeEligibleFactor (P R:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,relativePeak M f cutoff P i=q)
    (hs:∀i∈R.val.1,relativeSign M U (pointedProfile M f P cutoff) q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,pointedProfile M f R cutoff q (.inl i)=pointedProfile M f P cutoff q (.inl i)) :
    {V:RelativeEligibleWithin M f U cutoff P R // V≠⊤} ≃o PointedResidue M f strict R (cutoff+q) where
  toFun V:=⟨V.val.val,lt_of_le_of_ne V.val.property.1 (fun he=>V.property (Subtype.ext he)),
    fun i hi ho=>(relativeEligible_factor_iff M f U cutoff P R V.val.val hRP q strict hp hs hv i hi ho).mp
      (V.val.property.2 i hi ho)⟩
  invFun V:=⟨⟨V.val,V.property.1.le,fun i hi ho=>
    (relativeEligible_factor_iff M f U cutoff P R V.val hRP q strict hp hs hv i hi ho).mpr (V.property.2 i hi ho)⟩,
    fun he=>V.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def relativeEligibleProductPuncture (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    BinaryProductBoundary
      (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x))
      (RelativeEligibleWithin M f U cutoff Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
      {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) //V≠⊤} :=
  { toFun:=fun V=>⟨relativeEligibleProduct M f U cutoff Ref B C hT hd hc x V.val,by
      intro he
      exact V.property ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).injective
        (he.trans (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_top.symm))⟩
    invFun:=fun V=>⟨(relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).symm V.val,by
      intro he
      apply V.property
      rw [←(relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).apply_symm_apply V.val,he,
        (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_top]⟩
    left_inv:=fun V=>Subtype.ext ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).symm_apply_apply V.val)
    right_inv:=fun V=>Subtype.ext ((relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).apply_symm_apply V.val)
    map_rel_iff':=by intros;exact (relativeEligibleProduct M f U cutoff Ref B C hT hd hc x).map_rel_iff }

theorem relativeEligibleProduct_contractible (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (h:ContractibleSpace (OrderWeights
      {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights {V:RelativeEligibleWithin M f U cutoff Ref (sourceCoset M (B∪C) hT x) //V≠⊤}) := by
  let e:=relativeEligibleProductPuncture M f U cutoff Ref B C hT hd hc x
  apply (weightHomeomorph e).contractibleSpace_iff.mp
  apply binaryProductBoundary_contractible (fun V=>(e V).val.val.val.1.ncard) (Fintype.card S)
    (fun V=>sourceDeligne_rank_bound M (e V).val.val) ?_ h
  intro V W hVW
  exact sourceDeligne_rank_strictMono M (e.strictMono hVW)


end HarmonicArtin.ParabolicIntersections

end OAI
