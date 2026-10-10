import Mathlib
import OAI.Topology.ArtinGroups.Realizations.DeligneRankBound
import OAI.Topology.ArtinGroups.Harmonic.EligibleWithin
import OAI.Topology.ArtinGroups.Harmonic.BinaryProductBoundary

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

lemma sourceEligible_factor_iff (P R V:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,sourcePeak M P i=q)
    (hs:∀i∈R.val.1,sourceCosetSign M P q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,sourceCosetVector M R q (.inl i)=sourceCosetVector M P q (.inl i))
    (i:S) (hi:i∈R.val.1) (ho:i∉V.val.1) :
    SourceEligible M P V i ↔
      (∀d:ℤ,(q:ℤ)<d→sourceCosetVector M V d (.inl i)=0) ∧
      (if strict then sourceCosetVector M V q (.inl i)<sourceCosetVector M R q (.inl i)
        else sourceCosetVector M V q (.inl i) ≤ sourceCosetVector M R q (.inl i)) := by
  have hcap:(∀d:ℕ,q<d→sourceCosetVector M V d (.inl i)=0) ↔
      (∀d:ℤ,(q:ℤ)<d→sourceCosetVector M V d (.inl i)=0):=by
    constructor
    · intro h d hd
      have hn:0≤d:=by omega
      have he:(d.toNat:ℤ)=d:=Int.toNat_of_nonneg hn
      rw [←he]
      exact h d.toNat (by omega)
    · intro h d hd
      exact h d (by exact_mod_cast hd)
  simp only [SourceEligible,hRP hi,ho,true_and,hp i hi,hcap,hs i hi,←hv i hi]
  cases strict <;> simp only [Bool.false_eq_true,↓reduceIte,Int.reduceNeg,Int.reduceEq,not_false_eq_true,true_and,and_true,
    and_false,or_false]
  constructor
  · rintro ⟨ha,hb⟩
    exact ⟨ha,hb.elim le_of_lt le_of_eq⟩
  · rintro ⟨ha,hb⟩
    exact ⟨ha,lt_or_eq_of_le hb⟩

noncomputable def sourceEligibleFactor (P R:Deligne M) (hRP:R.val.1⊆P.val.1)
    (q:ℕ) (strict:Bool) (hp:∀i∈R.val.1,sourcePeak M P i=q)
    (hs:∀i∈R.val.1,sourceCosetSign M P q (.inl i)=if strict then -1 else 1)
    (hv:∀i∈R.val.1,sourceCosetVector M R q (.inl i)=sourceCosetVector M P q (.inl i)) :
    {V:SourceEligibleWithin M P R // V≠⊤} ≃o SourceResidue M strict R q where
  toFun V:=⟨V.val.val,lt_of_le_of_ne V.val.property.1 (fun he=>V.property (Subtype.ext he)),
    fun i hi ho=>(sourceEligible_factor_iff M P R V.val.val hRP q strict hp hs hv i hi ho).mp
      (V.val.property.2 i hi ho)⟩
  invFun V:=⟨⟨V.val,V.property.1.le,fun i hi ho=>
    (sourceEligible_factor_iff M P R V.val hRP q strict hp hs hv i hi ho).mpr (V.property.2 i hi ho)⟩,
    fun he=>V.property.1.ne (congrArg Subtype.val he)⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=by intros;rfl

noncomputable def sourceEligibleProductPuncture (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M) :
    BinaryProductBoundary
      (SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x))
      (SourceEligibleWithin M Ref (sourceCoset M C (source_spherical_mono M Set.subset_union_right hT) x)) ≃o
      {V:SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) //V≠⊤} :=
  { toFun:=fun V=>⟨sourceEligibleProduct M Ref B C hT hd hc x V.val,by
      intro he
      exact V.property ((sourceEligibleProduct M Ref B C hT hd hc x).injective
        (he.trans (sourceEligibleProduct M Ref B C hT hd hc x).map_top.symm))⟩
    invFun:=fun V=>⟨(sourceEligibleProduct M Ref B C hT hd hc x).symm V.val,by
      intro he
      apply V.property
      rw [←(sourceEligibleProduct M Ref B C hT hd hc x).apply_symm_apply V.val,he,
        (sourceEligibleProduct M Ref B C hT hd hc x).map_top]⟩
    left_inv:=fun V=>Subtype.ext ((sourceEligibleProduct M Ref B C hT hd hc x).symm_apply_apply V.val)
    right_inv:=fun V=>Subtype.ext ((sourceEligibleProduct M Ref B C hT hd hc x).apply_symm_apply V.val)
    map_rel_iff':=by intros;exact (sourceEligibleProduct M Ref B C hT hd hc x).map_rel_iff }

theorem sourceEligibleProduct_contractible (Ref:Deligne M) (B C:Set S) (hT:IsSpherical M (B∪C))
    (hd:Disjoint B C) (hc:∀s∈B,∀t∈C,M s t=2) (x:Artin M)
    (h:ContractibleSpace (OrderWeights
      {V:SourceEligibleWithin M Ref (sourceCoset M B (source_spherical_mono M Set.subset_union_left hT) x) //V≠⊤})) :
    ContractibleSpace (OrderWeights {V:SourceEligibleWithin M Ref (sourceCoset M (B∪C) hT x) //V≠⊤}) := by
  let e:=sourceEligibleProductPuncture M Ref B C hT hd hc x
  apply (weightHomeomorph e).contractibleSpace_iff.mp
  apply binaryProductBoundary_contractible (fun V=>(e V).val.val.val.1.ncard) (Fintype.card S)
    (fun V=>sourceDeligne_rank_bound M (e V).val.val) ?_ h
  intro V W hVW
  exact sourceDeligne_rank_strictMono M (e.strictMono hVW)

end HarmonicArtin

end OAI
