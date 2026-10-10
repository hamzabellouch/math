import Mathlib
import OAI.Topology.ArtinGroups.Realizations.EarlierUpperContractible
import OAI.Topology.ArtinGroups.Realizations.WeightColor
import OAI.Topology.ArtinGroups.Realizations.NegativeBlockContractible

namespace OAI

namespace HarmonicArtin
open CategoryTheory Simplicial

attribute [local instance] Classical.decEq Classical.propDecidable
variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S)

noncomputable def sourceEarlierLowerOrderIso (P:Deligne M) :
    WeightEarlierLower (SourceEarlier M) P ≃o SourceEarlierLower M P where
  toFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  invFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

noncomputable def sourceEarlierUpperOrderIso (P:Deligne M) :
    WeightEarlierUpper (SourceEarlier M) P ≃o SourceEarlierUpper M P where
  toFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  invFun Q:=⟨Q.val,Q.property.2,Q.property.1⟩
  left_inv _:=rfl
  right_inv _:=rfl
  map_rel_iff':=Iff.rfl

lemma sourceEarlierLower_contractible (P:Deligne M) (h:Nonempty (SourceEarlierLower M P)) :
    ContractibleSpace |nerve (SourceEarlierLower M P)| := by
  have he:=sourceEarlierLower_equiv_allEligible M P
  have hc:ContractibleSpace |nerve (SourceAllEligibleLower M P)|:=
    nerveWeightsHomeomorph.contractibleSpace_iff.mpr
      (sourceAllEligibleLower_contractible M P (Nonempty.map (sourceAllEligibleProjection M P) h))
  exact he.contractibleSpace_iff.mpr hc

theorem sourceDeligne_contractible : ContractibleSpace (DeligneRealization M) := by
  let:=deligne_connected M
  apply nerveWeightsHomeomorph.contractibleSpace_iff.mpr
  apply orderWeights_contractible_connected (SourceEarlier M) (sourceEarlier_wellFounded M)
    (fun x y h=>by
      rcases sourceEarlier_trichotomy M x y with h'|h'|h'
      · exact Or.inl h'
      · exact (h h').elim
      · exact Or.inr h')
    (fun P=>P.val.1.ncard) (Fintype.card S) (sourceDeligne_rank_bound M)
    (sourceDeligne_rank_strictMono M)
  · intro P h
    let e:=sourceEarlierLowerOrderIso M P
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      (nerveWeightsHomeomorph.contractibleSpace_iff.mp
        (sourceEarlierLower_contractible M P (Nonempty.map e h)))
  · intro P h
    let e:=sourceEarlierUpperOrderIso M P
    exact (weightHomeomorph e).contractibleSpace_iff.mpr
      (nerveWeightsHomeomorph.contractibleSpace_iff.mp
        (sourceEarlierUpper_contractible M P (Nonempty.map e h)))

end HarmonicArtin

end OAI
