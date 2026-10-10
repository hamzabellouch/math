import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativeLowerContractible
import OAI.Topology.ArtinGroups.ParabolicIntersections.RelativePoset
import OAI.Topology.ArtinGroups.ParabolicIntersections.ConnectedMinima
import OAI.Topology.ArtinGroups.Realizations.WeightColor

namespace OAI

/-! Comparability paths in the descending lower neighborhood. -/
namespace HarmonicArtin.ParabolicIntersections
open CategoryTheory Simplicial
attribute [local instance] Classical.decEq Classical.propDecidable

lemma orderWeights_comparability_connected {V:Type} [PartialOrder V]
    (h:ContractibleSpace (OrderWeights V)) (a b:V) :
    Relation.ReflTransGen (fun x y:V => x≤y ∨ y≤x) a b := by
  let s : Setoid V :=
    { r := Relation.ReflTransGen (fun x y:V => x≤y ∨ y≤x)
      iseqv :=
        { refl := fun _ => .refl
          symm := by
            intro x y hp
            induction hp with
            | refl => exact .refl
            | @tail z w hp edge ih =>
              exact (Relation.ReflTransGen.single (r:=fun x y:V => x≤y ∨ y≤x)
                (edge.elim Or.inr Or.inl)).trans ih
          trans := fun h₁ h₂ => h₁.trans h₂ } }
  have he : Quotient.mk s a = Quotient.mk s b :=
    orderWeights_colors_eq h (Quotient.mk s)
      (fun x y hxy => Quotient.sound (Relation.ReflTransGen.single (r:=fun x y:V => x≤y ∨ y≤x)
        (Or.inl hxy))) a b
  exact Quotient.exact he

variable {S:Type} [Fintype S] [LinearOrder S] (M:CoxeterMatrix S) (f:S)
  (U:Set (S ⊕ Unit)) (cutoff:ℤ)

theorem relativeDescendingLower_contractible (P:Deligne M)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P∈artinParabolic M {f}ᶜ)
    (hne:Nonempty (RelativeDescendingLower M f U cutoff P)) :
    ContractibleSpace (OrderWeights (RelativeDescendingLower M f U cutoff P)) := by
  have he:=relativeEarlierLower_equiv_allEligible M f U cutoff P
  have hc:ContractibleSpace |nerve (RelativeAllEligibleLower M f U cutoff P)|:=
    nerveWeightsHomeomorph.contractibleSpace_iff.mpr
      (relativeAllEligibleLower_contractible M f U cutoff P hU hf hxA
        (Nonempty.map (relativeAllEligibleProjection M f U cutoff P) hne))
  exact nerveWeightsHomeomorph.contractibleSpace_iff.mp (he.contractibleSpace_iff.mpr hc)

def RelativeStrictLower {Y:Set S} {x:Artin M} (P R:RelativeVertex M Y x) : Prop :=
  R<P ∧ relativeHeight M f U cutoff R.val < relativeHeight M f U cutoff P.val

/-- Any two descending lower neighbors are joined within that same neighborhood. -/
theorem relative_descending_lower_connected {Y:Set S} {x:Artin M} (P:RelativeVertex M Y x)
    (hU:U⊆Set.range (Sum.inl:S→S⊕Unit)) (hf:(.inl f:S⊕Unit)∉U)
    (hxA:sourceCosetRepresentative M P.val∈artinParabolic M {f}ᶜ)
    (R Q:RelativeVertex M Y x)
    (hR:RelativeStrictLower M f U cutoff P R) (hQ:RelativeStrictLower M f U cutoff P Q) :
    PathWithin (relativeAdjacent M) (RelativeStrictLower M f U cutoff P) R Q := by
  let A:RelativeDescendingLower M f U cutoff P.val:=⟨R.val,hR⟩
  let B:RelativeDescendingLower M f U cutoff P.val:=⟨Q.val,hQ⟩
  let e (V:RelativeDescendingLower M f U cutoff P.val) : RelativeVertex M Y x :=
    ⟨V.val, V.property.1.le.1.trans P.property.1, V.property.1.le.2.trans P.property.2⟩
  have hc:=relativeDescendingLower_contractible M f U cutoff P.val hU hf hxA ⟨A⟩
  have hp:=orderWeights_comparability_connected hc A B
  exact Relation.ReflTransGen.lift e (fun a b hab =>
    ⟨a.property,b.property,hab.elim Or.inl Or.inr⟩) A B hp

end HarmonicArtin.ParabolicIntersections

end OAI
