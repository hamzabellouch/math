import Mathlib
import OAI.Topology.ArtinGroups.Realizations.SalvettiCoverContractible

namespace OAI

namespace HarmonicArtin
open Topology

attribute [local instance] Classical.decEq Classical.propDecidable
universe u
variable {S : Type u} (M : CoxeterMatrix S)

def liftedDeckOrderHom (g : Artin M) : LiftedCell M →o LiftedCell M := liftedDeck M g

noncomputable instance liftedWeightsMulAction : MulAction (Artin M) (OrderWeights (LiftedCell M)) where
  smul g x := weightMap (liftedDeckOrderHom M g) x
  one_smul x := by
    have h : (liftedDeckOrderHom M 1) = OrderHom.id := by
      apply OrderHom.ext
      funext a
      exact Prod.ext (one_mul a.1) rfl
    change weightMap _ x = x
    rw [h,weightMap_id]
  mul_smul g h x := by
    have he : (liftedDeckOrderHom M g).comp (liftedDeckOrderHom M h) =
        (liftedDeckOrderHom M (g*h)) := by
      apply OrderHom.ext
      funext a
      exact Prod.ext (mul_assoc g h a.1).symm rfl
    change weightMap _ x = weightMap _ (weightMap _ x)
    rw [weightMap_comp,he]

instance liftedWeightsContinuousAction : ContinuousConstSMul (Artin M) (OrderWeights (LiftedCell M)) where
  continuous_const_smul g := weightMap_continuous (liftedDeckOrderHom M g)

lemma liftedWeights_smul_apply (g : Artin M) (x : OrderWeights (LiftedCell M)) (a : LiftedCell M) :
    (g • x).weights (liftedDeck M g a) = x.weights a :=
  weightMap_apply_embedding (liftedDeckOrderHom M g) (liftedDeck M g).injective x a

lemma liftedDeck_comparable (g : Artin M) (a : LiftedCell M)
    (h : a ≤ liftedDeck M g a ∨ liftedDeck M g a ≤ a) : g = 1 := by
  have he : liftedDeck M g a = a := by
    rcases h with h|h
    · exact (lifted_eq_of_le_type_eq M h rfl).symm
    · exact lifted_eq_of_le_type_eq M h rfl
  have hh := congrArg (fun c : LiftedCell M => c.1) he
  change g*a.1 = a.1 at hh
  have hg : g*a.1 = 1*a.1 := by simpa only [one_mul] using hh
  exact mul_right_cancel hg

lemma liftedWeights_disjoint_star (x : OrderWeights (LiftedCell M)) :
    ∃ U ∈ 𝓝 x, ∀ g : Artin M, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  obtain ⟨a,ha⟩ := x.support_nonempty
  let U : Set (OrderWeights (LiftedCell M)) := {y | 0 < y.weights a}
  have ho : IsOpen U := isOpen_lt continuous_const (weightEval_continuous a)
  have hx : x ∈ U := lt_of_le_of_ne (x.nonneg a) (Ne.symm (Finsupp.mem_support_iff.mp ha))
  refine ⟨U,ho.mem_nhds hx,?_⟩
  intro g hg
  obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hg
  have ha' : a ∈ (g • z).weights.support := Finsupp.mem_support_iff.mpr (ne_of_gt hy)
  have hga : liftedDeck M g a ∈ (g • z).weights.support := by
    rw [Finsupp.mem_support_iff,liftedWeights_smul_apply]
    exact ne_of_gt hz
  exact liftedDeck_comparable M g a ((g • z).chain a ha' _ hga)

def SalvettiDeckQuotient := Quotient (MulAction.orbitRel (Artin M) (OrderWeights (LiftedCell M)))

instance : TopologicalSpace (SalvettiDeckQuotient M) :=
  inferInstanceAs (TopologicalSpace (Quotient (MulAction.orbitRel (Artin M) (OrderWeights (LiftedCell M)))))

noncomputable def salvettiDeckProjection : OrderWeights (LiftedCell M) → SalvettiDeckQuotient M := Quotient.mk _

theorem salvettiDeckProjection_quotientCovering :
    IsQuotientCoveringMap (salvettiDeckProjection M) (Artin M) where
  __ := isQuotientMap_quotient_mk'
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := Quotient.eq''
  disjoint := liftedWeights_disjoint_star M

theorem salvettiDeckProjection_covering : IsCoveringMap (salvettiDeckProjection M) :=
  (salvettiDeckProjection_quotientCovering M).isCoveringMap

theorem liftedWeights_contractible [Finite S] : ContractibleSpace (OrderWeights (LiftedCell M)) :=
  nerveWeightsHomeomorph.contractibleSpace_iff.mp (salvetti_cover_contractible M)

end HarmonicArtin

end OAI
