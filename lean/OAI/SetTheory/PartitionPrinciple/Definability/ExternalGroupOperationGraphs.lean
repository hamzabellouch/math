import OAI.SetTheory.PartitionPrinciple.Forcing.ExternalWordInverseEvaluation
import OAI.SetTheory.PartitionPrinciple.Models.GroundQuotientBinaryOperations
import OAI.SetTheory.PartitionPrinciple.Models.GroundQuotientUnaryOperations

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

noncomputable def externalGroupPresentation : Presentation (External J L) :=
  (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).reindex
    (ExternalWordRewrite.quotientEquiv J L).symm.toEquiv

theorem externalGroupPresentation_carrier :
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).carrier =
      equivalenceClasses (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
        (M.externalWordEquivalence s.carrier t.carrier
          ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) := rfl

theorem externalGroupPresentation_encode_evalWord (xs : List (J ⊕ (L × Bool))) :
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode
      (ExternalWordRewrite.evalWord J L xs) =
        equivalenceClass (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
          (M.externalWordEquivalence s.carrier t.carrier
            ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1))
          (finiteWordGraph (externalGeneratorAlphabetPresentation s t) xs) := by
  change (M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS).encode
    (ExternalWordRewrite.fromExternal J L (ExternalWordRewrite.evalWord J L xs)) = _
  rw [ExternalWordRewrite.fromExternal_evalWord]
  exact M.externalWordQuotientPresentation_encode_mk pairing unions powers separation infinite s t hG hS xs

theorem externalGroupClassifier_eq_graph :
    equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet s.carrier t.carrier))
      (M.externalWordEquivalence s.carrier t.carrier
        ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1)) =
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite
        (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.evalWord J L) := by
  let words := finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M
    pairing unions separation infinite
    (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)
  let quotient := M.externalWordQuotientPresentation pairing unions powers separation infinite s t hG hS
  refine (M.externalWordClassifier_eq_graph pairing unions powers separation infinite s t hG hS).trans ?_
  refine Eq.trans ?_ (quotient.graph_reindex
    (ExternalWordRewrite.quotientEquiv J L).symm.toEquiv words (ExternalWordRewrite.evalWord J L)).symm
  exact congrArg (words.graph quotient)
    (funext fun xs => (ExternalWordRewrite.fromExternal_evalWord J L xs).symm)

theorem externalGroupPresentation_ground
    (hm : (s.product s).graph s (fun p => p.1 * p.2) ∈ M.sets) :
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).carrier ∈ M.sets ∧
      (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite
        (M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS)).graph
        (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
        (ExternalWordRewrite.evalWord J L) ∈ M.sets := by
  have ground := M.externalWordQuotient_ground pairing unions powers separation infinite s t hG hS hm
  exact ⟨ground.1, (M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS) ▸ ground.2⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetRealization SetFormula
open Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

noncomputable def externalGroupCarrier (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClasses (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one)

noncomputable def externalGroupProjection (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClassifier (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one)

noncomputable def externalGroupMultiplication (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  quotientBinaryGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalGroupCarrier G S m one) (M.externalGroupProjection G S m one)
    (M.finiteWordAppendGraph (externalGeneratorAlphabet G S))

noncomputable def externalGroupInverse (G S m inv one : ZFSet.{u}) : ZFSet.{u} :=
  quotientUnaryGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalGroupCarrier G S m one) (M.externalGroupProjection G S m one)
    (M.externalInverseWordGraph G S inv)

noncomputable def externalGroupIdentity (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  equivalenceClass (M.finiteWords (externalGeneratorAlphabet G S))
    (M.externalWordEquivalence G S m one) ∅

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)

include pairing unions powers separation infinite in
theorem externalGroupOperations_ground {G S m inv one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets)
    (hInv : inv ∈ M.sets) (hOne : one ∈ M.sets) :
    M.externalGroupCarrier G S m one ∈ M.sets ∧
      M.externalGroupMultiplication G S m one ∈ M.sets ∧
      M.externalGroupInverse G S m inv one ∈ M.sets ∧
      M.externalGroupIdentity G S m one ∈ M.sets ∧
      M.externalGroupProjection G S m one ∈ M.sets := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hE := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  have hQ := M.equivalenceClasses_mem powers separation hWords hE
  have hProjection := M.equivalenceClassifier_mem pairing unions powers separation hWords hE
  exact ⟨hQ,
    M.quotientBinaryGraph_mem pairing unions powers separation hWords hQ hProjection
      (M.finiteWordAppendGraph_mem pairing unions powers separation infinite hAlphabet),
    M.quotientUnaryGraph_mem pairing unions powers separation hWords hQ hProjection
      (M.externalInverseWordGraph_mem pairing unions powers separation infinite hG hS hInv),
    M.equivalenceClass_mem separation hWords hE (M.empty_mem ⟨G, hG⟩), hProjection⟩

variable {J L : Type u} [Group J] (s : Presentation J) (t : Presentation L)
variable (hG : s.carrier ∈ M.sets) (hS : t.carrier ∈ M.sets)

theorem externalGroupMultiplication_eq_graph :
    let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
    M.externalGroupMultiplication s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) =
      (q.product q).graph q (fun p => p.1 * p.2) := by
  dsimp only
  unfold externalGroupMultiplication externalGroupProjection
  rw [M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have append := M.finiteWordAppendGraph_eq_graph pairing unions separation infinite
    (externalGeneratorAlphabetPresentation s t) hAlphabet
  change M.finiteWordAppendGraph (externalGeneratorAlphabet s.carrier t.carrier) = _ at append
  rw [append]
  exact quotientBinaryGraph_eq_graph
    (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite hAlphabet)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (ExternalWordRewrite.evalWord J L) List.append
    (fun x y => x * y) (ExternalWordRewrite.evalWord_surjective J L)
    (fun x y => (ExternalWordRewrite.evalWord J L).map_mul x y)

theorem externalGroupInverse_eq_graph :
    let q := M.externalGroupPresentation pairing unions powers separation infinite s t hG hS
    M.externalGroupInverse s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.graph s Inv.inv) (s.encode 1) =
      q.graph q Inv.inv := by
  dsimp only
  unfold externalGroupInverse externalGroupProjection
  rw [M.externalGroupClassifier_eq_graph pairing unions powers separation infinite s t hG hS]
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  rw [M.externalInverseWordGraph_eq_graph pairing unions separation infinite s t hAlphabet]
  exact quotientUnaryGraph_eq_graph
    (finiteWordPresentation (externalGeneratorAlphabetPresentation s t) M pairing unions separation infinite hAlphabet)
    (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS)
    (ExternalWordRewrite.evalWord J L) externalWordInverse Inv.inv
    (ExternalWordRewrite.evalWord_surjective J L) (ExternalWordRewrite.evalWord_inverse J L)

theorem externalGroupIdentity_eq_encode :
    M.externalGroupIdentity s.carrier t.carrier
      ((s.product s).graph s (fun p => p.1 * p.2)) (s.encode 1) =
      (M.externalGroupPresentation pairing unions powers separation infinite s t hG hS).encode 1 := by
  have unit : ExternalWordRewrite.evalWord J L [] = 1 := (ExternalWordRewrite.evalWord J L).map_one
  have encoded := M.externalGroupPresentation_encode_evalWord pairing unions powers separation infinite
    s t hG hS []
  rw [unit, finiteWordGraph_nil] at encoded
  exact encoded.symm

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
