import OAI.SetTheory.PartitionPrinciple.Definability.GroundBoundedExternalBirths
import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundHistoryUnionBounds

namespace OAI

namespace PartitionPilot.Forcing

namespace GroundBelow
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {A K : ZFSet.{u}}

theorem finiteWords
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hA : A ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (omegaBelow : ZFSet.omega ∈ K) (alphabet : GroundBelow M A K) :
    GroundBelow M (M.finiteWords A) K := by
  have natural := GroundBelow.of_member pairing unions powers separation hK omegaBelow
  have relations := GroundBelow.relations pairing unions powers separation
    (M.omega_mem separation infinite) hA hK ordinal strong natural alphabet
  exact relations.restrict separation (M.finiteWords_mem pairing unions powers separation infinite hA)
    hK (fun _ member => (ZFSet.mem_sep.1 member).1)

end GroundBelow

section
open SetFormula
universe u
namespace GroundBelow
variable {M : TransitiveGround.{u}} {A E K : ZFSet.{u}}

theorem equivalenceClasses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hA : A ∈ M.sets) (hE : E ∈ M.sets) (hK : K ∈ M.sets)
    (strong : GroundStrongLimit M K) (small : GroundBelow M A K) :
    GroundBelow M (Forcing.equivalenceClasses A E) K := by
  have included : Forcing.equivalenceClasses A E ⊆ M.groundPower A := by
    intro X hX
    rw [M.equivalenceClasses_eq_sep_groundPower separation hA hE] at hX
    exact (ZFSet.mem_sep.1 hX).1
  exact (strong.power_closed pairing unions powers separation hA hK small).restrict
    separation (M.equivalenceClasses_mem powers separation hA hE) hK included

end GroundBelow

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalGroupCarrier_below
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S m one K : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) (hK : K ∈ M.sets)
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (omegaBelow : ZFSet.omega ∈ K) (alphabet : GroundBelow M (externalGeneratorAlphabet G S) K) :
    GroundBelow M (M.externalGroupCarrier G S m one) K := by
  have hAlphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  have hWords := M.finiteWords_mem pairing unions powers separation infinite hAlphabet
  have hRelation := M.externalWordEquivalence_mem pairing unions powers separation infinite hG hS hm hOne
  exact GroundBelow.equivalenceClasses pairing unions powers separation hWords hRelation hK strong
    (GroundBelow.finiteWords pairing unions powers separation infinite hAlphabet hK ordinal strong omegaBelow alphabet)

end TransitiveGround
end

namespace TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (choice : Realize M.sets SetFormula.choice Fin.elim0)
variable {K : ZFSet.{u}} (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
include pairing unions powers separation hK conditions

theorem externalRectangleBound_below {P G : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets)
    (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) :
    GroundBelow M (externalRectangleBound P G) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  exact (product ⟨hP, smallP⟩ (product ⟨hP, smallP⟩
    (product ⟨hP, smallP⟩ (product ⟨hG, smallG⟩ ⟨hG, smallG⟩)))).2

theorem externalRectangles_below {P G r μ A : ZFSet.{u}}
    (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hr : r ∈ M.sets)
    (hμ : μ ∈ M.sets) (hA : A ∈ M.sets)
    (smallP : GroundBelow M P K) (smallG : GroundBelow M G K) :
    GroundBelow M (externalRectangles P G r μ A) K := by
  exact (M.externalRectangleBound_below pairing unions powers separation hK conditions hP hG smallP smallG).restrict
    separation (M.externalRectangles_mem pairing unions powers separation hP hG hr hμ hA) hK
    (fun _ hz => (ZFSet.mem_sep.1 hz).1)

include infinite choice

theorem externalRequestCarrier_below {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets)
    (smallI : GroundBelow M I K) (smallP : GroundBelow M P K)
    (smallRectangles : GroundBelow M Rectangles K) :
    GroundBelow M (externalRequestCarrier I P Rectangles) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  exact (join (join (product (tag 0) ⟨hI, smallI⟩) (product (tag 1) ⟨hP, smallP⟩))
    (product (tag 2) ⟨hRectangles, smallRectangles⟩)).2

theorem externalChildLetters_below {I P Rectangles : ZFSet.{u}}
    (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hRectangles : Rectangles ∈ M.sets)
    (smallI : GroundBelow M I K) (smallP : GroundBelow M P K)
    (smallRectangles : GroundBelow M Rectangles K) :
    GroundBelow M (externalChildLetters I P Rectangles) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  have requests := M.externalRequestCarrier_below pairing unions powers separation infinite choice hK conditions
    hI hP hRectangles smallI smallP smallRectangles
  exact (join (product ⟨M.externalRequestCarrier_mem pairing unions powers separation hI hP hRectangles,
      requests⟩ (tag 0)) (product (product (tag 2) ⟨hRectangles, smallRectangles⟩) (tag 1))).2

theorem externalGeneratorAlphabet_below {G S : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets)
    (smallG : GroundBelow M G K) (smallS : GroundBelow M S K) :
    GroundBelow M (externalGeneratorAlphabet G S) K := by
  have product := @GroundInaccessibleConditions.product M K conditions pairing unions powers separation hK
  have join := @GroundInaccessibleConditions.binary_union M K conditions pairing unions powers separation infinite choice hK
  have tag := fun n => conditions.singleton pairing unions powers separation infinite hK
    (M.natSetCode_mem separation infinite n)
  exact (join (product (tag 0) ⟨hG, smallG⟩)
    (product (tag 1) (product ⟨hS, smallS⟩ (conditions.natural pairing unions powers separation infinite hK 2)))).2

theorem externalGroupCarrier_below_of_carriers {G S m one : ZFSet.{u}}
    (hG : G ∈ M.sets) (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets)
    (smallG : GroundBelow M G K) (smallS : GroundBelow M S K) :
    GroundBelow M (M.externalGroupCarrier G S m one) K :=
  M.externalGroupCarrier_below pairing unions powers separation infinite hG hS hm hOne hK
    conditions.1 conditions.2.2.2 conditions.2.1
    (M.externalGeneratorAlphabet_below pairing unions powers separation infinite choice hK conditions hG hS smallG smallS)

end TransitiveGround

namespace GroundExternalGeometryInputs
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m inv one T τ P r μ A K : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P r μ A completion)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0)
variable (hP : P ∈ M.sets) (hG : G ∈ M.sets) (hK : K ∈ M.sets)
local notation "letters" => externalChildLetters I P (externalRectangles P G r μ A)
local notation "actors" => M.externalGroupCarrier G letters m one
local notation "U" => completion.algebra.union.fields 0
include data pairing unions powers separation infinite hP hG hK

theorem externalPointCarrier_below
    (ordinal : ordinalSetProperty K) (strong : GroundStrongLimit M K)
    (groupSmall : GroundBelow M actors K) (pointsSmall : GroundBelow M U K) :
    GroundBelow M (completion.externalPointCarrier P r μ A) K := by
  have quotient := data.point_quotient_ground pairing unions powers separation infinite hP hG
  have hProduct := M.prod_mem pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0)
  have smallProduct := GroundBelow.product pairing unions powers separation
    data.group.carrier_mem (completion.algebra.union.ground 0) hK ordinal strong groupSmall pointsSmall
  exact GroundBelow.equivalenceClasses pairing unions powers separation
    hProduct quotient.1 hK strong smallProduct

theorem externalBoundedCarrier_below
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    (conditions : GroundInaccessibleConditions M K)
    (groupSmall : GroundBelow M actors K) (pointsSmall : GroundBelow M U K) :
    GroundBelow M (completion.externalBoundedCarrier P r μ A) K := by
  have hQ := (data.point_quotient_ground pairing unions powers separation infinite hP hG).2.2.1
  exact GroundBelow.insert pairing unions powers separation infinite choice hQ hQ hK conditions.2.1
    conditions.1 conditions.2.2.1 conditions.2.2.2
    (data.externalPointCarrier_below pairing unions powers separation infinite hP hG hK
      conditions.1 conditions.2.2.2 groupSmall pointsSmall)

end GroundExternalGeometryInputs

end PartitionPilot.Forcing

end OAI
