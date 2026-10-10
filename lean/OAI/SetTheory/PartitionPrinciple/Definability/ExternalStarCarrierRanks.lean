import OAI.SetTheory.PartitionPrinciple.Definability.GroundBoundedExternalBirths
import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalRequestRankBounds

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalGroupCarrier_rank_lt {G S : ZFSet.{u}} (m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o)
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (M.externalGroupCarrier G S m one) < o :=
  rank_equivalenceClasses_lt limit (M.externalWordEquivalence G S m one)
    (M.finiteWords_rank_lt limit omega (externalGeneratorAlphabet_rank_lt limit actors letters))

theorem externalRequestWords_rank_lt {I P G : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.finiteWords (externalRequestAlphabet I P G r μ A)) < o :=
  M.finiteWords_rank_lt limit omega (externalRequestAlphabet_rank_lt limit r μ A indices points actors)

theorem externalRequestGroup_rank_lt {I P G : ZFSet.{u}} (r μ A m one : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o :=
  M.externalGroupCarrier_rank_lt limit m one omega actors
    (externalChildLetters_rank_lt limit indices points (externalRectangles_rank_lt limit r μ A points actors))

end TransitiveGround

namespace GroundCompressionCompletion
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ : ZFSet.{u}}
variable (completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ)
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalPointCarrier_rank_lt {P r μ A : ZFSet.{u}}
    (actors : ZFSet.rank (M.externalGroupCarrier G
      (externalChildLetters I P (externalRectangles P G r μ A)) m one) < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  rank_equivalenceClasses_lt limit (completion.externalFlatEquivalence P r μ A)
    (rank_product_lt limit actors completed)

theorem externalPointCarrier_rank_lt_of_inputs {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalPointCarrier P r μ A) < o :=
  completion.externalPointCarrier_rank_lt limit
    (M.externalRequestGroup_rank_lt limit r μ A m one omega indices points actors) completed

theorem externalBoundedCarrier_rank_lt {P : ZFSet.{u}} (r μ A : ZFSet.{u})
    (omega : ZFSet.rank ZFSet.omega < o) (indices : ZFSet.rank I < o)
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o)
    (completed : ZFSet.rank (completion.algebra.union.fields 0) < o) :
    ZFSet.rank (completion.externalBoundedCarrier P r μ A) < o :=
  rank_fixedTopCarrier_lt limit
    (completion.externalPointCarrier_rank_lt_of_inputs limit r μ A omega indices points actors completed)

end GroundCompressionCompletion
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem taggedSumCarrier_rank_lt {A B : ZFSet.{u}}
    (left : ZFSet.rank A < o) (right : ZFSet.rank B < o) :
    ZFSet.rank (taggedSumCarrier A B) < o := by
  rw [taggedSumCarrier, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 0)) left)
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 1)) right)

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalStarVertices_rank_lt {G S R : ZFSet.{u}} (m one : ZFSet.{u})
    (actors : ZFSet.rank (M.externalGroupCarrier G S m one) < o)
    (requests : ZFSet.rank R < o) :
    ZFSet.rank (M.externalStarVertices G S R m one) < o :=
  taggedSumCarrier_rank_lt limit
    (rank_equivalenceClasses_lt limit (M.externalCosetEquivalence G S m one) actors)
    (rank_product_lt limit actors requests)

theorem externalStarVertices_rank_lt_of_inputs {I P G : ZFSet.{u}}
    (r μ A m one : ZFSet.{u}) (omega : ZFSet.rank ZFSet.omega < o)
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (actors : ZFSet.rank G < o) :
    ZFSet.rank (M.externalStarVertices G
      (externalChildLetters I P (externalRectangles P G r μ A))
      (externalRequestCarrier I P (externalRectangles P G r μ A)) m one) < o :=
  M.externalStarVertices_rank_lt limit m one
    (M.externalRequestGroup_rank_lt limit r μ A m one omega indices points actors)
    (externalRequestCarrier_rank_lt limit indices points
      (externalRectangles_rank_lt limit r μ A points actors))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
