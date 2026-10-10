import OAI.SetTheory.PartitionPrinciple.Geometry.GroundInitialExternalGroup

namespace OAI

section

namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {o : Ordinal.{u}} (limit : Order.IsSuccLimit o)
include limit

theorem externalRectangleBound_rank_lt {P G : ZFSet.{u}}
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangleBound P G) < o :=
  rank_product_lt limit points (rank_product_lt limit points
    (rank_product_lt limit points (rank_product_lt limit actors actors)))

theorem externalRectangles_rank_lt {P G : ZFSet.{u}} (r μ A : ZFSet.{u})
    (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRectangles P G r μ A) < o :=
  (ZFSet.rank_mono (show externalRectangles P G r μ A ⊆ externalRectangleBound P G from
    fun _ hx => (ZFSet.mem_sep.1 hx).1)).trans_lt
      (externalRectangleBound_rank_lt limit points actors)

theorem externalRequestCarrier_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalRequestCarrier I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalRequestCarrier, ZFSet.rank_union, ZFSet.rank_union]
  exact max_lt (max_lt (rank_product_lt limit (tag 0) indices)
    (rank_product_lt limit (tag 1) points)) (rank_product_lt limit (tag 2) rectangles)

theorem externalChildLetters_rank_lt {I P Rectangles : ZFSet.{u}}
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o)
    (rectangles : ZFSet.rank Rectangles < o) :
    ZFSet.rank (externalChildLetters I P Rectangles) < o := by
  have tag := fun n => rank_singleton_lt limit (rank_natSetCode_lt limit n)
  rw [externalChildLetters, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (externalRequestCarrier_rank_lt limit indices points rectangles) (tag 0))
    (rank_product_lt limit (rank_product_lt limit (tag 2) rectangles) (tag 1))

theorem externalGeneratorAlphabet_rank_lt {G S : ZFSet.{u}}
    (actors : ZFSet.rank G < o) (letters : ZFSet.rank S < o) :
    ZFSet.rank (externalGeneratorAlphabet G S) < o := by
  rw [externalGeneratorAlphabet, ZFSet.rank_union]
  exact max_lt
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 0)) actors)
    (rank_product_lt limit (rank_singleton_lt limit (rank_natSetCode_lt limit 1))
      (rank_product_lt limit letters (rank_natSetCode_lt limit 2)))

theorem externalRequestAlphabet_rank_lt {I P G : ZFSet.{u}} (r μ A : ZFSet.{u})
    (indices : ZFSet.rank I < o) (points : ZFSet.rank P < o) (actors : ZFSet.rank G < o) :
    ZFSet.rank (externalRequestAlphabet I P G r μ A) < o :=
  externalGeneratorAlphabet_rank_lt limit actors
    (externalChildLetters_rank_lt limit indices points (externalRectangles_rank_lt limit r μ A points actors))

end PartitionPilot.Forcing

end

end OAI
