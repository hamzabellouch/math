import OAI.SetTheory.PartitionPrinciple.Geometry.GroundMainTransitionLaws
import OAI.SetTheory.PartitionPrinciple.Geometry.RectangleFulfillmentAtBound

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

structure MainTransitionLaws
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : ZFSet.{u}) : Prop where
  point_embedding : MeetEmbeddingCode P Q rP rQ μP μQ points
  order_iff : ∀ x y x' y', ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    (ZFSet.pair x' y' ∈ rQ ↔ ZFSet.pair x y ∈ rP)
  group_embedding : GroupEmbeddingCode G H mG mH oneG oneH actors
  equivariant : ∀ g g' x y x' y', ZFSet.pair g g' ∈ actors →
    ZFSet.pair x x' ∈ points → ZFSet.pair y y' ∈ points →
    ZFSet.pair (ZFSet.pair g x) y ∈ AP → ZFSet.pair (ZFSet.pair g' x') y' ∈ AQ
  bottom : ZFSet.pair bP bQ ∈ points
  height : ∀ x y z, ZFSet.pair x y ∈ points →
    (ZFSet.pair y z ∈ heightQ ↔ ZFSet.pair x z ∈ heightP)
  agreement : ∀ g h g' h' v v', ZFSet.pair g g' ∈ actors → ZFSet.pair h h' ∈ actors →
    ZFSet.pair v v' ∈ points → ActionAgreementBelow P rP AP g h v →
      ActionAgreementBelow Q rQ AQ g' h' v'

namespace BoundedFormula

def transitionOrderFormula {n} (P Q rP rQ points : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  .allMem P (.allMem P.succ (.allMem Q.succ.succ (.allMem Q.succ.succ.succ
    (imp (.conj (pairMembershipFormula 3 1 (lift points)) (pairMembershipFormula 2 0 (lift points)))
      (.conj (imp (pairMembershipFormula 1 0 (lift rQ)) (pairMembershipFormula 3 2 (lift rP)))
        (imp (pairMembershipFormula 3 2 (lift rP)) (pairMembershipFormula 1 0 (lift rQ))))))))

def transitionEquivarianceFormula {n} (P Q G H AP AQ points actors : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem G (.allMem H.succ (.allMem P.succ.succ (.allMem P.succ.succ.succ
    (.allMem Q.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 4 (lift actors))
        (.conj (pairMembershipFormula 3 1 (lift points))
          (.conj (pairMembershipFormula 2 0 (lift points))
            (tripleMembershipFormula 5 3 2 (lift AP)))))
        (tripleMembershipFormula 4 1 0 (lift AQ))))))))

def transitionHeightFormula {n} (P Q heightP heightQ points : Fin n) : BoundedFormula n :=
  .allMem P (.allMem Q.succ (imp (pairMembershipFormula 1 0 points.succ.succ)
    (graphFiberEqualityFormula 0 1 heightQ.succ.succ heightP.succ.succ)))

def transitionAgreementFormula {n} (P Q rP rQ G H AP AQ points actors : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ.succ.succ
  .allMem G (.allMem G.succ (.allMem H.succ.succ (.allMem H.succ.succ.succ
    (.allMem P.succ.succ.succ.succ (.allMem Q.succ.succ.succ.succ.succ
      (imp (.conj (pairMembershipFormula 5 3 (lift actors))
        (.conj (pairMembershipFormula 4 2 (lift actors))
          (.conj (pairMembershipFormula 1 0 (lift points))
            (actionAgreementBelowFormula (lift P) (lift rP) (lift AP) 5 4 1))))
        (actionAgreementBelowFormula (lift Q) (lift rQ) (lift AQ) 3 2 0)))))))

def mainTransitionLawsFormula {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n) :
    BoundedFormula n :=
  .conj (meetEmbeddingFormula P Q rP rQ μP μQ points)
    (.conj (transitionOrderFormula P Q rP rQ points)
      (.conj (groupEmbeddingFormula G H mG mH oneG oneH actors)
        (.conj (transitionEquivarianceFormula P Q G H AP AQ points actors)
          (.conj (pairMembershipFormula bP bQ points)
            (.conj (transitionHeightFormula P Q heightP heightQ points)
              (transitionAgreementFormula P Q rP rQ G H AP AQ points actors))))))

theorem truth_mainTransitionLawsFormula {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors) env ↔
    MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
      (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
      (env heightP) (env heightQ) (env points) (env actors) := by
  simp only [mainTransitionLawsFormula, transitionOrderFormula, transitionEquivarianceFormula,
    transitionHeightFormula, transitionAgreementFormula, Truth, truth_meetEmbeddingFormula,
    truth_groupEmbeddingFormula, truth_imp, truth_pairMembershipFormula,
    truth_tripleMembershipFormula, truth_graphFiberEqualityFormula, truth_actionAgreementBelowFormula]
  constructor
  · rintro ⟨point, order, group, equivariant, bottom, height, agreement⟩
    have pb {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env points) : x ∈ env P ∧ y ∈ env Q :=
      ZFSet.pair_mem_prod.1 (point.injection.function.1 entry)
    have ab {x y : ZFSet.{u}} (entry : ZFSet.pair x y ∈ env actors) : x ∈ env G ∧ y ∈ env H :=
      ZFSet.pair_mem_prod.1 (group.injection.function.1 entry)
    refine ⟨point, ?_, group, ?_, bottom, ?_, ?_⟩
    · intro x y x' y' xx yy
      have h := order x (pb xx).1 y (pb yy).1 x' (pb xx).2 y' (pb yy).2 ⟨xx, yy⟩
      exact ⟨h.1, h.2⟩
    · intro g g' x y x' y' gg xx yy act
      exact equivariant g (ab gg).1 g' (ab gg).2 x (pb xx).1 y (pb yy).1
        x' (pb xx).2 y' (pb yy).2 ⟨gg, xx, yy, act⟩
    · intro x y z entry
      exact height x (pb entry).1 y (pb entry).2 entry z
    · intro g h g' h' v v' gg hh vv agree
      exact agreement g (ab gg).1 h (ab hh).1 g' (ab gg).2 h' (ab hh).2
        v (pb vv).1 v' (pb vv).2 ⟨gg, hh, vv, agree⟩
  · intro code
    refine ⟨code.point_embedding, ?_, code.group_embedding, ?_, code.bottom, ?_, ?_⟩
    · intro x _ y _ x' _ y' _ h
      exact ⟨(code.order_iff x y x' y' h.1 h.2).1, (code.order_iff x y x' y' h.1 h.2).2⟩
    · intro g _ g' _ x _ y _ x' _ y' _ h
      exact code.equivariant g g' x y x' y' h.1 h.2.1 h.2.2.1 h.2.2.2
    · intro x _ y _ entry z
      exact code.height x y z entry
    · intro g _ h _ g' _ h' _ v _ v' _ entries
      exact code.agreement g h g' h' v v' entries.1 entries.2.1 entries.2.2.1 entries.2.2.2

theorem realize_mainTransitionLawsFormula (M : TransitiveGround.{u}) {n}
    (P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ heightP heightQ points actors : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors).toFormula env ↔
    MainTransitionLaws (env P) (env Q) (env rP) (env rQ) (env μP) (env μQ) (env G) (env H)
      (env mG) (env mH) (env oneG) (env oneH) (env AP) (env AQ) (env bP) (env bQ)
      (env heightP) (env heightQ) (env points) (env actors) :=
  (realize_toFormula M _ env members).trans
    (truth_mainTransitionLawsFormula P Q rP rQ μP μQ G H mG mH oneG oneH AP AQ bP bQ
      heightP heightQ points actors env)

end BoundedFormula

end PartitionPilot.Forcing

end

end OAI
