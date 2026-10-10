import OAI.SetTheory.PartitionPrinciple.Definability.GroundMainTransitionCodes

namespace OAI

namespace PartitionPilot.Forcing.GroundMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

noncomputable def identity (stage : GroundMainStage M C D rD) : GroundMainTransition stage stage where
  points := identityFunctionGraph stage.carrier
  actors := identityFunctionGraph stage.actors
  points_ground := M.identityFunctionGraph_mem pairing unions powers separation stage.carrier_ground
  actors_ground := M.identityFunctionGraph_mem pairing unions powers separation stage.actors_ground
  point_embedding := by
    refine ⟨identityFunctionGraph_injection _, ?_, ?_⟩
    · intro x y x' y' lower first second
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
      exact lower
    · intro x y z x' y' z' meet first second third
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
      obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 third
      exact meet
  order_iff := by
    intro x y x' y' first second
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    exact Iff.rfl
  group_embedding := GroupEmbeddingCode.identity stage.group_code
  equivariant := by
    intro g g' x y x' y' actor first second acted
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 actor
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    exact acted
  bottom := (pair_mem_identityFunctionGraph _ _ _).2 ⟨rfl, stage.bottom_mem⟩
  height := by
    intro x y z entry
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 entry
    exact Iff.rfl
  agreement := by
    intro g h g' h' v v' first second image agree
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 first
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 second
    obtain ⟨rfl, _⟩ := (pair_mem_identityFunctionGraph _ _ _).1 image
    exact agree

noncomputable def comp {source middle target : GroundMainStage M C D rD}
    (first : GroundMainTransition source middle) (second : GroundMainTransition middle target) :
    GroundMainTransition source target where
  points := relationCompose source.carrier middle.carrier target.carrier first.points second.points
  actors := relationCompose source.actors middle.actors target.actors first.actors second.actors
  points_ground := M.relationCompose_mem pairing unions powers separation source.carrier_ground
    middle.carrier_ground target.carrier_ground first.points_ground second.points_ground
  actors_ground := M.relationCompose_mem pairing unions powers separation source.actors_ground
    middle.actors_ground target.actors_ground first.actors_ground second.actors_ground
  point_embedding := first.point_embedding.compose second.point_embedding
  order_iff := by
    intro x y x' y' xx yy
    obtain ⟨_, _, a, _, xa, ax⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, b, _, yb, by'⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact (second.order_iff a b x' y' ax by').trans (first.order_iff x y a b xa yb)
  group_embedding := first.group_embedding.compose second.group_embedding
  equivariant := by
    intro g g' x y x' y' actor xx yy acted
    obtain ⟨_, _, a, _, ga, ag⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 actor
    obtain ⟨_, _, b, _, xb, bx⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 xx
    obtain ⟨_, _, c, _, yc, cy⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 yy
    exact second.equivariant a g' b c x' y' ag bx cy (first.equivariant g a x y b c ga xb yc acted)
  bottom := (pair_mem_relationCompose _ _ _ _ _ _ _).2
    ⟨source.bottom_mem, target.bottom_mem, middle.bottom, middle.bottom_mem, first.bottom, second.bottom⟩
  height := by
    intro x y z entry
    obtain ⟨_, _, a, _, xa, ay⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 entry
    exact (second.height a y z ay).trans (first.height x a z xa)
  agreement := by
    intro g h g' h' v v' gg hh vv agree
    obtain ⟨_, _, a, _, ga, ag⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 gg
    obtain ⟨_, _, b, _, hb, bh⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 hh
    obtain ⟨_, _, w, _, vw, wv⟩ := (pair_mem_relationCompose _ _ _ _ _ _ _).1 vv
    exact second.agreement a b g' h' w v' ag bh wv (first.agreement g h a b v w ga hb vw agree)

@[ext] theorem ext {source target : GroundMainStage M C D rD}
    {first second : GroundMainTransition source target}
    (points : first.points = second.points) (actors : first.actors = second.actors) : first = second := by
  cases first
  cases second
  cases points
  cases actors
  rfl

end PartitionPilot.Forcing.GroundMainTransition

namespace PartitionPilot.Forcing
universe u
namespace GroundMainTransition
open SetFormula
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable {source target : GroundMainStage M C D rD}

noncomputable def code (transition : GroundMainTransition source target) : ZFSet.{u} :=
  ZFSet.pair transition.points transition.actors

theorem code_injective : Function.Injective (code (source := source) (target := target)) := by
  intro first second equal
  obtain ⟨points, actors⟩ := ZFSet.pair_inj.1 equal
  exact ext points actors

theorem code_mem (transition : GroundMainTransition source target)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) : transition.code ∈ M.sets :=
  M.orderedPair_mem pairing transition.points_ground transition.actors_ground

end GroundMainTransition

namespace BoundedFormula
open SetFormula

def mainTransitionFormula {n} (z points actors : Fin n) : BoundedFormula n :=
  orderedPairFormula z points actors

theorem truth_mainTransitionFormula {n} (z points actors : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (mainTransitionFormula z points actors) env ↔
      env z = ZFSet.pair (env points) (env actors) :=
  truth_orderedPairFormula z points actors env

theorem realize_mainTransitionFormula (M : TransitiveGround.{u}) {n}
    (z points actors : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (mainTransitionFormula z points actors).toFormula env ↔
      env z = ZFSet.pair (env points) (env actors) :=
  (realize_toFormula M _ env members).trans (truth_mainTransitionFormula z points actors env)

end BoundedFormula
end PartitionPilot.Forcing

namespace PartitionPilot.Forcing.GroundMainTransition
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

@[simp] theorem identity_comp {source target : GroundMainStage M C D rD}
    (f : GroundMainTransition source target) :
    comp pairing unions powers separation (identity pairing unions powers separation source) f = f := by
  apply ext
  · exact relationCompose_identity_left f.point_embedding.injection.function.1
  · exact relationCompose_identity_left f.group_embedding.injection.function.1

@[simp] theorem comp_identity {source target : GroundMainStage M C D rD}
    (f : GroundMainTransition source target) :
    comp pairing unions powers separation f (identity pairing unions powers separation target) = f := by
  apply ext
  · exact relationCompose_identity_right f.point_embedding.injection.function.1
  · exact relationCompose_identity_right f.group_embedding.injection.function.1

theorem comp_assoc {source first second target : GroundMainStage M C D rD}
    (f : GroundMainTransition source first) (g : GroundMainTransition first second)
    (h : GroundMainTransition second target) :
    comp pairing unions powers separation (comp pairing unions powers separation f g) h =
      comp pairing unions powers separation f (comp pairing unions powers separation g h) := by
  apply ext
  · exact relationCompose_assoc source.carrier first.carrier second.carrier target.carrier f.points g.points h.points
  · exact relationCompose_assoc source.actors first.actors second.actors target.actors f.actors g.actors h.actors

end PartitionPilot.Forcing.GroundMainTransition

end OAI
