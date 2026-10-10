import OAI.SetTheory.PartitionPrinciple.Definability.BoundedDirectedOrders
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundPrincipalSupportZF
import OAI.SetTheory.PartitionPrinciple.Forcing.MeetOrderPosetActions
import OAI.SetTheory.PartitionPrinciple.Forcing.SmallCodedMeetActions

namespace OAI

namespace PartitionPilot.Forcing

namespace TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps.CosetGeometry
universe u
variable (M : TransitiveGround.{u})

theorem geometry_supportBasis_mem {I G : Type u} [Group G]
    (s : GeometryPresentation I G) (P : MeetOrder I) (a : OrderAction G P)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : s.points.carrier ∈ M.sets) (group : s.actors.carrier ∈ M.sets)
    (order : s.orderRelation P ∈ M.sets) (graph : s.actionGraph P a ∈ M.sets) :
    supportBasisCode s.points s.actors a.fixSubgroup ∈ M.sets := by
  let := P.toPartialOrder
  exact M.principalSupportBasis_mem a.toPosetAction s.points s.actors pairing unions powers separation
    nodes group order graph

theorem decoded_supportBasis_mem {G L m i e R A : ZFSet.{u}}
    (group : GroupCode G m i e) (order : PartialOrderCode L R)
    (action : PosetActionCode G L m e R A)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (hL : L ∈ M.sets) (hG : G ∈ M.sets) (hR : R ∈ M.sets) (hA : A ∈ M.sets) :
    letI := group.toGroup
    letI := order.toPartialOrder
    supportBasisCode (SetMembers.presentation L) (SetMembers.presentation G)
      (action.toPosetAction group order).principalFix ∈ M.sets := by
  let := group.toGroup
  let := order.toPartialOrder
  have order_mem : (SetMembers.presentation L).conditionOrder ∈ M.sets := by
    rw [order.conditionOrder_eq]
    exact hR
  have action_mem : (action.toPosetAction group order).actionGraph
      (SetMembers.presentation L) (SetMembers.presentation G) ∈ M.sets := by
    rw [action.actionGraph_eq group order]
    exact hA
  exact M.principalSupportBasis_mem (action.toPosetAction group order)
    (SetMembers.presentation L) (SetMembers.presentation G) pairing unions powers separation hL hG order_mem action_mem

noncomputable def decoded_supportFamily {G L m i e R A : ZFSet.{u}}
    (group : GroupCode G m i e) (order : PartialOrderCode L R)
    (action : PosetActionCode G L m e R A)
    (hL : L ∈ M.sets) (hR : R ∈ M.sets)
    (directed : Realize M.sets (BoundedFormula.upwardDirectedFormula 0 1).toFormula
      (extend L (extend R Fin.elim0))) (C : SetMembers L) :
    letI := group.toGroup
    Compression.RecursiveMaps.NormalSubgroupFamily (SetMembers G) := by
  letI := group.toGroup
  letI := order.toPartialOrder
  exact (action.toPosetAction group order).principalSupportFamily C
    (M.decoded_upward_directed order hL hR directed)

end TransitiveGround

section
open SetFormula
universe u

structure GroundMainFinalGeometry (M : TransitiveGround.{u}) (C D rD : ZFSet.{u}) where
  carrier : ZFSet.{u}
  order : ZFSet.{u}
  meetGraph : ZFSet.{u}
  actors : ZFSet.{u}
  multiplication : ZFSet.{u}
  inverse : ZFSet.{u}
  identity : ZFSet.{u}
  action : ZFSet.{u}
  bottom : ZFSet.{u}
  height : ZFSet.{u}
  birth : ZFSet.{u}
  times : ZFSet.{u}
  carrier_ground : carrier ∈ M.sets
  order_ground : order ∈ M.sets
  meet_ground : meetGraph ∈ M.sets
  actors_ground : actors ∈ M.sets
  multiplication_ground : multiplication ∈ M.sets
  inverse_ground : inverse ∈ M.sets
  action_ground : action ∈ M.sets
  height_ground : height ∈ M.sets
  birth_ground : birth ∈ M.sets
  times_ground : times ∈ M.sets
  columns_ground : C ∈ M.sets
  coordinates_ground : D ∈ M.sets
  coordinate_order_ground : rD ∈ M.sets
  meet : MeetOrderCode carrier order meetGraph
  group_code : GroupCode actors multiplication inverse identity
  action_code : PosetActionCode actors carrier multiplication identity order action
  bottom_mem : bottom ∈ carrier
  least : ∀ x ∈ carrier, ZFSet.pair bottom x ∈ order
  height_code : StrictLexHeightCode carrier C D order height rD
  birth_function : ZFSet.IsFunc carrier times birth
  times_ordinal : ordinalSetProperty times
  old_meet : OldMeetCode order meetGraph birth

namespace GroundMainFinalGeometry
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem identity_ground : geometry.identity ∈ M.sets :=
  M.transitive geometry.actors_ground geometry.group_code.identity_mem

theorem bottom_ground : geometry.bottom ∈ M.sets :=
  M.transitive geometry.carrier_ground geometry.bottom_mem

noncomputable def fields : Fin 12 → ZFSet.{u} :=
  Fin.cases geometry.carrier (Fin.cases geometry.order (Fin.cases geometry.meetGraph
    (Fin.cases geometry.actors (Fin.cases geometry.multiplication (Fin.cases geometry.inverse
      (Fin.cases geometry.identity (Fin.cases geometry.action (Fin.cases geometry.bottom
        (Fin.cases geometry.height (Fin.cases geometry.birth (fun _ => geometry.times)))))))))))

theorem fields_ground : ∀ j, geometry.fields j ∈ M.sets :=
  Fin.cases geometry.carrier_ground (Fin.cases geometry.order_ground (Fin.cases geometry.meet_ground
    (Fin.cases geometry.actors_ground (Fin.cases geometry.multiplication_ground (Fin.cases geometry.inverse_ground
      (Fin.cases geometry.identity_ground (Fin.cases geometry.action_ground (Fin.cases geometry.bottom_ground
        (Fin.cases geometry.height_ground (Fin.cases geometry.birth_ground (fun _ => geometry.times_ground)))))))))))

noncomputable def code : ZFSet.{u} := nonemptyTupleCode 11 geometry.fields

theorem code_ground (pairing : Realize M.sets SetFormula.pairing Fin.elim0) :
    geometry.code ∈ M.sets := M.nonemptyTupleCode_mem pairing 11 geometry.fields geometry.fields_ground

end GroundMainFinalGeometry

end

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

@[instance_reducible] noncomputable def decodedBottom :
    letI := geometry.meet.order.toPartialOrder
    OrderBot (SetMembers geometry.carrier) := by
  letI := geometry.meet.order.toPartialOrder
  refine { bot := SetMembers.ofMem geometry.bottom geometry.bottom_mem, bot_le := ?_ }
  intro x
  change ZFSet.pair (SetMembers.raw (SetMembers.ofMem geometry.bottom geometry.bottom_mem))
    (SetMembers.raw x) ∈ geometry.order
  rw [SetMembers.raw_ofMem]
  exact geometry.least _ (SetMembers.raw_mem x)

noncomputable def decodedAction :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    PosetAction (SetMembers geometry.actors) (SetMembers geometry.carrier) :=
  geometry.action_code.toPosetAction geometry.group_code geometry.meet.order

theorem decoded_order_eq :
    letI := geometry.meet.order.toPartialOrder
    (SetMembers.presentation geometry.carrier).conditionOrder = geometry.order :=
  geometry.meet.order.conditionOrder_eq

theorem decoded_action_eq :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    geometry.decodedAction.actionGraph (SetMembers.presentation geometry.carrier)
      (SetMembers.presentation geometry.actors) = geometry.action :=
  geometry.action_code.actionGraph_eq geometry.group_code geometry.meet.order

theorem decoded_supportBasis_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    supportBasisCode (SetMembers.presentation geometry.carrier) (SetMembers.presentation geometry.actors)
      geometry.decodedAction.principalFix ∈ M.sets :=
  M.decoded_supportBasis_mem geometry.group_code geometry.meet.order geometry.action_code
    pairing unions powers separation geometry.carrier_ground geometry.actors_ground
    geometry.order_ground geometry.action_ground

theorem decoded_unbounded
    (growth : ∀ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
      ZFSet.pair x y ∈ geometry.order ∧ ¬ ZFSet.pair y x ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ x : SetMembers geometry.carrier, ∃ y : SetMembers geometry.carrier, ¬ y ≤ x := by
  let := geometry.meet.order.toPartialOrder
  intro x
  obtain ⟨y, hy, _, strict⟩ := growth _ (SetMembers.raw_mem x)
  refine ⟨SetMembers.ofMem y hy, ?_⟩
  change ¬ ZFSet.pair (SetMembers.raw (SetMembers.ofMem y hy)) (SetMembers.raw x) ∈ geometry.order
  simpa only [SetMembers.raw_ofMem] using strict

theorem decoded_countable_bound
    (bounds : ∀ X ∈ M.sets, X ⊆ geometry.carrier → M.groundEmbeddable X ZFSet.omega →
      ∃ b ∈ geometry.carrier, ∀ x ∈ X, ZFSet.pair x b ∈ geometry.order) :
    letI := geometry.meet.order.toPartialOrder
    ∀ X ∈ M.sets, X ⊆ (SetMembers.presentation geometry.carrier).carrier →
      M.groundEmbeddable X ZFSet.omega →
      ∃ b : SetMembers geometry.carrier, ∀ x : SetMembers geometry.carrier,
        (SetMembers.presentation geometry.carrier).encode x ∈ X → x ≤ b := by
  let := geometry.meet.order.toPartialOrder
  intro X hX subset countable
  obtain ⟨b, hb, bound⟩ := bounds X hX subset countable
  refine ⟨SetMembers.ofMem b hb, ?_⟩
  intro x hx
  change ZFSet.pair (SetMembers.raw x) (SetMembers.raw (SetMembers.ofMem b hb)) ∈ geometry.order
  rw [SetMembers.raw_ofMem]
  exact bound _ hx

end GroundMainFinalGeometry

namespace BoundedFormula
open SetFormula

def separatedActorsFormula : BoundedFormula 7 :=
  exMem 4 (exMem 5 (exMem 5 (exMem 6
    (.conj (orderedPairFormula 4 3 2)
      (.conj (tripleMembershipFormula 3 5 1 9)
        (.conj (tripleMembershipFormula 2 5 0 9) (tripleMembershipFormula 1 0 6 10)))))))

end BoundedFormula

namespace GroundMainFinalGeometry
open SetFormula SetRealization
universe u
variable {M : TransitiveGround.{u}} {C D rD : ZFSet.{u}}
variable (geometry : GroundMainFinalGeometry M C D rD)

theorem separatedActorPairs_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    letI := geometry.group_code.toGroup
    letI := geometry.meet.order.toPartialOrder
    let a := geometry.decodedAction
    let t := SetMembers.presentation geometry.actors
    ∀ (d W : SetMembers geometry.carrier),
      (t.product t).subset (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) ∈ M.sets := by
  let := geometry.group_code.toGroup
  let := geometry.meet.order.toPartialOrder
  let a := geometry.decodedAction
  let s := SetMembers.presentation geometry.carrier
  let t := SetMembers.presentation geometry.actors
  dsimp only
  intro d W
  let params := extend (SetMembers.raw d) (extend (SetMembers.raw W)
    (extend geometry.carrier (extend geometry.actors (extend geometry.action (extend geometry.meetGraph Fin.elim0)))))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.transitive geometry.carrier_ground (SetMembers.raw_mem d))
      (Fin.cases (M.transitive geometry.carrier_ground (SetMembers.raw_mem W))
        (Fin.cases geometry.carrier_ground (Fin.cases geometry.actors_ground
          (Fin.cases geometry.action_ground (Fin.cases geometry.meet_ground (fun i => Fin.elim0 i))))))
  have selected := M.bounded_separation_mem separation BoundedFormula.separatedActorsFormula params members
    (M.prod_mem pairing unions powers separation geometry.actors_ground geometry.actors_ground)
  have correct (z : ZFSet.{u}) : BoundedFormula.Truth BoundedFormula.separatedActorsFormula
      (extend z params) ↔ z ∈ (t.product t).subset
        (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) := by
    simp only [BoundedFormula.separatedActorsFormula, BoundedFormula.truth_exMem, BoundedFormula.Truth,
      BoundedFormula.truth_orderedPairFormula, BoundedFormula.truth_tripleMembershipFormula]
    change (∃ h₁ ∈ geometry.actors, ∃ h₂ ∈ geometry.actors,
      ∃ x ∈ geometry.carrier, ∃ y ∈ geometry.carrier,
      z = ZFSet.pair h₁ h₂ ∧ ZFSet.pair (ZFSet.pair h₁ (SetMembers.raw d)) x ∈ geometry.action ∧
      ZFSet.pair (ZFSet.pair h₂ (SetMembers.raw d)) y ∈ geometry.action ∧
      ZFSet.pair (ZFSet.pair x y) (SetMembers.raw W) ∈ geometry.meetGraph) ↔ _
    have action (g : SetMembers geometry.actors) (x : SetMembers geometry.carrier) :
        ZFSet.pair (ZFSet.pair (SetMembers.raw g) (SetMembers.raw d)) (SetMembers.raw x) ∈ geometry.action ↔
        a.iso g d = x := by
      rw [← geometry.decoded_action_eq]
      exact a.triple_mem_actionGraph s t g d x
    constructor
    · rintro ⟨h₁,hh₁,h₂,hh₂,x,hx,y,hy,shape,first,second,meet⟩
      obtain ⟨g₁,rfl⟩ := (t.mem_carrier h₁).1 hh₁
      obtain ⟨g₂,rfl⟩ := (t.mem_carrier h₂).1 hh₂
      obtain ⟨x,rfl⟩ := (s.mem_carrier x).1 hx
      obtain ⟨y,rfl⟩ := (s.mem_carrier y).1 hy
      have first' := (action g₁ x).1 first
      have second' := (action g₂ y).1 second
      apply ((t.product t).mem_subset _ z).2
      refine ⟨(g₁,g₂),?_,shape.symm⟩
      rw [first',second']
      exact (geometry.meet.smallMeet_eq_iff x y W).2 meet
    · intro hz
      obtain ⟨⟨g₁,g₂⟩,meet,shape⟩ := ((t.product t).mem_subset _ z).1 hz
      exact ⟨t.encode g₁,t.encode_mem g₁,t.encode g₂,t.encode_mem g₂,
        s.encode (a.iso g₁ d),s.encode_mem _,s.encode (a.iso g₂ d),s.encode_mem _,
        shape.symm,(action g₁ _).2 rfl,(action g₂ _).2 rfl,
        (geometry.meet.smallMeet_eq_iff _ _ W).1 meet⟩
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth BoundedFormula.separatedActorsFormula
      (extend z params)) (ZFSet.prod geometry.actors geometry.actors) =
      (t.product t).subset (fun gh => geometry.meet.smallMeet (a.iso gh.1 d) (a.iso gh.2 d) = W) := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep,correct]
    exact ⟨And.right,fun hz => ⟨(t.product t).subset_carrier _ hz,hz⟩⟩
  exact eq ▸ selected

end GroundMainFinalGeometry

end PartitionPilot.Forcing

end OAI
