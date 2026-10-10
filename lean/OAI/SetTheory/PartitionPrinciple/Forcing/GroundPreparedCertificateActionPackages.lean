import OAI.SetTheory.PartitionPrinciple.Definability.GroundActedRepresentativeGraphs
import OAI.SetTheory.PartitionPrinciple.Definability.PreparedCertificateCodes

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

theorem visibilityProfileImage_entry {L G : Type u} [Group G] [PartialOrder L]
    (b : Presentation L) (d : PosetAction G L) (F : ZFSet.{u}) (g : G) (v : L) :
    b.encode (d.iso g v) ∈ relationImage F b.carrier (b.graph b (d.iso g)) ↔
      b.encode v ∈ F := by
  constructor
  · intro member
    obtain ⟨_, x, hx, edge⟩ := (mem_relationImage F b.carrier (b.graph b (d.iso g)) _).1 member
    obtain ⟨w, equal⟩ := (b.mem_graph b (d.iso g) _).1 edge
    have parts := ZFSet.pair_inj.1 equal
    have same : w = v := (d.iso g).injective (b.injective parts.2)
    subst w
    rw [parts.1]
    exact hx
  · intro member
    exact (mem_relationImage F b.carrier (b.graph b (d.iso g)) _).2
      ⟨b.encode_mem _, b.encode v, member, (b.pair_mem_graph b (d.iso g) v _).2 rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}}
variable (closed : ∀ g (z : Name s), z.val ∈ T → (a.act s g z).val ∈ T)

include pairing unions powers separation collection carrier maps closed in
theorem decidesVisibilityProfile_act (F : ZFSet.{u}) (z : Name s) (p : P) (g : G)
    (decisions : M.DecidesVisibilityProfile a s b d.principalFix T F z p) :
    M.DecidesVisibilityProfile a s b d.principalFix T
      (relationImage F b.carrier (b.graph b (d.iso g))) (a.act s g z) (a.iso g p) := by
  intro w
  obtain ⟨v, rfl⟩ := (d.iso g).surjective w
  have profile := visibilityProfileImage_entry b d F g v
  have visibility := M.act_niceVisibilityName a s t d pairing unions powers separation collection
    carrier maps closed g v
  constructor
  · intro yes
    have moved := a.forcesMem_act s g ((decisions v).1 (profile.1 yes))
    rw [visibility] at moved
    exact moved
  · intro no q qp bad
    have oldq : (a.iso g).symm q ≤ p := by simpa using (a.iso g).symm.monotone qp
    have moved : Name.ForcesMem (a.iso g ((a.iso g).symm q)) (a.act s g z)
        (a.act s g (M.niceVisibilityName a s T (d.principalFix v))) := by
      simpa only [OrderIso.apply_symm_apply, visibility] using bad
    exact (decisions v).2 (fun yes => no (profile.2 yes)) _ oldq
      ((a.forcesMem_act_iff s g _ _ _).1 moved)

include closed in
theorem forces_visibilityProfile_act
    (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
    (supports : supportBasisCode b t d.principalFix ∈ M.sets)
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets)
    (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z) (small : M.sets.Countable)
    (F : ZFSet.{u}) (hF : F ∈ M.sets) (z : (M.nameDomain s).names) (p : P) (g : G)
    (forced : Forces (M.nameDomain s) visibilityProfileFormula
      (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
        carrier group nodes supports maps hT valid F hF z) p) :
    let image := relationImage F b.carrier (b.graph b (d.iso g))
    let imageGround := M.relationImage_mem separation hF nodes
      (M.conditionMap_graph_mem d b t nodeMaps g)
    let moved : (M.nameDomain s).names := ⟨a.act s g z.val,
      M.act_mem s a t pairing unions powers separation collection carrier maps g z.val z.property⟩
    Forces (M.nameDomain s) visibilityProfileFormula
      (M.visibilityProfileEnv a s t b d.principalFix pairing unions powers separation collection
        carrier group nodes supports maps hT valid image imageGround moved) (a.iso g p) := by
  dsimp only
  apply (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers separation collection
    carrier group nodes supports maps hT valid small _ _ _ _).2
  apply M.decidesVisibilityProfile_act a s t b d pairing unions powers separation collection carrier maps closed F z.val p g
  exact (M.forces_visibilityProfile_iff a s t b d.principalFix pairing unions powers separation collection
    carrier group nodes supports maps hT valid small F hF z p).1 forced

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {L G : Type u} [Group G] [PartialOrder L]
variable (b : Presentation L) (d : PosetAction G L) (g : G)

theorem nodeBasisImage_nonempty {B : ZFSet.{u}}
    (subset : B ⊆ b.carrier) (nonempty : B.Nonempty) :
    (relationImage B b.carrier (b.graph b (d.iso g))).Nonempty := by
  obtain ⟨x, hx⟩ := nonempty
  obtain ⟨v, rfl⟩ := (b.mem_carrier x).1 (subset hx)
  exact ⟨b.encode (d.iso g v), (visibilityProfileImage_entry b d B g v).2 hx⟩

theorem nodeBasisImage_coinitial {F target B : ZFSet.{u}}
    (subset : F ⊆ b.carrier) (basis : CoinitialBelowCode b.conditionOrder F target B) :
    CoinitialBelowCode b.conditionOrder
      (relationImage F b.carrier (b.graph b (d.iso g)))
      (relationImage target b.carrier (b.graph b (d.iso g)))
      (relationImage B b.carrier (b.graph b (d.iso g))) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨bound, v, hv, edge⟩ := (mem_relationImage B b.carrier (b.graph b (d.iso g)) x).1 hx
    exact (mem_relationImage F b.carrier (b.graph b (d.iso g)) x).2
      ⟨bound, v, basis.1 hv, edge⟩
  · intro x hx
    obtain ⟨_, old, member, edge⟩ :=
      (mem_relationImage target b.carrier (b.graph b (d.iso g)) x).1 hx
    obtain ⟨v, equal⟩ := (b.mem_graph b (d.iso g) _).1 edge
    obtain ⟨oldEq, imageEq⟩ := ZFSet.pair_inj.1 equal
    subst old
    subst x
    obtain ⟨y, hy, below⟩ := basis.2 (b.encode v) member
    obtain ⟨w, rfl⟩ := (b.mem_carrier y).1 (subset (basis.1 hy))
    exact ⟨b.encode (d.iso g w), (visibilityProfileImage_entry b d B g w).2 hy,
      (b.pair_mem_conditionOrder _ _).2
        ((d.iso g).monotone ((b.pair_mem_conditionOrder w v).1 below))⟩

theorem nodeBasisImage_filter {F meetGraph : ZFSet.{u}}
    (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    (filter : MeetFilterCode b.carrier b.conditionOrder meetGraph F) :
    MeetFilterCode b.carrier b.conditionOrder meetGraph
      (relationImage F b.carrier (b.graph b (d.iso g))) := by
  refine ⟨fun x hx => ((mem_relationImage F b.carrier (b.graph b (d.iso g)) x).1 hx).1,
    nodeBasisImage_nonempty b d g filter.subset filter.nonempty, ?_, ?_⟩
  · intro x hx y hy lower
    obtain ⟨v', rfl⟩ := (b.mem_carrier x).1
      ((mem_relationImage F b.carrier (b.graph b (d.iso g)) x).1 hx).1
    obtain ⟨v, rfl⟩ := (d.iso g).surjective v'
    obtain ⟨w', rfl⟩ := (b.mem_carrier y).1 hy
    obtain ⟨w, rfl⟩ := (d.iso g).surjective w'
    apply (visibilityProfileImage_entry b d F g w).2
    exact filter.upward _ ((visibilityProfileImage_entry b d F g v).1 hx) _ (b.encode_mem w)
      ((b.pair_mem_conditionOrder v w).2
        ((d.iso g).le_iff_le.1 ((b.pair_mem_conditionOrder _ _).1 lower)))
  · intro x hx y hy z entry
    have data := meet.pair_iff.1 entry
    obtain ⟨v', rfl⟩ := (b.mem_carrier x).1 data.1
    obtain ⟨v, rfl⟩ := (d.iso g).surjective v'
    obtain ⟨w', rfl⟩ := (b.mem_carrier y).1 data.2.1
    obtain ⟨w, rfl⟩ := (d.iso g).surjective w'
    obtain ⟨k', rfl⟩ := (b.mem_carrier z).1 data.2.2.1
    obtain ⟨k, rfl⟩ := (d.iso g).surjective k'
    apply (visibilityProfileImage_entry b d F g k).2
    apply filter.closed_meet _ ((visibilityProfileImage_entry b d F g v).1 hx)
      _ ((visibilityProfileImage_entry b d F g w).1 hy) _
    apply meet.pair_iff.2
    refine ⟨b.encode_mem v, b.encode_mem w, b.encode_mem k, ?_, ?_, ?_⟩
    · exact (b.pair_mem_conditionOrder k v).2
        ((d.iso g).le_iff_le.1 ((b.pair_mem_conditionOrder _ _).1 data.2.2.2.1))
    · exact (b.pair_mem_conditionOrder k w).2
        ((d.iso g).le_iff_le.1 ((b.pair_mem_conditionOrder _ _).1 data.2.2.2.2.1))
    · intro t ht tv tw
      obtain ⟨r, rfl⟩ := (b.mem_carrier t).1 ht
      have movedBelow := data.2.2.2.2.2 (b.encode (d.iso g r)) (b.encode_mem _)
        ((b.pair_mem_conditionOrder _ _).2 ((d.iso g).monotone ((b.pair_mem_conditionOrder _ _).1 tv)))
        ((b.pair_mem_conditionOrder _ _).2 ((d.iso g).monotone ((b.pair_mem_conditionOrder _ _).1 tw)))
      exact (b.pair_mem_conditionOrder r k).2
        ((d.iso g).le_iff_le.1 ((b.pair_mem_conditionOrder _ _).1 movedBelow))

namespace TransitiveGround
open SetFormula

theorem nodeBasisTransport_ground_small (M : TransitiveGround.{u}) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) (maps : d.conditionMapFamily b t ∈ M.sets)
    {F B size : ZFSet.{u}} (hF : F ∈ M.sets) (hB : B ∈ M.sets) (hSize : size ∈ M.sets)
    (subset : B ⊆ b.carrier) (small : M.groundEmbeddable B size) :
    relationImage F b.carrier (b.graph b (d.iso g)) ∈ M.sets ∧
    relationImage B b.carrier (b.graph b (d.iso g)) ∈ M.sets ∧
    M.groundEmbeddable (relationImage B b.carrier (b.graph b (d.iso g))) size := by
  have mapGround := M.conditionMap_graph_mem d b t maps g
  exact ⟨M.relationImage_mem separation hF nodes mapGround,
    M.relationImage_mem separation hB nodes mapGround,
    M.groundEmbeddable_image pairing unions powers separation hB nodes hSize mapGround
      (b.graph_injection b (d.iso g) (d.iso g).injective) subset small⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u

namespace SynchronizedEnumerationCode

theorem graph_transport {omega nodes movedNodes N movedN B f e names nodeMap nameMap : ZFSet.{u}}
    (code : SynchronizedEnumerationCode omega N B f e names)
    (basis : B ⊆ nodes) (nodeInjection : InjectionCode nodes movedNodes nodeMap)
    (nameFunction : ZFSet.IsFunc N movedN nameMap) :
    SynchronizedEnumerationCode omega movedN (relationImage B movedNodes nodeMap)
      (relationCompose movedNodes B movedN (relationConverse B movedNodes nodeMap)
        (relationCompose B N movedN f nameMap))
      (relationCompose omega B movedNodes e nodeMap)
      (relationCompose omega N movedN names nameMap) := by
  let movedB := relationImage B movedNodes nodeMap
  let inverse := relationConverse B movedNodes nodeMap
  let mapped := relationCompose B N movedN f nameMap
  let movedF := relationCompose movedNodes B movedN inverse mapped
  let movedE := relationCompose omega B movedNodes e nodeMap
  let movedNames := relationCompose omega N movedN names nameMap
  have mappedFunction : ZFSet.IsFunc B movedN mapped :=
    relationCompose_function_of_subset code.1 nameFunction (fun _ h => h)
  have enumFunction : ZFSet.IsFunc omega movedNodes movedE :=
    relationCompose_function_of_subset code.2.1 nodeInjection.function basis
  have namesFunction : ZFSet.IsFunc omega movedN movedNames :=
    relationCompose_function_of_subset code.2.2.1 nameFunction (fun _ h => h)
  have inverseUnique : ∀ x v w, ZFSet.pair x v ∈ inverse →
      ZFSet.pair x w ∈ inverse → v = w := by
    intro x v w first second
    exact nodeInjection.injective v w x
      ((pair_mem_relationConverse B movedNodes nodeMap v x).1 first).2.2
      ((pair_mem_relationConverse B movedNodes nodeMap w x).1 second).2.2
  have movedFunction : ZFSet.IsFunc movedB movedN movedF := by
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, v, hv, tau, ht, rfl, xv, vt⟩ :=
        (mem_relationCompose movedNodes B movedN inverse mapped z).1 hz
      exact ZFSet.pair_mem_prod.2
        ⟨(mem_relationImage B movedNodes nodeMap x).2
          ⟨hx, v, hv, ((pair_mem_relationConverse B movedNodes nodeMap v x).1 xv).2.2⟩, ht⟩
    · intro x hx
      obtain ⟨hxNodes, v, hv, vx⟩ := (mem_relationImage B movedNodes nodeMap x).1 hx
      have xv : ZFSet.pair x v ∈ inverse :=
        (pair_mem_relationConverse B movedNodes nodeMap v x).2 ⟨hv, hxNodes, vx⟩
      obtain ⟨tau, vt, unique⟩ := mappedFunction.2 v hv
      have ht := (ZFSet.pair_mem_prod.1 (mappedFunction.1 vt)).2
      refine ⟨tau, (pair_mem_relationCompose movedNodes B movedN inverse mapped x tau).2
        ⟨hxNodes, ht, v, hv, xv, vt⟩, ?_⟩
      intro other entry
      obtain ⟨_, _, w, _, xw, wt⟩ :=
        (pair_mem_relationCompose movedNodes B movedN inverse mapped x other).1 entry
      exact unique other (inverseUnique x w v xw xv ▸ wt)
  refine ⟨movedFunction, ⟨?_, enumFunction.2⟩, namesFunction, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn, v, hv, x, hx, rfl, nv, vx⟩ :=
      (mem_relationCompose omega B movedNodes e nodeMap z).1 hz
    exact ZFSet.pair_mem_prod.2
      ⟨hn, (mem_relationImage B movedNodes nodeMap x).2 ⟨hx, v, hv, vx⟩⟩
  · intro x hx
    obtain ⟨hxNodes, v, hv, vx⟩ := (mem_relationImage B movedNodes nodeMap x).1 hx
    obtain ⟨n, hn, nv⟩ := code.2.2.2.1 v hv
    exact ⟨n, hn, (pair_mem_relationCompose omega B movedNodes e nodeMap n x).2
      ⟨hn, hxNodes, v, hv, nv, vx⟩⟩
  · intro n hn x tau nx nt
    obtain ⟨_, hx, v, hv, nv, vx⟩ :=
      (pair_mem_relationCompose omega B movedNodes e nodeMap n x).1 nx
    obtain ⟨_, ht, old, hold, no, ot⟩ :=
      (pair_mem_relationCompose omega N movedN names nameMap n tau).1 nt
    have vo := code.2.2.2.2.1 n hn v old nv no
    exact (pair_mem_relationCompose movedNodes B movedN inverse mapped x tau).2
      ⟨hx, ht, v, hv, (pair_mem_relationConverse B movedNodes nodeMap v x).2 ⟨hv, hx, vx⟩,
        (pair_mem_relationCompose B N movedN f nameMap v tau).2 ⟨hv, ht, old, hold, vo, ot⟩⟩
  · intro n hn x tau nx xt
    obtain ⟨_, hx, v, hv, nv, vx⟩ :=
      (pair_mem_relationCompose omega B movedNodes e nodeMap n x).1 nx
    obtain ⟨_, ht, w, _, xw, wt⟩ :=
      (pair_mem_relationCompose movedNodes B movedN inverse mapped x tau).1 xt
    have xv : ZFSet.pair x v ∈ inverse :=
      (pair_mem_relationConverse B movedNodes nodeMap v x).2 ⟨hv, hx, vx⟩
    have vt := inverseUnique x w v xw xv ▸ wt
    obtain ⟨_, _, old, hold, vo, ot⟩ :=
      (pair_mem_relationCompose B N movedN f nameMap v tau).1 vt
    exact (pair_mem_relationCompose omega N movedN names nameMap n tau).2
      ⟨hn, ht, old, hold, code.2.2.2.2.2 n hn v old nv vo, ot⟩

end SynchronizedEnumerationCode

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem synchronizedEnumerationTransport_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {omega movedNodes N movedN B f e names nodeMap nameMap : ZFSet.{u}}
    (hOmega : omega ∈ M.sets) (hNodes : movedNodes ∈ M.sets)
    (hN : N ∈ M.sets) (hMovedN : movedN ∈ M.sets) (hB : B ∈ M.sets)
    (hf : f ∈ M.sets) (he : e ∈ M.sets) (hNames : names ∈ M.sets)
    (hNodeMap : nodeMap ∈ M.sets) (hNameMap : nameMap ∈ M.sets) :
    relationImage B movedNodes nodeMap ∈ M.sets ∧
    relationCompose movedNodes B movedN (relationConverse B movedNodes nodeMap)
      (relationCompose B N movedN f nameMap) ∈ M.sets ∧
    relationCompose omega B movedNodes e nodeMap ∈ M.sets ∧
    relationCompose omega N movedN names nameMap ∈ M.sets := by
  exact ⟨M.relationImage_mem separation hB hNodes hNodeMap,
    M.relationCompose_mem pairing unions powers separation hNodes hB hMovedN
      (M.relationConverse_mem pairing unions powers separation hB hNodes hNodeMap)
      (M.relationCompose_mem pairing unions powers separation hB hN hMovedN hf hNameMap),
    M.relationCompose_mem pairing unions powers separation hOmega hB hNodes he hNodeMap,
    M.relationCompose_mem pairing unions powers separation hOmega hN hMovedN hNames hNameMap⟩

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization
universe u
variable {L G : Type u} [Group G] [PartialOrder L]
variable (b : Presentation L) (d : PosetAction G L) (g : G)

theorem nodeEnumerationImage_entry {omega B e : ZFSet.{u}}
    (function : ZFSet.IsFunc omega B e) (n : ZFSet.{u}) (v : L) :
    ZFSet.pair n (b.encode (d.iso g v)) ∈
      relationCompose omega B b.carrier e (b.graph b (d.iso g)) ↔
        ZFSet.pair n (b.encode v) ∈ e := by
  constructor
  · intro member
    obtain ⟨_, _, old, _, edge, moved⟩ :=
      (pair_mem_relationCompose omega B b.carrier e (b.graph b (d.iso g)) n _).1 member
    obtain ⟨w, equal⟩ := (b.mem_graph b (d.iso g) _).1 moved
    obtain ⟨oldEq, movedEq⟩ := ZFSet.pair_inj.1 equal
    have same : w = v := (d.iso g).injective (b.injective movedEq)
    subst w
    exact oldEq ▸ edge
  · intro edge
    have bounds := ZFSet.pair_mem_prod.1 (function.1 edge)
    exact (pair_mem_relationCompose omega B b.carrier e (b.graph b (d.iso g)) n _).2
      ⟨bounds.1, b.encode_mem _, b.encode v, bounds.2, edge,
        (b.pair_mem_graph b (d.iso g) v _).2 rfl⟩

theorem nodeEnumerationImage_function {omega B e : ZFSet.{u}}
    (function : ZFSet.IsFunc omega B e) (subset : B ⊆ b.carrier) :
    ZFSet.IsFunc omega (relationImage B b.carrier (b.graph b (d.iso g)))
      (relationCompose omega B b.carrier e (b.graph b (d.iso g))) := by
  have composed := relationCompose_function_of_subset function (b.graph_isFunc b (d.iso g)) subset
  refine ⟨?_, composed.2⟩
  intro z member
  obtain ⟨n, hn, v, hv, w, hw, rfl, nv, vw⟩ :=
    (mem_relationCompose omega B b.carrier e (b.graph b (d.iso g)) z).1 member
  exact ZFSet.pair_mem_prod.2
    ⟨hn, (mem_relationImage B b.carrier (b.graph b (d.iso g)) w).2 ⟨hw, v, hv, vw⟩⟩

theorem nodeEnumerationImage_onto {omega B e : ZFSet.{u}}
    (onto : ∀ v ∈ B, ∃ n ∈ omega, ZFSet.pair n v ∈ e) :
    ∀ w ∈ relationImage B b.carrier (b.graph b (d.iso g)), ∃ n ∈ omega,
      ZFSet.pair n w ∈ relationCompose omega B b.carrier e (b.graph b (d.iso g)) := by
  intro w hw
  obtain ⟨bound, v, hv, vw⟩ := (mem_relationImage B b.carrier (b.graph b (d.iso g)) w).1 hw
  obtain ⟨n, hn, nv⟩ := onto v hv
  exact ⟨n, hn, (pair_mem_relationCompose omega B b.carrier e (b.graph b (d.iso g)) n w).2
    ⟨hn, bound, v, hv, nv, vw⟩⟩

namespace TransitiveGround
open SetFormula

theorem nodeEnumerationImage_ground (M : TransitiveGround.{u}) (t : Presentation G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (nodes : b.carrier ∈ M.sets) (maps : d.conditionMapFamily b t ∈ M.sets)
    {omega B e : ZFSet.{u}} (hOmega : omega ∈ M.sets) (hB : B ∈ M.sets) (he : e ∈ M.sets) :
    relationCompose omega B b.carrier e (b.graph b (d.iso g)) ∈ M.sets :=
  M.relationCompose_mem pairing unions powers separation hOmega hB nodes he
    (M.conditionMap_graph_mem d b t maps g)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]

theorem visibilitySupportIncidence_act_iff
    (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
    (b : Presentation L) (d : PosetAction G L)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets)
    (carrier : s.carrier ∈ M.sets) (maps : a.conditionMapFamily s t ∈ M.sets)
    {T : ZFSet.{u}}
    (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
    (g : G) (v : L) (tau : Name s) :
    ZFSet.pair (b.encode (d.iso g v)) (a.act s g tau).val ∈
      visibilitySupportIncidence b.carrier (M.groundRelations T s.carrier)
        (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) ↔
    ZFSet.pair (b.encode v) tau.val ∈
      visibilitySupportIncidence b.carrier (M.groundRelations T s.carrier)
        (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤) := by
  rw [M.visibilitySupportIncidence_candidates, M.visibilitySupportIncidence_candidates]
  have moved := M.niceNameCandidates_principal_act_iff a s t pairing unions powers
    separation collection carrier maps closed d g v tau
  rw [M.mem_niceNameCandidates, M.mem_niceNameCandidates] at moved
  exact moved

end PartitionPilot.Forcing.TransitiveGround




namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier order group nodes supports maps hT valid closed

theorem preparedCertificateCode_act
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    (z : (M.nameDomain s).names) (F B f e names : ZFSet.{u}) (p : P) (g : G)
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder meetGraph (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega z.val.val F B f e names) :
    let N := M.groundRelations T s.carrier
    let validN := fun x (hx : x ∈ N) =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier x).1 hx).2
    let nodeMap := b.graph b (d.iso g)
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode (a.iso g p))
      b.carrier b.conditionOrder meetGraph N
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega (a.act s g z.val).val
      (relationImage F b.carrier nodeMap) (relationImage B b.carrier nodeMap)
      (Name.actedRepresentativeGraph a s b d N validN g B f)
      (relationCompose ZFSet.omega B b.carrier e nodeMap)
      (Name.actedEnumerationGraph a s N validN g ZFSet.omega names) := by
  let N := M.groundRelations T s.carrier
  let validN := fun x (hx : x ∈ N) =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier x).1 hx).2
  have hN := M.groundRelations_mem pairing unions powers separation hT carrier
  have nameClosed (tau : Name s) (member : tau.val ∈ N) : (a.act s g tau).val ∈ N := by
    obtain ⟨ground, shape⟩ := (M.mem_groundRelations T s.carrier tau.val).1 member
    exact (M.mem_groundRelations T s.carrier _).2
      ⟨M.act_mem s a t pairing unions powers separation collection carrier maps g tau ground,
        Name.act_subset_of_closed a closed shape g⟩
  have graphGround := M.niceVisibilityGraph_mem a s t b d.principalFix pairing unions powers
    separation collection carrier group nodes supports maps hT valid
  obtain ⟨filter, basis, nonempty, enumerated, supported, forced⟩ := code
  have basisNodes : B ⊆ b.carrier := fun v hv => filter.subset (basis.1 hv)
  have originalRange : f ⊆ ZFSet.prod b.carrier N := by
    intro entry member
    obtain ⟨v, hv, tau, ht, rfl⟩ := ZFSet.mem_prod.1 (enumerated.1.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨basisNodes hv, ht⟩
  have original := (M.preparationForcingCode_iff a s b d.principalFix pairing unions powers
    separation collection carrier order T N graphGround hN validN z F f originalRange p).1 forced
  have movedEnumeration := enumerated.graph_transport basisNodes
    (b.graph_injection b (d.iso g) (d.iso g).injective)
    (Name.renameFamilyGraph_act_function a s N validN g nameClosed)
  have movedFilter := nodeBasisImage_filter b d g meet filter
  have movedBasis := nodeBasisImage_coinitial b d g filter.subset basis
  let movedF := Name.actedRepresentativeGraph a s b d N validN g B f
  have movedFunction : ZFSet.IsFunc (relationImage B b.carrier (b.graph b (d.iso g))) N movedF :=
    movedEnumeration.1
  have movedRange : movedF ⊆ ZFSet.prod b.carrier N := by
    intro entry member
    obtain ⟨v, hv, tau, ht, rfl⟩ := ZFSet.mem_prod.1 (movedFunction.1 member)
    exact ZFSet.pair_mem_prod.2 ⟨movedFilter.subset (movedBasis.1 hv), ht⟩
  have movedEdges (v tau : ZFSet.{u}) (entry : ZFSet.pair v tau ∈ movedF) :
      ∃ w : L, ∃ sigma : Name s,
        ZFSet.pair (b.encode w) sigma.val ∈ f ∧
        v = b.encode (d.iso g w) ∧ tau = (a.act s g sigma).val := by
    obtain ⟨w', rfl⟩ := (b.mem_carrier v).1 (ZFSet.pair_mem_prod.1 (movedRange entry)).1
    obtain ⟨w, rfl⟩ := (d.iso g).surjective w'
    obtain ⟨sigma, old, equal⟩ :=
      (Name.pair_mem_actedRepresentativeGraph a s b d N validN g basisNodes
        enumerated.1 nameClosed w tau).1 entry
    exact ⟨w, sigma, old, rfl, equal⟩
  dsimp only
  refine ⟨movedFilter, movedBasis, nodeBasisImage_nonempty b d g basisNodes nonempty,
    movedEnumeration, ?_, ?_⟩
  · intro v tau entry
    obtain ⟨w, sigma, old, rfl, rfl⟩ := movedEdges v tau entry
    exact (M.visibilitySupportIncidence_act_iff a s t b d pairing unions powers separation
      collection carrier maps closed g w sigma).2 (supported _ _ old)
  · let moved : (M.nameDomain s).names := ⟨a.act s g z.val,
      M.act_mem s a t pairing unions powers separation collection carrier maps g z.val z.property⟩
    apply (M.preparationForcingCode_iff a s b d.principalFix pairing unions powers
      separation collection carrier order T N graphGround hN validN moved
      (relationImage F b.carrier (b.graph b (d.iso g))) movedF movedRange (a.iso g p)).2
    refine ⟨M.decidesVisibilityProfile_act a s t b d pairing unions powers separation collection
      carrier maps closed F z.val p g original.1, ?_⟩
    intro v tau _ entry
    obtain ⟨w, sigma, old, _equalNode, equalName⟩ := movedEdges v tau.val entry
    have sigmaInN := (ZFSet.pair_mem_prod.1 (enumerated.1.1 old)).2
    have equal : tau = a.act s g sigma := Subtype.ext equalName
    rw [equal]
    exact a.forcesEq_act s g (original.2 (b.encode w) sigma sigmaInN old)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u}) {L G P : Type u}
variable [Group G] [PartialOrder L] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (t : Presentation G)
variable (b : Presentation L) (d : PosetAction G L)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)
variable (group : t.carrier ∈ M.sets) (nodes : b.carrier ∈ M.sets)
variable (supports : supportBasisCode b t d.principalFix ∈ M.sets)
variable (maps : a.conditionMapFamily s t ∈ M.sets)
variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)
variable (closed : ∀ g (tau : Name s), tau.val ∈ T → (a.act s g tau).val ∈ T)
include pairing unions powers separation collection carrier order group nodes supports maps hT valid closed

theorem preparedCertificateCode_act_ground_hs
    (nodeMaps : d.conditionMapFamily b t ∈ M.sets) (omega : ZFSet.omega ∈ M.sets)
    (base : L) (directed : ∀ v w : L, ∃ x, v ≤ x ∧ w ≤ x)
    (children : ∀ tau : Name s, tau.val ∈ T →
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau)
    (meetGraph : ZFSet.{u}) (meet : MeetOrderCode b.carrier b.conditionOrder meetGraph)
    (z : (M.nameDomain s).names) (F B f e names : ZFSet.{u})
    (hF : F ∈ M.sets) (hB : B ∈ M.sets) (hf : f ∈ M.sets)
    (he : e ∈ M.sets) (hNames : names ∈ M.sets) (p : P) (g : G)
    (code : PreparedCertificateCode M s.carrier s.conditionOrder (s.encode p)
      b.carrier b.conditionOrder meetGraph (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega z.val.val F B f e names) :
    let N := M.groundRelations T s.carrier
    let validN := fun x (hx : x ∈ N) =>
      Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier x).1 hx).2
    let nodeMap := b.graph b (d.iso g)
    let movedF := relationImage F b.carrier nodeMap
    let movedB := relationImage B b.carrier nodeMap
    let movedFunction := Name.actedRepresentativeGraph a s b d N validN g B f
    let movedE := relationCompose ZFSet.omega B b.carrier e nodeMap
    let movedNames := Name.actedEnumerationGraph a s N validN g ZFSet.omega names
    movedF ∈ M.sets ∧ movedB ∈ M.sets ∧ movedFunction ∈ M.sets ∧
      movedE ∈ M.sets ∧ movedNames ∈ M.sets ∧
    PreparedCertificateCode M s.carrier s.conditionOrder (s.encode (a.iso g p))
      b.carrier b.conditionOrder meetGraph N
      (M.niceVisibilityGraph a s b T d.principalFix) (s.encode ⊤)
      ZFSet.omega (a.act s g z.val).val movedF movedB movedFunction movedE movedNames ∧
    ∀ (v : L) (tau : Name s), ZFSet.pair (b.encode v) tau.val ∈ movedFunction →
      tau.val ∈ M.sets ∧ NiceNameCode a s T (d.principalFix v) tau.val ∧
      HereditarilySymmetric a s (d.principalSupportFamily base directed) tau := by
  let N := M.groundRelations T s.carrier
  let validN := fun x (hx : x ∈ N) =>
    Name.isName_of_subset valid ((M.mem_groundRelations T s.carrier x).1 hx).2
  have hN := M.groundRelations_mem pairing unions powers separation hT carrier
  have hNodeMap := M.conditionMap_graph_mem d b t nodeMaps g
  have moved := M.preparedCertificateCode_act a s t b d pairing unions powers separation collection
    carrier order group nodes supports maps hT valid closed meetGraph meet z F B f e names p g code
  refine ⟨M.relationImage_mem separation hF nodes hNodeMap,
    M.relationImage_mem separation hB nodes hNodeMap,
    M.actedRepresentativeGraph_mem a s b d t N validN pairing unions powers separation collection
      carrier nodes maps nodeMaps hN g hB hf,
    M.relationCompose_mem pairing unions powers separation omega hB nodes he hNodeMap,
    M.actedEnumerationGraph_mem a s t N validN pairing unions powers separation collection
      carrier maps hN g omega hNames, moved, ?_⟩
  intro v tau entry
  have candidate := (M.visibilitySupportIncidence_candidates a s b T d.principalFix v tau.val).1
    (moved.2.2.2.2.1 _ _ entry)
  exact ⟨candidate.1, candidate.2,
    niceNameCode_hs a s (d.principalSupportFamily base directed) ⟨v, le_rfl⟩ children candidate.2⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
