import OAI.SetTheory.PartitionPrinciple.Definability.MainLimitCoverageFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def visibilitySupportIncidence
    (nodes names visibility top : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v tau, z = ZFSet.pair v tau ∧
    ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V)
    (ZFSet.prod nodes names)

theorem mem_visibilitySupportIncidence
    (nodes names visibility top z : ZFSet.{u}) :
    z ∈ visibilitySupportIncidence nodes names visibility top ↔
      ∃ v ∈ nodes, ∃ tau ∈ names, z = ZFSet.pair v tau ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [visibilitySupportIncidence, ZFSet.mem_sep]
  constructor
  · rintro ⟨bound, v, tau, rfl, V, entry, member⟩
    exact ⟨v, (ZFSet.pair_mem_prod.1 bound).1,
      tau, (ZFSet.pair_mem_prod.1 bound).2, rfl, V, entry, member⟩
  · rintro ⟨v, hv, tau, htau, rfl, V, entry, member⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, htau⟩, v, tau, rfl, V, entry, member⟩

theorem pair_mem_visibilitySupportIncidence
    (nodes names visibility top v tau : ZFSet.{u}) :
    ZFSet.pair v tau ∈ visibilitySupportIncidence nodes names visibility top ↔
      v ∈ nodes ∧ tau ∈ names ∧
        ∃ V, ZFSet.pair v V ∈ visibility ∧ ZFSet.pair tau top ∈ V := by
  rw [mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨v', hv, tau', htau, equal, witness⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, htau, witness⟩
  · rintro ⟨hv, htau, witness⟩
    exact ⟨v, hv, tau, htau, rfl, witness⟩

namespace BoundedFormula

def visibilitySupportIncidenceFormula {n}
    (entry nodes names visibility top : Fin n) : BoundedFormula n :=
  exPairFields entry
    (.conj (.mem 1 nodes.succ.succ)
      (.conj (.mem 0 names.succ.succ)
        (exGraphFields visibility.succ.succ
          (.conj (.equal 1 3)
            (pairMembershipFormula 2 top.succ.succ.succ.succ 0)))))

theorem truth_visibilitySupportIncidenceFormula {n}
    (entry nodes names visibility top : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (visibilitySupportIncidenceFormula entry nodes names visibility top) env ↔
      env entry ∈ visibilitySupportIncidence (env nodes) (env names)
        (env visibility) (env top) := by
  simp only [visibilitySupportIncidenceFormula, truth_exPairFields, Truth,
    truth_exGraphFields, truth_pairMembershipFormula]
  rw [mem_visibilitySupportIncidence]
  change (∃ v tau, env entry = ZFSet.pair v tau ∧ v ∈ env nodes ∧
    tau ∈ env names ∧ ∃ v' V, ZFSet.pair v' V ∈ env visibility ∧
      v' = v ∧ ZFSet.pair tau (env top) ∈ V) ↔ _
  constructor
  · rintro ⟨v, tau, equal, hv, htau, v', V, edge, rfl, member⟩
    exact ⟨v', hv, tau, htau, equal, V, edge, member⟩
  · rintro ⟨v, hv, tau, htau, equal, V, edge, member⟩
    exact ⟨v, tau, equal, hv, htau, v, V, edge, rfl, member⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def visibilitySupportAt {n} (node tau nodes names visibility top : Fin n) : BoundedFormula n :=
  .conj (.mem node nodes) (.conj (.mem tau names)
    (exGraphFields visibility (.conj (.equal 1 node.succ.succ)
      (pairMembershipFormula tau.succ.succ top.succ.succ 0))))

theorem truth_visibilitySupportAt {n} (node tau nodes names visibility top : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (visibilitySupportAt node tau nodes names visibility top) env ↔
      ZFSet.pair (env node) (env tau) ∈ visibilitySupportIncidence
        (env nodes) (env names) (env visibility) (env top) := by
  simp only [visibilitySupportAt, Truth, truth_exGraphFields, truth_pairMembershipFormula]
  rw [pair_mem_visibilitySupportIncidence]
  change (env node ∈ env nodes ∧ env tau ∈ env names ∧
    ∃ v V, ZFSet.pair v V ∈ env visibility ∧ v = env node ∧
      ZFSet.pair (env tau) (env top) ∈ V) ↔ _
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨v, V, edge, rfl, member⟩
    exact ⟨V, edge, member⟩
  · rintro ⟨V, edge, member⟩
    exact ⟨env node, V, edge, rfl, member⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula SetRealization
universe u
variable (M : TransitiveGround.{u})

theorem visibilitySupportIncidence_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {nodes names visibility top : ZFSet.{u}}
    (hNodes : nodes ∈ M.sets) (hNames : names ∈ M.sets)
    (hVisibility : visibility ∈ M.sets) (hTop : top ∈ M.sets) :
    visibilitySupportIncidence nodes names visibility top ∈ M.sets := by
  let params := extend nodes (extend names (extend visibility (extend top Fin.elim0)))
  have ground := M.bounded_separation_mem separation
    (BoundedFormula.visibilitySupportIncidenceFormula 0 1 2 3 4) params
    (Fin.cases hNodes (Fin.cases hNames (Fin.cases hVisibility
      (Fin.cases hTop (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hNodes hNames)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.visibilitySupportIncidenceFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod nodes names) = visibilitySupportIncidence nodes names visibility top := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_visibilitySupportIncidenceFormula]
    exact and_iff_right_of_imp (fun member => (ZFSet.mem_sep.1 member).1)
  exact equal ▸ ground

variable {I G P : Type u} [Group G] [PartialOrder P] [OrderTop P]
variable (a : PosetAction G P) (s : Presentation P) (b : Presentation I)
variable (T : ZFSet.{u}) (K : I → Subgroup G)

theorem visibilitySupportIncidence_candidates (v : I) (tau : ZFSet.{u}) :
    ZFSet.pair (b.encode v) tau ∈ visibilitySupportIncidence b.carrier
      (M.groundRelations T s.carrier) (M.niceVisibilityGraph a s b T K) (s.encode ⊤) ↔
      tau ∈ M.sets ∧ NiceNameCode a s T (K v) tau := by
  rw [pair_mem_visibilitySupportIncidence]
  constructor
  · rintro ⟨_, _, V, entry, member⟩
    have equal := (M.pair_mem_niceVisibilityGraph a s b T K v V).1 entry
    rw [equal, M.niceVisibilityName_code] at member
    exact (M.mem_niceNameCandidates a s T (K v) tau).1
      (ZFSet.pair_mem_prod.1 member).1
  · intro code
    have member := (M.mem_niceNameCandidates a s T (K v) tau).2 code
    refine ⟨b.encode_mem v, M.niceNameCandidates_subset a s T (K v) member,
      (M.niceVisibilityName a s T (K v)).val,
      (M.pair_mem_niceVisibilityGraph a s b T K v _).2 rfl, ?_⟩
    rw [M.niceVisibilityName_code]
    exact ZFSet.pair_mem_prod.2 ⟨member, ZFSet.mem_singleton.2 rfl⟩

theorem visibilitySupportIncidence_eq_niceSupportRelation :
    visibilitySupportIncidence b.carrier (M.groundRelations T s.carrier)
      (M.niceVisibilityGraph a s b T K) (s.encode ⊤) =
      M.niceSupportRelation a s b T K := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨v, hv, tau, _, rfl, _⟩ :=
      (mem_visibilitySupportIncidence _ _ _ _ z).1 member
    obtain ⟨i, rfl⟩ := (b.mem_carrier v).1 hv
    exact (M.pair_mem_niceSupportRelation a s b T K i tau).2
      ((M.visibilitySupportIncidence_candidates a s b T K i tau).1 member)
  · intro member
    obtain ⟨_, i, tau, rfl, _⟩ := ZFSet.mem_sep.1 member
    exact (M.visibilitySupportIncidence_candidates a s b T K i tau).2
      ((M.pair_mem_niceSupportRelation a s b T K i tau).1 member)

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
