import OAI.SetTheory.PartitionPrinciple.Geometry.GroundSerializedCandidateLevels

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula
def linkedMainStageFormula {n} (K Labels C D rD N z : Fin n) : SetFormula n :=
  let old := suffixIndex n 24
  exBlock 24 (linkedMainStageRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N) (old z)
    (prefixIndex n 24))
end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedMainStageFormula_raw {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ f : Fin 24 → ZFSet.{u}, (∀ j, f j ∈ M.sets) ∧
        LinkedMainStageRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N) (env z) f := by
  rw [linkedMainStageFormula, realize_exBlock]
  have actual (f : Fin 24 → ZFSet.{u}) (ground : ∀ j, f j ∈ M.sets) :=
    M.realize_linkedMainStageRawFormula pairing unions powers separation collection
      (suffixIndex n 24 K) (suffixIndex n 24 Labels) (suffixIndex n 24 C) (suffixIndex n 24 D)
      (suffixIndex n 24 rD) (suffixIndex n 24 N) (suffixIndex n 24 z) (prefixIndex n 24)
      (extendMany 24 f env) (extendMany_members 24 f env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨f, ground, recognized⟩
    exact ⟨f, ground, (actual f ground).1 recognized⟩
  · rintro ⟨f, ground, raw⟩
    exact ⟨f, ground, (actual f ground).2 raw⟩

theorem realize_linkedMainStageFormula {n} (K Labels C D rD N z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedMainStageFormula K Labels C D rD N z) env ↔
      ∃ linked : GroundLinkedMainStage M (env K) (env Labels) (env C) (env D) (env rD),
        linked.code = env z := by
  rw [M.realize_linkedMainStageFormula_raw pairing unions powers separation collection
    K Labels C D rD N z env members omega ordinal]
  constructor
  · rintro ⟨f, ground, raw⟩
    exact raw.exists_linked pairing unions powers separation ground (members C) (members D) (members rD) omega
  · rintro ⟨linked, equal⟩
    refine ⟨linked.rawFields, linked.rawFields_ground pairing, ?_⟩
    rw [omega, ← equal]
    exact linked.rawFields_code

noncomputable def linkedMainStageCandidates (B K Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z) B

omit pairing unions powers separation collection in
theorem mem_linkedMainStageCandidates (B K Labels C D rD z : ZFSet.{u}) :
    z ∈ M.linkedMainStageCandidates B K Labels C D rD ↔
      z ∈ B ∧ ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z := ZFSet.mem_sep

theorem linkedMainStageCandidates_mem (infinite : Realize M.sets infinity Fin.elim0)
    {B K Labels C D rD : ZFSet.{u}} (hB : B ∈ M.sets) (hK : K ∈ M.sets)
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets)
    (ordinal : ordinalSetProperty K) : M.linkedMainStageCandidates B K Labels C D rD ∈ M.sets := by
  let params := extend K (extend Labels (extend C (extend D (extend rD (extend ZFSet.omega Fin.elim0)))))
  have ground : ∀ j, params j ∈ M.sets := Fin.cases hK (Fin.cases hLabels (Fin.cases hC
    (Fin.cases hD (Fin.cases hrD (Fin.cases (M.omega_mem separation infinite) (fun i => Fin.elim0 i))))))
  have selected := M.separation_mem separation (linkedMainStageFormula 1 2 3 4 5 6 0) params ground hB
  have equal : ZFSet.sep (fun z => Realize M.sets (linkedMainStageFormula 1 2 3 4 5 6 0)
      (extend z params)) B = M.linkedMainStageCandidates B K Labels C D rD := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, M.mem_linkedMainStageCandidates]
    apply and_congr_right
    intro hz
    exact M.realize_linkedMainStageFormula pairing unions powers separation collection
      1 2 3 4 5 6 0 (extend z params) (Fin.cases (M.transitive hB hz) ground) rfl ordinal
  exact equal ▸ selected

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace GroundMainCandidateLevel
variable {M : TransitiveGround.{u}} {K : ZFSet.{u}}
variable (level : GroundMainCandidateLevel M K)

noncomputable def validLinkedStages (Labels C D rD : ZFSet.{u}) : ZFSet.{u} :=
  M.linkedMainStageCandidates level.carrier K Labels C D rD

theorem validLinkedStages_ground
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (ordinal : ordinalSetProperty K) {Labels C D rD : ZFSet.{u}}
    (hLabels : Labels ∈ M.sets) (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hrD : rD ∈ M.sets) :
    level.validLinkedStages Labels C D rD ∈ M.sets :=
  M.linkedMainStageCandidates_mem pairing unions powers separation collection infinite
    level.carrier_ground hK hLabels hC hD hrD ordinal

theorem mem_validLinkedStages {Labels C D rD z : ZFSet.{u}} :
    z ∈ level.validLinkedStages Labels C D rD ↔
      z ∈ level.carrier ∧ ∃ linked : GroundLinkedMainStage M K Labels C D rD, linked.code = z :=
  M.mem_linkedMainStageCandidates level.carrier K Labels C D rD z

theorem linked_mem_validLinkedStages
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {Labels C D rD : ZFSet.{u}} (linked : GroundLinkedMainStage M K Labels C D rD) :
    linked.code ∈ level.validLinkedStages Labels C D rD :=
  level.mem_validLinkedStages.2 ⟨(level.membership _).2 ⟨linked.code_ground pairing,
    linked.code_rank_lt pairing unions powers separation infinite hK conditions⟩, linked, rfl⟩

theorem validLinkedStageFamily_rank_lt
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (collection : CollectionSchema M.sets) (infinite : Realize M.sets infinity Fin.elim0)
    (hK : K ∈ M.sets) (conditions : GroundInaccessibleConditions M K)
    {I Labels C D rD f : ZFSet.{u}} (hI : I ∈ K) (hf : f ∈ M.sets)
    (function : ZFSet.IsFunc I (level.validLinkedStages Labels C D rD) f) :
    ZFSet.rank f < ZFSet.rank K := by
  apply conditions.functionGraphOn_rank_lt pairing unions powers separation collection infinite
    hK hI hf ⟨level.validLinkedStages Labels C D rD, function⟩
  intro i _ v entry
  have hv := (ZFSet.pair_mem_prod.1 (function.1 entry)).2
  exact ((level.membership v).1 (level.mem_validLinkedStages.1 hv).1).2

end GroundMainCandidateLevel
end PartitionPilot.Forcing

end

end OAI
