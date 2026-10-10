import OAI.SetTheory.PartitionPrinciple.Transfinite.ExternalChronologyStageLaws

namespace OAI

section

namespace PartitionPilot.Forcing.GroundExternalBirthData
open SetFormula
universe u
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T τ P0 r0 μ0 A0 oldTimes oldBirth C D rD lo hi seed : ZFSet.{u}}
variable {completion : GroundCompressionCompletion M initial I Sources Reps G m one T τ}
variable (births : GroundExternalBirthData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 oldTimes oldBirth completion)
variable (heights : GroundExternalHeightData M initial I Sources Reps G m one T τ
  P0 r0 μ0 A0 C D rD lo hi seed completion)

noncomputable def cutoffField : Fin 5 → Nat → ZFSet.{u} :=
  Fin.cases births.cutoff (Fin.cases births.cutoffOrder (Fin.cases births.cutoffMeet
    (Fin.cases births.cutoffBirth (fun _ => births.cutoffHeight heights.height))))

noncomputable def terminalField : Fin 5 → ZFSet.{u} :=
  Fin.cases (completion.externalPointCarrier P0 r0 μ0 A0)
    (Fin.cases (completion.externalPointOrder P0 r0 μ0 A0)
      (Fin.cases (completion.externalPointMeet P0 r0 μ0 A0)
        (Fin.cases births.birth (fun _ => heights.height))))

noncomputable def cutoffFieldFamily : Fin 5 → ZFSet.{u} :=
  Fin.cases births.cutoffFamily
    (Fin.cases (M.chronologyRestrictionFamily 1 ZFSet.omega births.cutoffFamily
      (completion.externalPointOrder P0 r0 μ0 A0))
    (Fin.cases (M.chronologyRestrictionFamily 2 ZFSet.omega births.cutoffFamily
      (completion.externalPointMeet P0 r0 μ0 A0))
    (Fin.cases (M.chronologyRestrictionFamily 0 ZFSet.omega births.cutoffFamily births.birth)
      (fun _ => M.chronologyRestrictionFamily 0 ZFSet.omega births.cutoffFamily heights.height))))

variable {inv : ZFSet.{u}}
variable (data : GroundExternalGeometryInputs M initial I Sources Reps G m inv one T τ P0 r0 μ0 A0 completion)
variable (group : GroupCode G m inv one) (action : PosetActionCode G P0 m one r0 A0)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (infinite : Realize M.sets infinity Fin.elim0) (hG : G ∈ M.sets) (hP0 : P0 ∈ M.sets)
include data group action pairing unions powers separation infinite hG hP0

theorem terminalField_ground (j : Fin 5) : births.terminalField heights j ∈ M.sets := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  exact Fin.cases geometry.carrier_ground (Fin.cases geometry.order_ground
    (Fin.cases geometry.meet_ground (Fin.cases births.birth_ground (fun _ => heights.height_ground)))) j

theorem cutoffFieldFamily_spec (j : Fin 5) :
    births.cutoffFieldFamily heights j ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (births.cutoffFieldFamily heights j) ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ births.cutoffFieldFamily heights j ↔
        y = births.cutoffField heights j n := by
  have geometry := data.externalGeometryData group action pairing unions powers separation infinite hG hP0
  have domains := births.cutoffFamily_spec data group action pairing unions powers separation infinite hG hP0
  have hOmega := M.omega_mem separation infinite
  have restrictions (kind : Fin 3) {f : ZFSet.{u}} (hf : f ∈ M.sets) :
      M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f ∈ M.sets ∧
      FunctionGraphOn ZFSet.omega (M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f) ∧
      ∀ n y, ZFSet.pair (natSetCode n) y ∈ M.chronologyRestrictionFamily kind ZFSet.omega births.cutoffFamily f ↔
        y = chronologyRestriction kind (births.cutoff n) f :=
    ⟨M.chronologyRestrictionFamily_mem pairing unions powers separation kind hOmega domains.1 hf,
      ⟨_, M.chronologyRestrictionFamily_function pairing unions powers separation kind domains.1 hf domains.2.1⟩,
      fun n y => M.chronologyRestrictionFamily_entries pairing unions powers separation kind
        domains.1 hf domains.2.1 ((domains.2.2 n _).2 rfl) y⟩
  exact Fin.cases domains (Fin.cases (restrictions 1 geometry.order_ground)
    (Fin.cases (restrictions 2 geometry.meet_ground)
      (Fin.cases (restrictions 0 births.birth_ground) (fun _ => restrictions 0 heights.height_ground)))) j

end PartitionPilot.Forcing.GroundExternalBirthData

end

end OAI
