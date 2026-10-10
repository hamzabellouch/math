import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionUnionBaseFilling

namespace OAI

open scoped ZFSet

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

noncomputable def definable_compressionBases : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => familyEvaluationGraph
      (env 0) (env 1) (env 1) (⋃₀ ⋃₀ env 2) (env 2) (env 3)) := by
  let v : Fin 4 → GroundSetTerm M 4 := GroundSetTerm.var M
  let bound := GroundSetTerm.app (M.definable_doubleUnion unions)
    (fun _ : Fin 1 => v 2)
  let evaluated := GroundSetTerm.app (M.definable_familyEvaluation pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 1)
      (Fin.cases bound (Fin.cases (v 2) (Fin.cases (v 3) Fin.elim0))))))
  exact evaluated.definition.congr (fun _ => rfl)

noncomputable def definable_compressionCaps : GroundDefinableFunction M
    (fun env : Fin 4 → ZFSet.{u} => familyEvaluationGraph
      (env 0) (env 1) (env 1) (⋃₀ ⋃₀ env 2) (env 2)
      (constantFamilyGraph (env 0) (env 3))) := by
  let v : Fin 4 → GroundSetTerm M 4 := GroundSetTerm.var M
  let arguments := GroundSetTerm.app (M.definable_constantFamily pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 3) Fin.elim0))
  let evaluated := GroundSetTerm.app (M.definable_compressionBases pairing unions powers separation)
    (Fin.cases (v 0) (Fin.cases (v 1) (Fin.cases (v 2) (Fin.cases arguments Fin.elim0))))
  exact evaluated.definition.congr (fun _ => rfl)

noncomputable def compressionBasesFormula {n} (output I U Maps Sources : Fin n) : SetFormula n :=
  SetFormula.reindex (Fin.cases output
    (Fin.cases I (Fin.cases U (Fin.cases Maps (Fin.cases Sources Fin.elim0)))))
    (M.definable_compressionBases pairing unions powers separation).formula

noncomputable def compressionCapsFormula {n} (output I U Maps top : Fin n) : SetFormula n :=
  SetFormula.reindex (Fin.cases output
    (Fin.cases I (Fin.cases U (Fin.cases Maps (Fin.cases top Fin.elim0)))))
    (M.definable_compressionCaps pairing unions powers separation).formula

theorem realize_compressionBasesFormula {n} (output I U Maps Sources : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.compressionBasesFormula pairing unions powers separation output I U Maps Sources) env ↔
      env output = familyEvaluationGraph (env I) (env U) (env U)
        (⋃₀ ⋃₀ env Maps) (env Maps) (env Sources) := by
  let slots : Fin 4 → Fin n := Fin.cases I (Fin.cases U (Fin.cases Maps (Fin.cases Sources Fin.elim0)))
  unfold compressionBasesFormula
  rw [realize_reindex]
  change Realize M.sets (M.definable_compressionBases pairing unions powers separation).formula
    (fun j => env (extend output slots j)) ↔ _
  rw [map_extend]
  exact (M.definable_compressionBases pairing unions powers separation).correct
    (fun j => env (slots j)) (fun j => members (slots j)) (env output) (members output)

theorem realize_compressionCapsFormula {n} (output I U Maps top : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (M.compressionCapsFormula pairing unions powers separation output I U Maps top) env ↔
      env output = familyEvaluationGraph (env I) (env U) (env U)
        (⋃₀ ⋃₀ env Maps) (env Maps) (constantFamilyGraph (env I) (env top)) := by
  let slots : Fin 4 → Fin n := Fin.cases I (Fin.cases U (Fin.cases Maps (Fin.cases top Fin.elim0)))
  unfold compressionCapsFormula
  rw [realize_reindex]
  change Realize M.sets (M.definable_compressionCaps pairing unions powers separation).formula
    (fun j => env (extend output slots j)) ↔ _
  rw [map_extend]
  exact (M.definable_compressionCaps pairing unions powers separation).correct
    (fun j => env (slots j)) (fun j => members (slots j)) (env output) (members output)

end TransitiveGround

namespace GroundCompressionAlgebra
variable {M : TransitiveGround.{u}} {initial : RecursiveStateData.{u}}
variable {I Sources Reps G m one T : ZFSet.{u}}
variable (algebra : GroundCompressionAlgebra M initial I Sources Reps G m one T)
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_basesFormula (hI : I ∈ M.sets) (hSources : Sources ∈ M.sets)
    {z : ZFSet.{u}} (hz : z ∈ M.sets) :
    Realize M.sets (M.compressionBasesFormula pairing unions powers separation 0 1 2 3 4)
      (extend z (extend I (extend (algebra.union.fields 0)
        (extend algebra.maps (extend Sources Fin.elim0))))) ↔ z = algebra.bases := by
  exact M.realize_compressionBasesFormula pairing unions powers separation 0 1 2 3 4 _
    (Fin.cases hz (Fin.cases hI (Fin.cases (algebra.union.ground 0)
      (Fin.cases algebra.ground (Fin.cases hSources (fun j => Fin.elim0 j))))))

theorem realize_capsFormula (hI : I ∈ M.sets) {top z : ZFSet.{u}}
    (hTop : top ∈ M.sets) (hz : z ∈ M.sets) :
    Realize M.sets (M.compressionCapsFormula pairing unions powers separation 0 1 2 3 4)
      (extend z (extend I (extend (algebra.union.fields 0)
        (extend algebra.maps (extend top Fin.elim0))))) ↔ z = algebra.caps top := by
  exact M.realize_compressionCapsFormula pairing unions powers separation 0 1 2 3 4 _
    (Fin.cases hz (Fin.cases hI (Fin.cases (algebra.union.ground 0)
      (Fin.cases algebra.ground (Fin.cases hTop (fun j => Fin.elim0 j))))))

end GroundCompressionAlgebra
end PartitionPilot.Forcing

end

end OAI
