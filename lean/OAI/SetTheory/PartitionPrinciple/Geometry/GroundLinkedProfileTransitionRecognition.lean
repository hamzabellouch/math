import OAI.SetTheory.PartitionPrinciple.Definability.LinkedProfileTransitionRawCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def linkedProfilePreservingTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n) : SetFormula n :=
  let old := suffixIndex n 53
  let fresh := prefixIndex n 53
  exBlock 53 (linkedProfilePreservingTransitionRawFormula (old K) (old Labels) (old C) (old D) (old rD) (old N)
    (old sourceCode) (old targetCode) (old z) (fresh 48) (fresh 49) (fresh 50) (fresh 51) (fresh 52)
    (fun j => fresh (j.castAdd 29)) (fun j => fresh (Fin.natAdd 24 (j.castAdd 5))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable (collection : CollectionSchema M.sets)
include pairing unions powers separation collection

theorem realize_linkedProfilePreservingTransitionFormula_raw {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      ∃ fields : Fin 53 → ZFSet.{u}, (∀ j, fields j ∈ M.sets) ∧
        LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) (env N)
          (env sourceCode) (env targetCode) (env z) (fields 48) (fields 49) (fields 50) (fields 51) (fields 52)
          (fun j => fields (j.castAdd 29)) (fun j => fields (Fin.natAdd 24 (j.castAdd 5))) := by
  rw [linkedProfilePreservingTransitionFormula, realize_exBlock]
  have actual (fields : Fin 53 → ZFSet.{u}) (ground : ∀ j, fields j ∈ M.sets) :=
    M.realize_linkedProfilePreservingTransitionRawFormula pairing unions powers separation collection
      (suffixIndex n 53 K) (suffixIndex n 53 Labels) (suffixIndex n 53 C) (suffixIndex n 53 D)
      (suffixIndex n 53 rD) (suffixIndex n 53 N) (suffixIndex n 53 sourceCode)
      (suffixIndex n 53 targetCode) (suffixIndex n 53 z)
      (prefixIndex n 53 48) (prefixIndex n 53 49) (prefixIndex n 53 50) (prefixIndex n 53 51) (prefixIndex n 53 52)
      (fun j => prefixIndex n 53 (j.castAdd 29)) (fun j => prefixIndex n 53 (Fin.natAdd 24 (j.castAdd 5)))
      (extendMany 53 fields env) (extendMany_members 53 fields env ground members)
      (by simpa only [extendMany_suffix] using omega)
      (by simpa only [extendMany_suffix] using ordinal)
  simp only [extendMany_prefix, extendMany_suffix] at actual
  constructor
  · rintro ⟨fields, ground, recognized⟩
    exact ⟨fields, ground, (actual fields ground).1 recognized⟩
  · rintro ⟨fields, ground, raw⟩
    exact ⟨fields, ground, (actual fields ground).2 raw⟩

theorem realize_linkedProfilePreservingTransitionFormula {n} (K Labels C D rD N sourceCode targetCode z : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets)
    (omega : env N = ZFSet.omega) (ordinal : ordinalSetProperty (env K)) :
    Realize M.sets (linkedProfilePreservingTransitionFormula K Labels C D rD N sourceCode targetCode z) env ↔
      LinkedProfilePreservingTransitionCode M (env K) (env Labels) (env C) (env D) (env rD)
        (env sourceCode) (env targetCode) (env z) := by
  rw [M.realize_linkedProfilePreservingTransitionFormula_raw pairing unions powers separation collection
    K Labels C D rD N sourceCode targetCode z env members omega ordinal]
  constructor
  · rintro ⟨fields, ground, raw⟩
    exact raw.exists_transition pairing unions powers separation
      (fun j => ground (j.castAdd 29)) (fun j => ground (Fin.natAdd 24 (j.castAdd 5)))
      (ground 48) (ground 49) (members C) (members D) (members rD) omega
  · rintro ⟨source, target, sourceEq, targetEq, transition, codeEq, coverage, preserved⟩
    let extra : Fin 5 → ZFSet.{u} := Fin.cases transition.map.points (Fin.cases transition.map.actors
      (Fin.cases source.main.birth (Fin.cases target.main.birth
        (fun _ => M.groundPower source.main.stage.carrier))))
    let fields : Fin 53 → ZFSet.{u} := Fin.addCases (m := 24) (n := 29) source.rawFields (Fin.addCases (m := 24) (n := 5) target.rawFields extra)
    have extraGround : ∀ j, extra j ∈ M.sets :=
      Fin.cases transition.map.points_ground (Fin.cases transition.map.actors_ground
        (Fin.cases source.main.birth_ground (Fin.cases target.main.birth_ground
          (fun _ => M.groundPower_mem powers source.main.stage.carrier_ground))))
    have grounded : ∀ j, fields j ∈ M.sets := by
      intro j
      refine Fin.addCases (m := 24) (n := 29) ?_ ?_ j
      · intro k
        simpa only [fields, Fin.addCases_left] using source.rawFields_ground pairing k
      · intro k
        refine Fin.addCases (m := 24) (n := 5) ?_ ?_ k
        · intro a
          simpa only [fields, Fin.addCases_right, Fin.addCases_left] using target.rawFields_ground pairing a
        · intro a
          simpa only [fields, Fin.addCases_right] using extraGround a
    refine ⟨fields, grounded, ?_⟩
    have smap : (fun j : Fin 24 => fields (j.castAdd 29)) = source.rawFields := by
      funext j
      simp only [fields, Fin.addCases_left]
    have tmap : (fun j : Fin 24 => fields (Fin.natAdd 24 (j.castAdd 5))) = target.rawFields := by
      funext j
      simp only [fields, Fin.addCases_right, Fin.addCases_left]
    rw [smap, tmap, omega]
    change LinkedProfilePreservingTransitionRawCode M (env K) (env Labels) (env C) (env D) (env rD) ZFSet.omega
      (env sourceCode) (env targetCode) (env z) transition.map.points transition.map.actors
      (source.main.birth) (target.main.birth)
      (M.groundPower source.main.stage.carrier) source.rawFields target.rawFields
    rw [← sourceEq, ← targetEq, ← codeEq]
    exact source.profileTransition_rawFields target transition coverage preserved

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
