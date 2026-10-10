import OAI.SetTheory.PartitionPrinciple.Geometry.GroundEligibleCaps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def groundEligibleTaskElementFormula {n} (z P G r μ A Labels : Fin n) : SetFormula n :=
  let old := suffixIndex n 6
  let field := prefixIndex n 6
  exBlock 6 (.conj (.mem (field 5) (old Labels))
    (.conj (BoundedFormula.literalTaskFormula (old z)
      (field 0) (field 1) (field 2) (field 3) (field 4) (field 5)).toFormula
      (BoundedFormula.eligibleTaskFormula (old P) (old G) (old r) (old μ) (old A)
        (field 0) (field 1) (field 2) (field 3) (field 4)).toFormula))

def groundEligibleTasksFormula {n} (output P G r μ A Labels : Fin n) : SetFormula n :=
  exactSetFormula output
    (groundEligibleTaskElementFormula 0 P.succ G.succ r.succ μ.succ A.succ Labels.succ)

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_groundEligibleTaskElementFormula {n} (z P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundEligibleTaskElementFormula z P G r μ A Labels) env ↔
      env z ∈ M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  rw [groundEligibleTaskElementFormula, realize_exBlock]
  constructor
  · rintro ⟨fields, fieldMembers, label, tuple, eligible⟩
    have bounds := extendMany_members 6 fields env fieldMembers members
    have code := (BoundedFormula.realize_toFormula M _ _ bounds).1 tuple
    rw [BoundedFormula.truth_literalTaskFormula] at code
    simp only [extendMany_prefix, extendMany_suffix] at code label
    have task := (BoundedFormula.realize_toFormula M _ _ bounds).1 eligible
    have taskMeaning := (BoundedFormula.truth_eligibleTaskFormula
      (suffixIndex n 6 P) (suffixIndex n 6 G) (suffixIndex n 6 r)
      (suffixIndex n 6 μ) (suffixIndex n 6 A) (prefixIndex n 6 0) (prefixIndex n 6 1)
      (prefixIndex n 6 2) (prefixIndex n 6 3) (prefixIndex n 6 4)
      (extendMany 6 fields env) meet).1 task
    simp only [extendMany_prefix, extendMany_suffix] at taskMeaning
    rw [code, M.literalTaskCode_mem_groundEligibleTasks]
    exact ⟨label, fieldMembers 2, fieldMembers 4, taskMeaning⟩
  · intro member
    obtain ⟨a, ha, c, hc, base, hBase, e, he, F, hF, label, hLabel, equal, eligible⟩ :=
      (mem_eligibleTaskSet _ _ _ _ _ _ _ _ _).1 member
    have baseGround := ((M.mem_groundRelations _ _ base).1 hBase).1
    have filterGround := ((M.mem_groundMeetFilters _ _ _ F).1 hF).1
    let fields := literalTaskField a c base e F label
    have fieldMembers : ∀ j, fields j ∈ M.sets :=
      Fin.cases (M.transitive (members P) ha) (Fin.cases (M.transitive (members P) hc)
        (Fin.cases baseGround (Fin.cases (M.transitive (members P) he)
          (Fin.cases filterGround (Fin.cases (M.transitive (members Labels) hLabel)
            (fun i => Fin.elim0 i))))))
    have bounds := extendMany_members 6 fields env fieldMembers members
    refine ⟨fields, fieldMembers, ?_, ?_, ?_⟩
    · exact hLabel
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      rw [BoundedFormula.truth_literalTaskFormula]
      exact equal
    · apply (BoundedFormula.realize_toFormula M _ _ bounds).2
      exact (BoundedFormula.truth_eligibleTaskFormula
        (suffixIndex n 6 P) (suffixIndex n 6 G) (suffixIndex n 6 r)
        (suffixIndex n 6 μ) (suffixIndex n 6 A) (prefixIndex n 6 0) (prefixIndex n 6 1)
        (prefixIndex n 6 2) (prefixIndex n 6 3) (prefixIndex n 6 4)
        (extendMany 6 fields env) meet).2 eligible

theorem realize_groundEligibleTasksFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (output P G r μ A Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets)
    (meet : MeetOrderCode (env P) (env r) (env μ)) :
    Realize M.sets (groundEligibleTasksFormula output P G r μ A Labels) env ↔
      env output = M.groundEligibleTasks (env P) (env G) (env r) (env μ) (env A) (env Labels) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.groundEligibleTasks_mem pairing unions powers separation
      (members P) (members G) (members r) (members μ) (members A) (members Labels) meet) hz)
  intro z hz
  exact M.realize_groundEligibleTaskElementFormula 0 P.succ G.succ r.succ μ.succ A.succ Labels.succ
    (extend z env) (Fin.cases hz members) meet

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
