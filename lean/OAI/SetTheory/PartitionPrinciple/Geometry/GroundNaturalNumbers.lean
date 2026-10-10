import OAI.SetTheory.PartitionPrinciple.Forcing.GroundMixtureNames

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem omega_subset_inductive (I : ZFSet.{u}) (empty : (∅ : ZFSet.{u}) ∈ I)
    (successor : ∀ x ∈ I, insert x x ∈ I) : ZFSet.omega ⊆ I := by
  intro x hx
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode x).1 hx
  clear hx
  induction n with
  | zero => exact empty
  | succ n ih => exact successor (natSetCode n) ih

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem omega_mem (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) : ZFSet.omega ∈ M.sets := by
  obtain ⟨I, hI, empty, successor⟩ := M.infinity_witness infinite
  have subset := omega_subset_inductive I empty successor
  have selected := M.separation_mem separation (BoundedFormula.naturalFormula 0).toFormula
    Fin.elim0 (fun i => Fin.elim0 i) hI
  have eq : ZFSet.sep (fun x => Realize M.sets (BoundedFormula.naturalFormula 0).toFormula
      (extend x Fin.elim0)) I = ZFSet.omega := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hx, rel⟩
      exact (BoundedFormula.realize_naturalFormula M 0 (extend x Fin.elim0)
        (Fin.cases (M.transitive hI hx) (fun i => Fin.elim0 i))).1 rel
    · intro hx
      have hxI := subset hx
      exact ⟨hxI, (BoundedFormula.realize_naturalFormula M 0 (extend x Fin.elim0)
        (Fin.cases (M.transitive hI hxI) (fun i => Fin.elim0 i))).2 hx⟩
  exact eq ▸ selected

theorem natSetCode_mem (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0) (n : Nat) : natSetCode n ∈ M.sets :=
  M.transitive (M.omega_mem separation infinite) (natSetCode_mem_omega n)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
