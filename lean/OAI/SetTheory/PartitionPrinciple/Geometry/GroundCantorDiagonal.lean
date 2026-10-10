import OAI.SetTheory.PartitionPrinciple.Definability.GroundBelowFunctionGraphs

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula

def injectionDiagonalFormula {n} (x p f : Fin n) : BoundedFormula n :=
  exMem p (.conj (pairMembershipFormula 0 x.succ f.succ) (.neg (.mem x.succ 0)))

theorem truth_injectionDiagonalFormula {n} (x p f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (injectionDiagonalFormula x p f) env ↔
      ∃ X ∈ env p, ZFSet.pair X (env x) ∈ env f ∧ env x ∉ X := by
  simp only [injectionDiagonalFormula, truth_exMem, Truth, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def injectionDiagonal (A f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ X ∈ M.groundPower A, ZFSet.pair X x ∈ f ∧ x ∉ X) A

theorem mem_injectionDiagonal (A f x : ZFSet.{u}) :
    x ∈ M.injectionDiagonal A f ↔
      x ∈ A ∧ ∃ X ∈ M.groundPower A, ZFSet.pair X x ∈ f ∧ x ∉ X := ZFSet.mem_sep

theorem injectionDiagonal_mem
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    M.injectionDiagonal A f ∈ M.sets := by
  let params := extend (M.groundPower A) (extend f Fin.elim0)
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases (M.groundPower_mem powers hA) (Fin.cases hf (fun i => Fin.elim0 i))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.injectionDiagonalFormula 0 1 2) params members hA
  have eq : ZFSet.sep (fun x => BoundedFormula.Truth
      (BoundedFormula.injectionDiagonalFormula 0 1 2) (extend x params)) A =
      M.injectionDiagonal A f := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep, M.mem_injectionDiagonal, BoundedFormula.truth_injectionDiagonalFormula]
    rfl
  exact eq ▸ selected

theorem groundPower_not_embeddable_self
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : ¬ M.groundEmbeddable (M.groundPower A) A := by
  classical
  rintro ⟨f, hf, code⟩
  let D := M.injectionDiagonal A f
  have hD : D ∈ M.groundPower A := (M.mem_groundPower A D).2
    ⟨M.injectionDiagonal_mem powers separation hA hf,
      fun _ hx => (M.mem_injectionDiagonal A f _).1 hx |>.1⟩
  obtain ⟨y, entry, _⟩ := code.function.2 D hD
  have hy : y ∈ A := (ZFSet.pair_mem_prod.1 (code.function.1 entry)).2
  have outside : y ∉ D := by
    intro inside
    obtain ⟨_, X, _, image, missing⟩ := (M.mem_injectionDiagonal A f y).1 inside
    have same : X = D := code.injective X D y image entry
    exact missing (same.symm ▸ inside)
  exact outside ((M.mem_injectionDiagonal A f y).2 ⟨hy, D, hD, entry, outside⟩)

end TransitiveGround
end PartitionPilot.Forcing

end

end OAI
