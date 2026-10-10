import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions

namespace OAI


namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem literalTaskBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) : literalTaskBound P R U Labels ∈ M.sets :=
  M.prod_mem pairing unions powers separation hP
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hR
        (M.prod_mem pairing unions powers separation hP
          (M.prod_mem pairing unions powers separation hU hLabels))))

theorem literalTaskFieldBound_mem
    {P R U Labels : ZFSet.{u}} (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldBound P R U Labels j ∈ M.sets :=
  Fin.cases hP (Fin.cases hP (Fin.cases hR (Fin.cases hP
    (Fin.cases hU (Fin.cases hLabels (fun i => Fin.elim0 i)))))) j

theorem literalTaskFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets) (j : Fin 6) :
    literalTaskFieldGraph I P R U Labels j ∈ M.sets := by
  let params := extend I (extend P (extend R (extend U (extend Labels Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) params
    (Fin.cases hI (Fin.cases hP (Fin.cases hR (Fin.cases hU (Fin.cases hLabels
      (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hI
      (M.literalTaskFieldBound_mem hP hR hU hLabels j))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.literalTaskFieldEntryFormula j 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod I (literalTaskFieldBound P R U Labels j)) =
      literalTaskFieldGraph I P R U Labels j := by
    apply ZFSet.ext
    intro z
    rw [literalTaskFieldGraph, ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_literalTaskFieldEntryFormula j 0 1 2 3 4 5 _)
  exact equal ▸ selected

theorem literalTaskFieldFamilies
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I P R U Labels : ZFSet.{u}} (hI : I ∈ M.sets) (hP : P ∈ M.sets) (hR : R ∈ M.sets)
    (hU : U ∈ M.sets) (hLabels : Labels ∈ M.sets)
    (subset : I ⊆ literalTaskBound P R U Labels) :
    ∀ j : Fin 6, literalTaskFieldGraph I P R U Labels j ∈ M.sets ∧
      ZFSet.IsFunc I (literalTaskFieldBound P R U Labels j) (literalTaskFieldGraph I P R U Labels j) :=
  fun j => ⟨M.literalTaskFieldGraph_mem pairing unions powers separation hI hP hR hU hLabels j,
    literalTaskFieldGraph_function subset j⟩

theorem constantFamilyGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I x : ZFSet.{u}} (hI : I ∈ M.sets) (hx : x ∈ M.sets) : constantFamilyGraph I x ∈ M.sets := by
  have single : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.prod_mem pairing unions powers separation hI single

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u
namespace SetFormula

def literalTaskFieldSetFormula {n} (j : Fin 6) (output I P R U Labels : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.literalTaskFieldEntryFormula j 0 I.succ P.succ R.succ U.succ Labels.succ).toFormula

def constantFamilySetFormula {n} (output I x : Fin n) : SetFormula n :=
  exactSetFormula output
    (BoundedFormula.exMem I.succ (BoundedFormula.orderedPairFormula 1 0 x.succ.succ)).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_literalTaskFieldSetFormula {n} (j : Fin 6) (output I P R U Labels : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (literalTaskFieldSetFormula j output I P R U Labels) env ↔
      env output = literalTaskFieldGraph (env I) (env P) (env R) (env U) (env Labels) j := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.literalTaskFieldGraph_mem pairing unions powers separation
      (members I) (members P) (members R) (members U) (members Labels) j) hz)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_literalTaskFieldEntryFormula]
  exact (mem_literalTaskFieldGraph _ _ _ _ _ _ j).symm

theorem realize_constantFamilySetFormula {n} (output I x : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (constantFamilySetFormula output I x) env ↔
      env output = constantFamilyGraph (env I) (env x) := by
  apply M.realize_exactSetFormula output _ env (members output)
    (fun z hz => M.transitive (M.constantFamilyGraph_mem pairing unions powers separation
      (members I) (members x)) hz)
  intro z hz
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members),
    BoundedFormula.truth_exMem]
  simp only [BoundedFormula.truth_orderedPairFormula]
  change (∃ i ∈ env I, z = ZFSet.pair i (env x)) ↔ z ∈ constantFamilyGraph (env I) (env x)
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ZFSet.pair_mem_prod.2 ⟨hi, ZFSet.mem_singleton.2 rfl⟩
  · intro entry
    obtain ⟨i, hi, y, hy, equal⟩ := ZFSet.mem_prod.1 entry
    have same := ZFSet.mem_singleton.1 hy
    exact ⟨i, hi, same ▸ equal⟩

noncomputable def definable_literalTaskField (j : Fin 6) : GroundDefinableFunction M
    (fun env : Fin 5 → ZFSet.{u} => literalTaskFieldGraph (env 0) (env 1) (env 2) (env 3) (env 4) j) where
  formula := literalTaskFieldSetFormula j 0 1 2 3 4 5
  closed := fun _ members => M.literalTaskFieldGraph_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4) j
  correct := fun env members z hz => M.realize_literalTaskFieldSetFormula pairing unions powers separation
    j 0 1 2 3 4 5 (extend z env) (Fin.cases hz members)

noncomputable def definable_constantFamily : GroundDefinableFunction M
    (fun env : Fin 2 → ZFSet.{u} => constantFamilyGraph (env 0) (env 1)) where
  formula := constantFamilySetFormula 0 1 2
  closed := fun _ members => M.constantFamilyGraph_mem pairing unions powers separation (members 0) (members 1)
  correct := fun env members z hz => M.realize_constantFamilySetFormula pairing unions powers separation
    0 1 2 (extend z env) (Fin.cases hz members)

end TransitiveGround
end PartitionPilot.Forcing

end OAI
