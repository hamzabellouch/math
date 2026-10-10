import OAI.SetTheory.PartitionPrinciple.Definability.ExternalWordRewriteFormulas

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def externalWordStepGraph (W append G S m one : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ f ∈ W, ∃ g ∈ W, z = ZFSet.pair f g ∧
    ExternalWordStepCode W append G S m one f g) (ZFSet.prod W W)

theorem pair_mem_externalWordStepGraph (W append G S m one f g : ZFSet.{u}) :
    ZFSet.pair f g ∈ externalWordStepGraph W append G S m one ↔
      f ∈ W ∧ g ∈ W ∧ ExternalWordStepCode W append G S m one f g := by
  rw [externalWordStepGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, f', hf, g', hg, equal, step⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hf, hg, step⟩
  · rintro ⟨hf, hg, step⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hf, hg⟩, f, hf, g, hg, rfl, step⟩

theorem externalWordStepGraph_subset (W append G S m one : ZFSet.{u}) :
    externalWordStepGraph W append G S m one ⊆ ZFSet.prod W W :=
  fun _ member => (ZFSet.mem_sep.1 member).1

theorem externalWordStepGraph_symmetric {W append G S m one f g : ZFSet.{u}}
    (entry : ZFSet.pair f g ∈ externalWordStepGraph W append G S m one) :
    ZFSet.pair g f ∈ externalWordStepGraph W append G S m one := by
  obtain ⟨hf, hg, step⟩ := (pair_mem_externalWordStepGraph _ _ _ _ _ _ _ _).1 entry
  exact (pair_mem_externalWordStepGraph _ _ _ _ _ _ _ _).2 ⟨hg, hf, step.symm⟩

namespace BoundedFormula

def externalWordStepEntryFormula {n} (z W append zero unit G S m one : Fin n) : BoundedFormula n :=
  exMem W (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
      G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0)))

theorem truth_externalWordStepEntryFormula {n} (z W append zero unit G S m one : Fin n)
    (env : Fin n → ZFSet.{u}) (zeroValue : env zero = natSetCode 0)
    (unitValue : env unit = natSetCode 1) :
    Truth (externalWordStepEntryFormula z W append zero unit G S m one) env ↔
      ∃ f ∈ env W, ∃ g ∈ env W, env z = ZFSet.pair f g ∧
        ExternalWordStepCode (env W) (env append) (env G) (env S) (env m) (env one) f g := by
  simp only [externalWordStepEntryFormula, truth_exMem, Truth, truth_orderedPairFormula]
  constructor
  · rintro ⟨f, hf, g, hg, equal, step⟩
    exact ⟨f, hf, g, hg, equal,
      (truth_externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
        G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0 (extend g (extend f env)) zeroValue unitValue).1 step⟩
  · rintro ⟨f, hf, g, hg, equal, step⟩
    exact ⟨f, hf, g, hg, equal,
      (truth_externalWordStepFormula W.succ.succ append.succ.succ zero.succ.succ unit.succ.succ
        G.succ.succ S.succ.succ m.succ.succ one.succ.succ 1 0 (extend g (extend f env)) zeroValue unitValue).2 step⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalWordStepGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {W append G S m one : ZFSet.{u}}
    (hW : W ∈ M.sets) (hAppend : append ∈ M.sets) (hG : G ∈ M.sets)
    (hS : S ∈ M.sets) (hm : m ∈ M.sets) (hOne : one ∈ M.sets) :
    externalWordStepGraph W append G S m one ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨W, hW⟩
  have hUnit : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  let params := extend W (extend append (extend (natSetCode 0) (extend (natSetCode 1)
    (extend G (extend S (extend m (extend one Fin.elim0)))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalWordStepEntryFormula 0 1 2 3 4 5 6 7 8) params
    (Fin.cases hW (Fin.cases hAppend (Fin.cases hZero (Fin.cases hUnit
      (Fin.cases hG (Fin.cases hS (Fin.cases hm (Fin.cases hOne (fun j => Fin.elim0 j)))))))))
    (M.prod_mem pairing unions powers separation hW hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalWordStepEntryFormula 0 1 2 3 4 5 6 7 8) (extend z params))
      (ZFSet.prod W W) = externalWordStepGraph W append G S m one := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, externalWordStepGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_externalWordStepEntryFormula
      0 1 2 3 4 5 6 7 8 _ rfl rfl)
  exact equal ▸ selected

noncomputable def externalWordSteps (G S m one : ZFSet.{u}) : ZFSet.{u} :=
  externalWordStepGraph (M.finiteWords (externalGeneratorAlphabet G S))
    (M.finiteWordAppendGraph (externalGeneratorAlphabet G S)) G S m one

theorem externalWordSteps_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {G S m one : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets)
    (hm : m ∈ M.sets) (hOne : one ∈ M.sets) : M.externalWordSteps G S m one ∈ M.sets := by
  have alphabet := M.externalGeneratorAlphabet_mem pairing unions powers separation hG hS
  exact M.externalWordStepGraph_mem pairing unions powers separation
    (M.finiteWords_mem pairing unions powers separation infinite alphabet)
    (M.finiteWordAppendGraph_mem pairing unions powers separation infinite alphabet) hG hS hm hOne

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
