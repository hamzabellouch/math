import OAI.SetTheory.PartitionPrinciple.Definability.ParentSupportCodes

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def sizeWitnessRelation (R W N : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ p ∈ R, ∃ f ∈ W, z = ZFSet.pair p f ∧ InjectionCode p N f) (ZFSet.prod R W)

theorem pair_mem_sizeWitnessRelation (R W N p f : ZFSet.{u}) :
    ZFSet.pair p f ∈ sizeWitnessRelation R W N ↔ p ∈ R ∧ f ∈ W ∧ InjectionCode p N f := by
  rw [sizeWitnessRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, q, hq, g, hg, eq, code⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨hq, hg, code⟩
  · rintro ⟨hp, hf, code⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hp, hf⟩, p, hp, f, hf, rfl, code⟩

namespace BoundedFormula

open SetFormula

def sizeWitnessEntryFormula {k} (z r w n : Fin k) : BoundedFormula k :=
  exMem r (exMem w.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (injectionFormula 1 n.succ.succ 0)))

theorem truth_sizeWitnessEntryFormula {k} (z r w n : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (sizeWitnessEntryFormula z r w n) env ↔
      ∃ p ∈ env r, ∃ f ∈ env w, env z = ZFSet.pair p f ∧ InjectionCode p (env n) f := by
  simp only [sizeWitnessEntryFormula, truth_exMem, Truth, truth_orderedPairFormula, truth_injectionFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem sizeWitnessRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R W N : ZFSet.{u}} (hR : R ∈ M.sets) (hW : W ∈ M.sets) (hN : N ∈ M.sets) :
    sizeWitnessRelation R W N ∈ M.sets := by
  let params := extend R (extend W (extend N Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.sizeWitnessEntryFormula 0 1 2 3)
    params (Fin.cases hR (Fin.cases hW (Fin.cases hN (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hR hW)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.sizeWitnessEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod R W) = sizeWitnessRelation R W N := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, sizeWitnessRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_sizeWitnessEntryFormula 0 1 2 3 _)
  exact eq ▸ selected

theorem uniform_size_witnesses
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B N : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p N) :
    ∃ F ∈ M.sets, ZFSet.IsFunc R (M.groundRelations B N) F ∧
      ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f := by
  let W := M.groundRelations B N
  have hW := M.groundRelations_mem pairing unions powers separation hB hN
  have hT := M.sizeWitnessRelation_mem pairing unions powers separation hR hW hN
  have total (p : ZFSet.{u}) (hp : p ∈ R) : ∃ f ∈ W, ZFSet.pair p f ∈ sizeWitnessRelation R W N := by
    obtain ⟨f, hf, code⟩ := small p hp
    have bound : f ⊆ ZFSet.prod B N := by
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (code.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨subsets p hp hx, hy⟩
    have hfW := (M.mem_groundRelations B N f).2 ⟨hf, bound⟩
    exact ⟨f, hfW, (pair_mem_sizeWitnessRelation R W N p f).2 ⟨hp, hfW, code⟩⟩
  obtain ⟨F, hF, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice hR hW hT total
  exact ⟨F, hF, func, fun p f rel => ((pair_mem_sizeWitnessRelation R W N p f).1 (selected rel)).2.2⟩

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
