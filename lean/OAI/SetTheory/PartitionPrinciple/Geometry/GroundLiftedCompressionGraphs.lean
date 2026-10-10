import OAI.SetTheory.PartitionPrinciple.Definability.LiftedCompressionFormulas

namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem liftedCompressionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hN : N ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A ∈ M.sets := by
  have hV := M.union_mem unions (M.union_mem unions hMaps)
  have hW := M.union_mem unions (M.union_mem unions hFs)
  let params := extend (I) (extend (J) (extend (D) (extend (L) (extend (C) (extend (N) (extend (B) (extend (Maps) (extend (Sources) (extend (Fs) (extend (Reps) (extend (G) (extend (A) (extend (ZFSet.sUnion (ZFSet.sUnion Maps)) (extend (ZFSet.sUnion (ZFSet.sUnion Fs)) (Fin.elim0)))))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15) params
    (Fin.cases hI (Fin.cases hJ (Fin.cases hD (Fin.cases hL (Fin.cases hC (Fin.cases hN (Fin.cases hB (Fin.cases hMaps (Fin.cases hSources (Fin.cases hFs (Fin.cases hReps (Fin.cases hG (Fin.cases hA (Fin.cases hV (Fin.cases hW (fun i => Fin.elim0 i))))))))))))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hI hL) hC)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15)
        (extend z params)) (ZFSet.prod (ZFSet.prod I L) C) =
      liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, liftedCompressionGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl
      (BoundedFormula.truth_liftedCompressionEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15
        (extend z params) rfl rfl)
  exact equal ▸ selected

noncomputable def groundLiftedCompressionFamily
    (I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}) : ZFSet.{u} :=
  M.indexedRelationSections I L C (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A)

theorem groundLiftedCompressionFamily_spec
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I J D L C N B Maps Sources Fs Reps G A : ZFSet.{u}}
    (hI : I ∈ M.sets) (hJ : J ∈ M.sets) (hD : D ∈ M.sets)
    (hL : L ∈ M.sets) (hC : C ∈ M.sets) (hN : N ∈ M.sets) (hB : B ∈ M.sets)
    (hMaps : Maps ∈ M.sets) (hSources : Sources ∈ M.sets) (hFs : Fs ∈ M.sets)
    (hReps : Reps ∈ M.sets) (hG : G ∈ M.sets) (hA : A ∈ M.sets) :
    M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A ∈ M.sets ∧
      FunctionGraphOn I (M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A) ∧
      ∀ i f, ZFSet.pair i f ∈ M.groundLiftedCompressionFamily I J D L C N B Maps Sources Fs Reps G A ↔
        i ∈ I ∧ f = indexedRelationSection L C
          (liftedCompressionGraph I J D L C N B Maps Sources Fs Reps G A) i := by
  have graph := M.liftedCompressionGraph_mem pairing unions powers separation
    hI hJ hD hL hC hN hB hMaps hSources hFs hReps hG hA
  obtain ⟨member, function, entries⟩ := M.indexedRelationSections_spec
    pairing unions powers separation hI hL hC graph
  exact ⟨member, ⟨_, function⟩, entries⟩

end PartitionPilot.Forcing.TransitiveGround

end

end OAI
