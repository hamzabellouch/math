import OAI.SetTheory.PartitionPrinciple.Geometry.GroundLiftedCompressionGraphs

namespace OAI

namespace PartitionPilot.Forcing

universe u

namespace SetFormula

def sectionFamilyEntryFormula {n} (z I B C R : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 I.succ) (ex
    (.conj (BoundedFormula.orderedPairFormula z.succ.succ 1 0).toFormula
      (BoundedFormula.indexedRelationSectionFormula 0 1 B.succ.succ C.succ.succ R.succ.succ).toFormula)))

def sectionFamilyFormula {n} (family I B C R : Fin n) : SetFormula n :=
  exactSetFormula family (sectionFamilyEntryFormula 0 I.succ B.succ C.succ R.succ)

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_sectionFamilyEntryFormula {n} (z I B C R : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sectionFamilyEntryFormula z I B C R) env ↔
      env z ∈ M.indexedRelationSections (env I) (env B) (env C) (env R) := by
  rw [sectionFamilyEntryFormula, realize_ex]
  constructor
  · rintro ⟨i, hiM, hi, rest⟩
    obtain ⟨f, hfM, pair, sectionCode⟩ := (realize_ex M.sets _ _).1 rest
    have extended : ∀ j, extend f (extend i env) j ∈ M.sets := Fin.cases hfM (Fin.cases hiM members)
    have pairEq := (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 pair)
    have sectionEq := (BoundedFormula.truth_indexedRelationSectionFormula 0 1
      B.succ.succ C.succ.succ R.succ.succ _).1
      ((BoundedFormula.realize_toFormula M _ _ extended).1 sectionCode)
    change env z = ZFSet.pair i f at pairEq
    change f = indexedRelationSection (env B) (env C) (env R) i at sectionEq
    rw [pairEq]
    exact (M.pair_mem_indexedRelationSections _ _ _ _ _ _).2
      ⟨hi, (M.mem_groundRelations _ _ _).2 ⟨hfM, sectionEq.symm ▸ indexedRelationSection_subset _ _ _ _⟩,
        sectionEq⟩
  · intro member
    obtain ⟨_, i, hi, f, hf, pairEq, sectionEq⟩ := ZFSet.mem_sep.1 member
    have hiM := M.transitive (members I) hi
    have hfM := ((M.mem_groundRelations _ _ _).1 hf).1
    refine ⟨i, hiM, hi, ?_⟩
    rw [realize_ex]
    refine ⟨f, hfM, ?_, ?_⟩
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hfM (Fin.cases hiM members))).2
      exact (BoundedFormula.truth_orderedPairFormula z.succ.succ 1 0 _).2 pairEq
    · apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hfM (Fin.cases hiM members))).2
      exact (BoundedFormula.truth_indexedRelationSectionFormula 0 1
        B.succ.succ C.succ.succ R.succ.succ _).2 sectionEq

theorem realize_sectionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (family I B C R : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets (sectionFamilyFormula family I B C R) env ↔
      env family = M.indexedRelationSections (env I) (env B) (env C) (env R) := by
  apply M.realize_exactSetFormula family _ env (members family)
  · intro z member
    obtain ⟨_, i, hi, f, hf, pairEq, _⟩ := ZFSet.mem_sep.1 member
    exact pairEq.symm ▸ M.orderedPair_mem pairing (M.transitive (members I) hi)
      ((M.mem_groundRelations _ _ _).1 hf).1
  · intro z hz
    exact M.realize_sectionFamilyEntryFormula 0 I.succ B.succ C.succ R.succ
      (extend z env) (Fin.cases hz members)

end TransitiveGround

namespace BoundedFormula

theorem truth_liftedCompressionEntryFormula_mem {n}
    (z i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Truth (liftedCompressionEntryFormula z i j d l c ns b maps sources fs reps g action v w) env ↔
      env z ∈ liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  rw [truth_liftedCompressionEntryFormula _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mapsBound filterBound,
    liftedCompressionGraph, ZFSet.mem_sep]
  constructor
  · intro entry
    obtain ⟨task, hi, x, hx, y, hy, equal, branch⟩ := entry
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hi, hx⟩, hy⟩, task, hi, x, hx, y, hy, equal, branch⟩
  · exact And.right

end BoundedFormula

namespace SetFormula

def liftedCompressionGraphFormula {n}
    (output i j d l c ns b maps sources fs reps g action v w : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.liftedCompressionEntryFormula 0
    i.succ j.succ d.succ l.succ c.succ ns.succ b.succ maps.succ sources.succ
    fs.succ reps.succ g.succ action.succ v.succ w.succ).toFormula

def liftedCompressionFamilyFormula {n}
    (family i j d l c ns b maps sources fs reps g action v w : Fin n) : SetFormula n :=
  ex (.conj (liftedCompressionGraphFormula 0 i.succ j.succ d.succ l.succ c.succ
    ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ v.succ w.succ)
    (sectionFamilyFormula family.succ i.succ l.succ c.succ 0))

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_liftedCompressionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0) {n}
    (output i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets)
    (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (liftedCompressionGraphFormula output i j d l c ns b maps sources
      fs reps g action v w) env ↔
      env output = liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    obtain ⟨_, task, hi, x, hx, y, hy, rfl, _⟩ := ZFSet.mem_sep.1 member
    exact M.orderedPair_mem pairing
      (M.orderedPair_mem pairing (M.transitive (members i) hi) (M.transitive (members l) hx))
      (M.transitive (members c) hy)
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_liftedCompressionEntryFormula_mem 0 i.succ j.succ d.succ
      l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
      v.succ w.succ (extend z env) mapsBound filterBound

theorem realize_liftedCompressionFamilyFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) {n}
    (family i j d l c ns b maps sources fs reps g action v w : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets)
    (mapsBound : env v = ZFSet.sUnion (ZFSet.sUnion (env maps)))
    (filterBound : env w = ZFSet.sUnion (ZFSet.sUnion (env fs))) :
    Realize M.sets (liftedCompressionFamilyFormula family i j d l c ns b maps sources
      fs reps g action v w) env ↔
      env family = M.groundLiftedCompressionFamily (env i) (env j) (env d) (env l) (env c)
        (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) := by
  rw [liftedCompressionFamilyFormula, realize_ex]
  constructor
  · rintro ⟨graph, hgraph, graphCode, familyCode⟩
    have extended : ∀ k, extend graph env k ∈ M.sets := Fin.cases hgraph members
    have graphEq := (M.realize_liftedCompressionGraphFormula pairing 0 i.succ j.succ d.succ
      l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
      v.succ w.succ (extend graph env) extended mapsBound filterBound).1 graphCode
    have familyEq := (M.realize_sectionFamilyFormula pairing family.succ i.succ l.succ c.succ 0
      (extend graph env) extended).1 familyCode
    change graph = liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
      (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action) at graphEq
    change env family = M.indexedRelationSections (env i) (env l) (env c) graph at familyEq
    simpa only [groundLiftedCompressionFamily, graphEq] using familyEq
  · intro equal
    let graph := liftedCompressionGraph (env i) (env j) (env d) (env l) (env c)
      (env ns) (env b) (env maps) (env sources) (env fs) (env reps) (env g) (env action)
    have hgraph := M.liftedCompressionGraph_mem pairing unions powers separation
      (members i) (members j) (members d) (members l) (members c) (members ns) (members b)
      (members maps) (members sources) (members fs) (members reps) (members g) (members action)
    refine ⟨graph, hgraph, ?_, ?_⟩
    · apply (M.realize_liftedCompressionGraphFormula pairing 0 i.succ j.succ d.succ
        l.succ c.succ ns.succ b.succ maps.succ sources.succ fs.succ reps.succ g.succ action.succ
        v.succ w.succ (extend graph env) (Fin.cases hgraph members) mapsBound filterBound).2
      rfl
    · apply (M.realize_sectionFamilyFormula pairing family.succ i.succ l.succ c.succ 0
        (extend graph env) (Fin.cases hgraph members)).2
      exact equal

end TransitiveGround

end PartitionPilot.Forcing

end OAI
