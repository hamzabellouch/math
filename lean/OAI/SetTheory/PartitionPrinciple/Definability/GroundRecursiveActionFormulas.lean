import OAI.SetTheory.PartitionPrinciple.Forcing.GroundRecursiveActions

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

namespace BoundedFormula

open SetFormula

def tripleProductFormula {n} (z G X Y : Fin n) : BoundedFormula n :=
  exMem G (exMem X.succ (exMem Y.succ.succ
    (orderedTripleFormula z.succ.succ.succ 2 1 0)))

theorem truth_tripleProductFormula {n} (z G X Y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tripleProductFormula z G X Y) env ↔
      env z ∈ ZFSet.prod (ZFSet.prod (env G) (env X)) (env Y) := by
  simp only [tripleProductFormula, truth_exMem, truth_orderedTripleFormula]
  change (∃ g ∈ env G, ∃ x ∈ env X, ∃ y ∈ env Y,
    env z = ZFSet.pair (ZFSet.pair g x) y) ↔ _
  constructor
  · rintro ⟨g, hg, x, hx, y, hy, equal⟩
    exact equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, hx⟩, hy⟩
  · intro member
    obtain ⟨gx, hgx, y, hy, eq⟩ := ZFSet.mem_prod.1 member
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact ⟨g, hg, x, hx, y, hy, eq⟩

def indexedTaskActionCompleteEntryFormula {n} (z G I P N T : Fin n) : BoundedFormula n :=
  .conj (tripleProductFormula z G N N) (indexedTaskActionEntryFormula z G I P T)

theorem truth_indexedTaskActionCompleteEntryFormula {n} (z G I P N T : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (indexedTaskActionCompleteEntryFormula z G I P N T) env ↔
      env z ∈ indexedTaskActionGraph (env G) (env I) (env P) (env N) (env T) := by
  simp only [indexedTaskActionCompleteEntryFormula, Truth, truth_tripleProductFormula,
    truth_indexedTaskActionEntryFormula, indexedTaskActionGraph, ZFSet.mem_sep]

def taggedActionCompleteEntryFormula {n} (z G P N A B : Fin n) : BoundedFormula n :=
  disj (.mem z A) (taggedActionEntryFormula z G P N B)

theorem truth_taggedActionCompleteEntryFormula {n} (z G P N A B : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (taggedActionCompleteEntryFormula z G P N A B) env ↔
      env z ∈ taggedActionGraph (env G) (env P) (env N) (env A) (env B) := by
  rw [taggedActionCompleteEntryFormula, truth_disj, taggedActionGraph, ZFSet.mem_union]
  apply or_congr Iff.rfl
  rw [truth_taggedActionEntryFormula, ZFSet.mem_sep]
  constructor
  · intro entry
    obtain ⟨g, hg, q, hq, t, ht, equal, branch⟩ := entry
    exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2
      ⟨hg, pair_mem_taggedExtension.2 hq⟩, pair_mem_taggedExtension.2 ht⟩, g, hg, q, hq, t, ht, equal, branch⟩
  · exact And.right

end BoundedFormula

namespace SetFormula

def indexedTaskActionGraphFormula {n} (output G I P N T : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.indexedTaskActionCompleteEntryFormula 0
    G.succ I.succ P.succ N.succ T.succ).toFormula

def taggedActionGraphFormula {n} (output G P N A B : Fin n) : SetFormula n :=
  exactSetFormula output (BoundedFormula.taggedActionCompleteEntryFormula 0
    G.succ P.succ N.succ A.succ B.succ).toFormula

def recursiveActionGraphFormula {n} (output G L I J K B N A T : Fin n) : SetFormula n :=
  ex (.conj (indexedTaskActionGraphFormula 0 G.succ I.succ J.succ K.succ T.succ)
    (ex (.conj (indexedTaskActionGraphFormula 0 G.succ.succ K.succ.succ B.succ.succ N.succ.succ 1)
      (taggedActionGraphFormula output.succ.succ G.succ.succ L.succ.succ N.succ.succ A.succ.succ 0))))

end SetFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem realize_indexedTaskActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (output G I P N T : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (indexedTaskActionGraphFormula output G I P N T) env ↔
      env output = indexedTaskActionGraph (env G) (env I) (env P) (env N) (env T) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    obtain ⟨gx, hgx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.mem_sep.1 member).1
    obtain ⟨g, hg, x, hx, rfl⟩ := ZFSet.mem_prod.1 hgx
    exact M.orderedPair_mem pairing
      (M.orderedPair_mem pairing (M.transitive (members G) hg) (M.transitive (members N) hx))
      (M.transitive (members N) hy)
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_indexedTaskActionCompleteEntryFormula 0 G.succ I.succ P.succ N.succ T.succ _

theorem realize_taggedActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (output G P N A B : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (taggedActionGraphFormula output G P N A B) env ↔
      env output = taggedActionGraph (env G) (env P) (env N) (env A) (env B) := by
  apply M.realize_exactSetFormula output _ env (members output)
  · intro z member
    rcases ZFSet.mem_union.1 member with old | fresh
    · exact M.transitive (members A) old
    · obtain ⟨_, g, hg, q, hq, t, ht, rfl, _⟩ := ZFSet.mem_sep.1 fresh
      exact M.orderedPair_mem pairing
        (M.orderedPair_mem pairing (M.transitive (members G) hg)
          (M.orderedPair_mem pairing (members P) (M.transitive (members N) hq)))
        (M.orderedPair_mem pairing (members P) (M.transitive (members N) ht))
  · intro z hz
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hz members)]
    exact BoundedFormula.truth_taggedActionCompleteEntryFormula 0 G.succ P.succ N.succ A.succ B.succ _

theorem realize_recursiveActionGraphFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {n} (output G L I J K B N A T : Fin n) (env : Fin n → ZFSet.{u})
    (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (recursiveActionGraphFormula output G L I J K B N A T) env ↔
      env output = taggedActionGraph (env G) (env L) (env N) (env A)
        (indexedTaskActionGraph (env G) (env K) (env B) (env N)
          (indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T))) := by
  rw [recursiveActionGraphFormula, realize_ex]
  constructor
  · rintro ⟨indexAction, hIndex, indexCode, rest⟩
    obtain ⟨freshAction, hFresh, freshCode, taggedCode⟩ := (realize_ex M.sets _ _).1 rest
    have firstMembers : ∀ k, extend indexAction env k ∈ M.sets := Fin.cases hIndex members
    have secondMembers : ∀ k, extend freshAction (extend indexAction env) k ∈ M.sets :=
      Fin.cases hFresh firstMembers
    have indexEq := (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ I.succ J.succ
      K.succ T.succ (extend indexAction env) firstMembers).1 indexCode
    have freshEq := (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ.succ K.succ.succ
      B.succ.succ N.succ.succ 1 _ secondMembers).1 freshCode
    have taggedEq := (M.realize_taggedActionGraphFormula pairing output.succ.succ G.succ.succ
      L.succ.succ N.succ.succ A.succ.succ 0 _ secondMembers).1 taggedCode
    change indexAction = indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T) at indexEq
    change freshAction = indexedTaskActionGraph (env G) (env K) (env B) (env N) indexAction at freshEq
    change env output = taggedActionGraph (env G) (env L) (env N) (env A) freshAction at taggedEq
    exact taggedEq.trans (congrArg (taggedActionGraph (env G) (env L) (env N) (env A))
      (freshEq.trans (congrArg (indexedTaskActionGraph (env G) (env K) (env B) (env N)) indexEq)))
  · intro equal
    let indexAction := indexedTaskActionGraph (env G) (env I) (env J) (env K) (env T)
    have hIndex := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members G) (members I) (members J) (members K) (members T)
    let freshAction := indexedTaskActionGraph (env G) (env K) (env B) (env N) indexAction
    have hFresh := M.indexedTaskActionGraph_mem pairing unions powers separation
      (members G) (members K) (members B) (members N) hIndex
    have firstMembers : ∀ k, extend indexAction env k ∈ M.sets := Fin.cases hIndex members
    have secondMembers : ∀ k, extend freshAction (extend indexAction env) k ∈ M.sets :=
      Fin.cases hFresh firstMembers
    refine ⟨indexAction, hIndex, ?_, ?_⟩
    · exact (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ I.succ J.succ
        K.succ T.succ _ firstMembers).2 rfl
    · rw [realize_ex]
      refine ⟨freshAction, hFresh, ?_, ?_⟩
      · exact (M.realize_indexedTaskActionGraphFormula pairing 0 G.succ.succ K.succ.succ
          B.succ.succ N.succ.succ 1 _ secondMembers).2 rfl
      · exact (M.realize_taggedActionGraphFormula pairing output.succ.succ G.succ.succ
          L.succ.succ N.succ.succ A.succ.succ 0 _ secondMembers).2 equal

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
