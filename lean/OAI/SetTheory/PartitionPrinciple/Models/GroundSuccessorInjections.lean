import OAI.SetTheory.PartitionPrinciple.Geometry.GroundNaturalNumbers

namespace OAI


namespace PartitionPilot.Forcing

universe u

theorem setSuccessor_injective : Function.Injective (fun x : ZFSet.{u} => insert x x) := by
  intro x y eq
  change insert x x = insert y y at eq
  have xy : x = y ∨ x ∈ y := ZFSet.mem_insert_iff.1 (eq ▸ ZFSet.mem_insert x x)
  have yx : y = x ∨ y ∈ x := ZFSet.mem_insert_iff.1 (eq.symm ▸ ZFSet.mem_insert y y)
  rcases xy with eq | xy
  · exact eq
  · rcases yx with eq | yx
    · exact eq.symm
    · exact False.elim (ZFSet.mem_asymm xy yx)

theorem setSuccessor_ne_empty (x : ZFSet.{u}) : insert x x ≠ (∅ : ZFSet.{u}) := by
  intro eq
  exact ZFSet.notMem_empty x (eq ▸ ZFSet.mem_insert x x)

noncomputable def shiftedInjectionGraph (D f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ D, ∃ n ∈ ZFSet.omega,
    z = ZFSet.pair x (insert n n) ∧ ZFSet.pair x n ∈ f) (ZFSet.prod D ZFSet.omega)

theorem mem_shiftedInjectionGraph (D f z : ZFSet.{u}) :
    z ∈ shiftedInjectionGraph D f ↔ ∃ x ∈ D, ∃ n ∈ ZFSet.omega,
      z = ZFSet.pair x (insert n n) ∧ ZFSet.pair x n ∈ f := by
  rw [shiftedInjectionGraph, ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro h
    obtain ⟨x, hx, n, hn, eq, rel⟩ := h
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.omega_succ hn⟩,
      x, hx, n, hn, eq, rel⟩

theorem pair_mem_shiftedInjectionGraph (D f x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ shiftedInjectionGraph D f ↔
      x ∈ D ∧ ∃ n ∈ ZFSet.omega, y = insert n n ∧ ZFSet.pair x n ∈ f := by
  rw [mem_shiftedInjectionGraph]
  constructor
  · rintro ⟨a, ha, n, hn, eq, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, n, hn, rfl, rel⟩
  · rintro ⟨hx, n, hn, rfl, rel⟩
    exact ⟨x, hx, n, hn, rfl, rel⟩

theorem shiftedInjectionGraph_no_zero (D f x : ZFSet.{u}) :
    ZFSet.pair x ∅ ∉ shiftedInjectionGraph D f := by
  intro rel
  obtain ⟨_, n, _, eq, _⟩ := (pair_mem_shiftedInjectionGraph D f x ∅).1 rel
  exact setSuccessor_ne_empty n eq.symm

namespace InjectionCode

theorem shift {D f : ZFSet.{u}} (h : InjectionCode D ZFSet.omega f) :
    InjectionCode D ZFSet.omega (shiftedInjectionGraph D f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨n, rel, unique⟩ := h.function.2 x hx
    have hn := (ZFSet.pair_mem_prod.1 (h.function.1 rel)).2
    refine ⟨insert n n, (pair_mem_shiftedInjectionGraph D f x _).2 ⟨hx, n, hn, rfl, rel⟩, ?_⟩
    intro y hy
    obtain ⟨_, m, _, eq, hm⟩ := (pair_mem_shiftedInjectionGraph D f x y).1 hy
    rw [eq, unique m hm]
  · intro x y z hx hy
    obtain ⟨_, n, _, zn, xn⟩ := (pair_mem_shiftedInjectionGraph D f x z).1 hx
    obtain ⟨_, m, _, zm, ym⟩ := (pair_mem_shiftedInjectionGraph D f y z).1 hy
    have eq := setSuccessor_injective (zn.symm.trans zm)
    exact h.injective x y m (eq ▸ xn) ym

end InjectionCode

noncomputable def adjoinInjectionGraph (D f a : ZFSet.{u}) : ZFSet.{u} :=
  insert (ZFSet.pair a ∅) (shiftedInjectionGraph D f)

theorem pair_mem_adjoinInjectionGraph (D f a x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ adjoinInjectionGraph D f a ↔
      (x = a ∧ y = ∅) ∨ ZFSet.pair x y ∈ shiftedInjectionGraph D f := by
  rw [adjoinInjectionGraph, ZFSet.mem_insert_iff, ZFSet.pair_inj]

namespace InjectionCode

theorem adjoin_fresh {D f a : ZFSet.{u}} (h : InjectionCode D ZFSet.omega f) (fresh : a ∉ D) :
    InjectionCode (insert a D) ZFSet.omega (adjoinInjectionGraph D f a) := by
  have shifted := h.shift
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    rcases ZFSet.mem_insert_iff.1 hz with rfl | hz
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert a D, ZFSet.omega_zero⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (shifted.function.1 hz)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_insert_of_mem a hx, hy⟩
  · intro x hx
    rcases ZFSet.mem_insert_iff.1 hx with eq | hx
    · subst x
      refine ⟨∅, (pair_mem_adjoinInjectionGraph D f a a ∅).2 (Or.inl ⟨rfl, rfl⟩), ?_⟩
      intro y hy
      rcases (pair_mem_adjoinInjectionGraph D f a a y).1 hy with eq | rel
      · exact eq.2
      · exact False.elim (fresh ((pair_mem_shiftedInjectionGraph D f a y).1 rel).1)
    · obtain ⟨y, rel, unique⟩ := shifted.function.2 x hx
      refine ⟨y, (pair_mem_adjoinInjectionGraph D f a x y).2 (Or.inr rel), ?_⟩
      intro z hz
      rcases (pair_mem_adjoinInjectionGraph D f a x z).1 hz with eq | rel
      · exact False.elim (fresh (eq.1 ▸ hx))
      · exact unique z rel
  · intro x y z hx hy
    rcases (pair_mem_adjoinInjectionGraph D f a x z).1 hx with eqx | shiftx
    · rcases (pair_mem_adjoinInjectionGraph D f a y z).1 hy with eqy | shifty
      · exact eqx.1.trans eqy.1.symm
      · rw [eqx.2] at shifty
        exact False.elim (shiftedInjectionGraph_no_zero D f y shifty)
    · rcases (pair_mem_adjoinInjectionGraph D f a y z).1 hy with eqy | shifty
      · rw [eqy.2] at shiftx
        exact False.elim (shiftedInjectionGraph_no_zero D f x shiftx)
      · exact shifted.injective x y z shiftx shifty

end InjectionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def shiftedInjectionEntryFormula {n} (z d o f : Fin n) : BoundedFormula n :=
  exMem d (exMem o.succ (exMem o.succ.succ
    (.conj (successorFormula 0 1)
      (.conj (orderedPairFormula z.succ.succ.succ 2 0)
        (pairMembershipFormula 2 1 f.succ.succ.succ)))))

theorem truth_shiftedInjectionEntryFormula {n} (z d o f : Fin n)
    (env : Fin n → ZFSet.{u}) (omega : env o = ZFSet.omega) :
    Truth (shiftedInjectionEntryFormula z d o f) env ↔
      ∃ x ∈ env d, ∃ m ∈ ZFSet.omega,
        env z = ZFSet.pair x (insert m m) ∧ ZFSet.pair x m ∈ env f := by
  simp only [shiftedInjectionEntryFormula, truth_exMem, Truth,
    truth_successorFormula, truth_orderedPairFormula, truth_pairMembershipFormula]
  change (∃ x ∈ env d, ∃ m ∈ env o, ∃ k ∈ env o,
    k = insert m m ∧ env z = ZFSet.pair x k ∧ ZFSet.pair x m ∈ env f) ↔ _
  rw [omega]
  constructor
  · rintro ⟨x, hx, m, hm, k, _, rfl, eq, rel⟩
    exact ⟨x, hx, m, hm, eq, rel⟩
  · rintro ⟨x, hx, m, hm, eq, rel⟩
    exact ⟨x, hx, m, hm, insert m m, ZFSet.omega_succ hm, rfl, eq, rel⟩

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem insert_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {a D : ZFSet.{u}} (ha : a ∈ M.sets) (hD : D ∈ M.sets) : insert a D ∈ M.sets := by
  have single : ({a} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing ha ha
  have joined := M.binary_union_mem pairing unions single hD
  have eq : ({a} : ZFSet.{u}) ∪ D = insert a D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_union, ZFSet.mem_singleton, ZFSet.mem_insert_iff]
  exact eq ▸ joined

theorem shiftedInjectionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D f : ZFSet.{u}} (hD : D ∈ M.sets) (hf : f ∈ M.sets) :
    shiftedInjectionGraph D f ∈ M.sets := by
  have hO := M.omega_mem separation infinite
  have bound := M.prod_mem pairing unions powers separation hD hO
  let params := extend D (extend ZFSet.omega (extend f Fin.elim0))
  have members : ∀ i, params i ∈ M.sets :=
    Fin.cases hD (Fin.cases hO (Fin.cases hf (fun i => Fin.elim0 i)))
  have selected := M.separation_mem separation
    (BoundedFormula.shiftedInjectionEntryFormula 0 1 2 3).toFormula params members bound
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.shiftedInjectionEntryFormula 0 1 2 3).toFormula (extend z params))
      (ZFSet.prod D ZFSet.omega) = shiftedInjectionGraph D f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, shiftedInjectionGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact (BoundedFormula.realize_toFormula M _ _
      (Fin.cases (M.transitive bound hz) members)).trans
        (BoundedFormula.truth_shiftedInjectionEntryFormula 0 1 2 3 (extend z params) rfl)
  exact eq ▸ selected

theorem adjoinInjectionGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D f a : ZFSet.{u}} (hD : D ∈ M.sets) (hf : f ∈ M.sets) (ha : a ∈ M.sets) :
    adjoinInjectionGraph D f a ∈ M.sets :=
  M.insert_mem pairing unions
    (M.orderedPair_mem pairing ha (M.empty_mem ⟨a, ha⟩))
    (M.shiftedInjectionGraph_mem pairing unions powers separation infinite hD hf)

theorem groundEmbeddable_insert
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {D a : ZFSet.{u}} (hD : D ∈ M.sets) (ha : a ∈ M.sets)
    (small : M.groundEmbeddable D ZFSet.omega) :
    M.groundEmbeddable (insert a D) ZFSet.omega := by
  classical
  by_cases member : a ∈ D
  · have eq : insert a D = D := by
      apply ZFSet.ext
      intro z
      rw [ZFSet.mem_insert_iff]
      exact ⟨fun h => h.elim (fun eq => eq.symm ▸ member) id, Or.inr⟩
    exact eq.symm ▸ small
  · obtain ⟨f, hf, code⟩ := small
    exact ⟨adjoinInjectionGraph D f a,
      M.adjoinInjectionGraph_mem pairing unions powers separation infinite hD hf ha,
      code.adjoin_fresh member⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
