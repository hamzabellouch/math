import OAI.SetTheory.PartitionPrinciple.Definability.GroundRationalCodes
import OAI.SetTheory.PartitionPrinciple.Forcing.GroundCountableFunctionForcing
import OAI.SetTheory.PartitionPrinciple.Forcing.UniformGroundSizeWitnesses

namespace OAI

open scoped ZFSet


namespace PartitionPilot.Forcing

universe u

noncomputable def indexedSizeRelation (U R W N g F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ n ∈ N, ∃ k ∈ N, ∃ p ∈ R, ∃ f ∈ W,
    z = ZFSet.pair (ZFSet.pair n k) x ∧ ZFSet.pair n p ∈ g ∧
      ZFSet.pair p f ∈ F ∧ ZFSet.pair x k ∈ f) (ZFSet.prod (ZFSet.prod N N) U)

theorem pair_mem_indexedSizeRelation (U R W N g F v x : ZFSet.{u}) :
    ZFSet.pair v x ∈ indexedSizeRelation U R W N g F ↔
      x ∈ U ∧ ∃ n ∈ N, ∃ k ∈ N, v = ZFSet.pair n k ∧ ∃ p ∈ R, ∃ f ∈ W,
        ZFSet.pair n p ∈ g ∧ ZFSet.pair p f ∈ F ∧ ZFSet.pair x k ∈ f := by
  rw [indexedSizeRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, n, hn, k, hk, p, hp, f, hf, eq, ng, pf, yk⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 eq
    exact ⟨second.symm ▸ hy, n, hn, k, hk, first, p, hp, f, hf, ng, pf, second.symm ▸ yk⟩
  · rintro ⟨hx, n, hn, k, hk, rfl, p, hp, f, hf, ng, pf, xk⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hn, hk⟩, hx⟩,
      x, hx, n, hn, k, hk, p, hp, f, hf, rfl, ng, pf, xk⟩

theorem indexedSizeRelation_partial {U R W N g F : ZFSet.{u}}
    (enumeration : ZFSet.IsFunc N R g) (family : ZFSet.IsFunc R W F)
    (codes : ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f) :
    PartialFunctionCode (ZFSet.prod N N) U (indexedSizeRelation U R W N g F) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro v x y vx vy
  obtain ⟨_, n, hn, k, _, vn, p, hp, f, _, np, pf, xk⟩ :=
    (pair_mem_indexedSizeRelation U R W N g F v x).1 vx
  obtain ⟨_, m, _, l, _, vm, q, _, h, _, mq, qh, yl⟩ :=
    (pair_mem_indexedSizeRelation U R W N g F v y).1 vy
  obtain ⟨nm, kl⟩ := ZFSet.pair_inj.1 (vn.symm.trans vm)
  subst m
  subst l
  obtain ⟨a, _, uniqueP⟩ := enumeration.2 n hn
  have pq := (uniqueP p np).trans (uniqueP q mq).symm
  subst q
  obtain ⟨b, _, uniqueF⟩ := family.2 p hp
  have fh := (uniqueF f pf).trans (uniqueF h qh).symm
  subst h
  exact (codes p f pf).injective x y k xk yl

theorem indexedSizeRelation_onto {R W N g F : ZFSet.{u}}
    (onto : ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g) (family : ZFSet.IsFunc R W F)
    (codes : ∀ p f, ZFSet.pair p f ∈ F → InjectionCode p N f) :
    ∀ x ∈ ⋃₀ R, ∃ v ∈ ZFSet.prod N N,
      ZFSet.pair v x ∈ indexedSizeRelation (⋃₀ R) R W N g F := by
  intro x hx
  obtain ⟨p, hp, xp⟩ := ZFSet.mem_sUnion.1 hx
  obtain ⟨n, hn, np⟩ := onto p hp
  obtain ⟨f, pf, _⟩ := family.2 p hp
  have hf := (ZFSet.pair_mem_prod.1 (family.1 pf)).2
  have code := codes p f pf
  obtain ⟨k, xk, _⟩ := code.function.2 x xp
  have hk := (ZFSet.pair_mem_prod.1 (code.function.1 xk)).2
  exact ⟨ZFSet.pair n k, ZFSet.pair_mem_prod.2 ⟨hn, hk⟩,
    (pair_mem_indexedSizeRelation (⋃₀ R) R W N g F _ x).2
      ⟨hx, n, hn, k, hk, rfl, p, hp, f, hf, np, pf, xk⟩⟩

namespace BoundedFormula

open SetFormula

def indexedSizeEntryFormula {k} (z u r w n g f : Fin k) : BoundedFormula k :=
  exMem u (exMem n.succ (exMem n.succ.succ (exMem r.succ.succ.succ (exMem w.succ.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ.succ 3 2 4)
      (.conj (pairMembershipFormula 3 1 g.succ.succ.succ.succ.succ)
        (.conj (pairMembershipFormula 1 0 f.succ.succ.succ.succ.succ)
          (pairMembershipFormula 4 2 0))))))))

theorem truth_indexedSizeEntryFormula {k} (z u r w n g f : Fin k) (env : Fin k → ZFSet.{u}) :
    Truth (indexedSizeEntryFormula z u r w n g f) env ↔
      ∃ x ∈ env u, ∃ i ∈ env n, ∃ j ∈ env n, ∃ p ∈ env r, ∃ h ∈ env w,
        env z = ZFSet.pair (ZFSet.pair i j) x ∧ ZFSet.pair i p ∈ env g ∧
          ZFSet.pair p h ∈ env f ∧ ZFSet.pair x j ∈ h := by
  simp only [indexedSizeEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem indexedSizeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U R W N g F : ZFSet.{u}} (hU : U ∈ M.sets) (hR : R ∈ M.sets) (hW : W ∈ M.sets)
    (hN : N ∈ M.sets) (hg : g ∈ M.sets) (hF : F ∈ M.sets) :
    indexedSizeRelation U R W N g F ∈ M.sets := by
  let params := extend U (extend R (extend W (extend N (extend g (extend F Fin.elim0)))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.indexedSizeEntryFormula 0 1 2 3 4 5 6)
    params (Fin.cases hU (Fin.cases hR (Fin.cases hW (Fin.cases hN (Fin.cases hg
      (Fin.cases hF (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hN hN) hU)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.indexedSizeEntryFormula 0 1 2 3 4 5 6)
      (extend z params)) (ZFSet.prod (ZFSet.prod N N) U) = indexedSizeRelation U R W N g F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, indexedSizeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_indexedSizeEntryFormula 0 1 2 3 4 5 6 _)
  exact eq ▸ selected

theorem groundEmbeddable_of_partial_surjection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets)
    (code : PartialFunctionCode A B r) (onto : ∀ y ∈ B, ∃ x ∈ A, ZFSet.pair x y ∈ r) :
    M.groundEmbeddable B A := by
  have inverse := M.relationConverse_mem pairing unions powers separation hA hB hr
  have total (y : ZFSet.{u}) (hy : y ∈ B) : ∃ x ∈ A, ZFSet.pair y x ∈ relationConverse A B r := by
    obtain ⟨x, hx, rel⟩ := onto y hy
    exact ⟨x, hx, (pair_mem_relationConverse A B r x y).2 ⟨hx, hy, rel⟩⟩
  obtain ⟨f, hf, func, selected⟩ := M.uniformize_relation pairing unions powers separation choice hB hA inverse total
  exact ⟨f, hf, func, fun x y z hx hy => code.unique z x y
    ((pair_mem_relationConverse A B r z x).1 (selected hx)).2.2
    ((pair_mem_relationConverse A B r z y).1 (selected hy)).2.2⟩

end TransitiveGround





noncomputable def unionSizeRelation (U R W D F : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ U, ∃ A ∈ R, ∃ k ∈ D, ∃ f ∈ W,
    z = ZFSet.pair (ZFSet.pair A k) x ∧ ZFSet.pair A f ∈ F ∧ ZFSet.pair x k ∈ f)
    (ZFSet.prod (ZFSet.prod R D) U)

theorem pair_mem_unionSizeRelation (U R W D F v x : ZFSet.{u}) :
    ZFSet.pair v x ∈ unionSizeRelation U R W D F ↔
      x ∈ U ∧ ∃ A ∈ R, ∃ k ∈ D, v = ZFSet.pair A k ∧
        ∃ f ∈ W, ZFSet.pair A f ∈ F ∧ ZFSet.pair x k ∈ f := by
  rw [unionSizeRelation, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, y, hy, A, hA, k, hk, f, hf, equal, selected, value⟩
    obtain ⟨first, second⟩ := ZFSet.pair_inj.1 equal
    exact ⟨second.symm ▸ hy, A, hA, k, hk, first, f, hf, selected, second.symm ▸ value⟩
  · rintro ⟨hx, A, hA, k, hk, rfl, f, hf, selected, value⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hA, hk⟩, hx⟩,
      x, hx, A, hA, k, hk, f, hf, rfl, selected, value⟩

theorem unionSizeRelation_partial {U R W D F : ZFSet.{u}}
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    PartialFunctionCode (ZFSet.prod R D) U (unionSizeRelation U R W D F) := by
  refine ⟨fun _ entry => (ZFSet.mem_sep.1 entry).1, ?_⟩
  intro v x y first second
  obtain ⟨_, A, hA, k, _, va, f, _, selected, value⟩ :=
    (pair_mem_unionSizeRelation U R W D F v x).1 first
  obtain ⟨_, B, _, l, _, vb, g, _, selected', value'⟩ :=
    (pair_mem_unionSizeRelation U R W D F v y).1 second
  obtain ⟨sameA, sameK⟩ := ZFSet.pair_inj.1 (va.symm.trans vb)
  subst B
  subst l
  obtain ⟨_, _, unique⟩ := family.2 A hA
  have sameF := (unique f selected).trans (unique g selected').symm
  subst g
  exact (codes A f selected).injective x y k value value'

theorem unionSizeRelation_onto {R W D F : ZFSet.{u}}
    (family : ZFSet.IsFunc R W F)
    (codes : ∀ A f, ZFSet.pair A f ∈ F → InjectionCode A D f) :
    ∀ x ∈ ⋃₀ R, ∃ v ∈ ZFSet.prod R D,
      ZFSet.pair v x ∈ unionSizeRelation (⋃₀ R) R W D F := by
  intro x hx
  obtain ⟨A, hA, member⟩ := ZFSet.mem_sUnion.1 hx
  obtain ⟨f, selected, _⟩ := family.2 A hA
  have hf := (ZFSet.pair_mem_prod.1 (family.1 selected)).2
  have code := codes A f selected
  obtain ⟨k, value, _⟩ := code.function.2 x member
  have hk := (ZFSet.pair_mem_prod.1 (code.function.1 value)).2
  exact ⟨ZFSet.pair A k, ZFSet.pair_mem_prod.2 ⟨hA, hk⟩,
    (pair_mem_unionSizeRelation (⋃₀ R) R W D F _ x).2
      ⟨hx, A, hA, k, hk, rfl, f, hf, selected, value⟩⟩

namespace BoundedFormula
open SetFormula

def unionSizeEntryFormula {n} (z u r w d f : Fin n) : BoundedFormula n :=
  exMem u (exMem r.succ (exMem d.succ.succ (exMem w.succ.succ.succ
    (.conj (orderedTripleFormula z.succ.succ.succ.succ 2 1 3)
      (.conj (pairMembershipFormula 2 0 f.succ.succ.succ.succ)
        (pairMembershipFormula 3 1 0))))))

theorem truth_unionSizeEntryFormula {n} (z u r w d f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (unionSizeEntryFormula z u r w d f) env ↔
      ∃ x ∈ env u, ∃ A ∈ env r, ∃ k ∈ env d, ∃ h ∈ env w,
        env z = ZFSet.pair (ZFSet.pair A k) x ∧
          ZFSet.pair A h ∈ env f ∧ ZFSet.pair x k ∈ h := by
  simp only [unionSizeEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround
open SetFormula
variable (M : TransitiveGround.{u})

theorem unionSizeRelation_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {U R W D F : ZFSet.{u}} (hU : U ∈ M.sets) (hR : R ∈ M.sets)
    (hW : W ∈ M.sets) (hD : D ∈ M.sets) (hF : F ∈ M.sets) :
    unionSizeRelation U R W D F ∈ M.sets := by
  let params := extend U (extend R (extend W (extend D (extend F Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.unionSizeEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hU (Fin.cases hR (Fin.cases hW (Fin.cases hD (Fin.cases hF (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hR hD) hU)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.unionSizeEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod R D) U) = unionSizeRelation U R W D F := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, unionSizeRelation, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_unionSizeEntryFormula 0 1 2 3 4 5 _)
  exact equal ▸ selected

end TransitiveGround






noncomputable def defaultInverse (R N f d : ZFSet.{u}) : ZFSet.{u} :=
  relationConverse R N f ∪
    ZFSet.prod (ZFSet.sep (fun n => n ∉ relationImage R N f) N) {d}

theorem pair_mem_defaultInverse (R N f d n p : ZFSet.{u}) :
    ZFSet.pair n p ∈ defaultInverse R N f d ↔
      (p ∈ R ∧ n ∈ N ∧ ZFSet.pair p n ∈ f) ∨
      (n ∈ N ∧ n ∉ relationImage R N f ∧ p = d) := by
  simp only [defaultInverse, ZFSet.mem_union, pair_mem_relationConverse,
    ZFSet.pair_mem_prod, ZFSet.mem_sep, ZFSet.mem_singleton, and_assoc]

theorem defaultInverse_isFunc {R N f d : ZFSet.{u}}
    (code : InjectionCode R N f) (hd : d ∈ R) :
    ZFSet.IsFunc N R (defaultInverse R N f d) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with hz | hz
    · obtain ⟨p, hp, n, hn, rfl, _⟩ := (mem_relationConverse R N f z).1 hz
      exact ZFSet.pair_mem_prod.2 ⟨hn, hp⟩
    · obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 hz
      exact ZFSet.pair_mem_prod.2
        ⟨(ZFSet.mem_sep.1 hn).1, ZFSet.mem_singleton.1 hp ▸ hd⟩
  · intro n hn
    by_cases image : n ∈ relationImage R N f
    · obtain ⟨_, p, hp, hpn⟩ := (mem_relationImage R N f n).1 image
      refine ⟨p, (pair_mem_defaultInverse R N f d n p).2 (Or.inl ⟨hp, hn, hpn⟩), ?_⟩
      intro q hq
      rcases (pair_mem_defaultInverse R N f d n q).1 hq with hq | hq
      · exact code.injective q p n hq.2.2 hpn
      · exact False.elim (hq.2.1 image)
    · refine ⟨d, (pair_mem_defaultInverse R N f d n d).2 (Or.inr ⟨hn, image, rfl⟩), ?_⟩
      intro p hp
      rcases (pair_mem_defaultInverse R N f d n p).1 hp with hp | hp
      · exact False.elim (image ((mem_relationImage R N f n).2 ⟨hn, p, hp.1, hp.2.2⟩))
      · exact hp.2.2

theorem defaultInverse_onto {R N f : ZFSet.{u}}
    (code : InjectionCode R N f) (d : ZFSet.{u}) :
    ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ defaultInverse R N f d := by
  intro p hp
  obtain ⟨n, hpn, _⟩ := code.function.2 p hp
  have hn := (ZFSet.pair_mem_prod.1 (code.function.1 hpn)).2
  exact ⟨n, hn, (pair_mem_defaultInverse R N f d n p).2 (Or.inl ⟨hp, hn, hpn⟩)⟩

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem defaultInverse_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R N f d : ZFSet.{u}}
    (hR : R ∈ M.sets) (hN : N ∈ M.sets) (hf : f ∈ M.sets) (hd : d ∈ M.sets) :
    defaultInverse R N f d ∈ M.sets := by
  have image := M.relationImage_mem separation hR hN hf
  have missing : ZFSet.sep (fun n => n ∉ relationImage R N f) N ∈ M.sets :=
    M.bounded_separation_mem separation (.neg (.mem 0 1))
      (extend (relationImage R N f) Fin.elim0) (Fin.cases image (fun i => Fin.elim0 i)) hN
  have singleton : ({d} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hd hd
  exact M.binary_union_mem pairing unions
    (M.relationConverse_mem pairing unions powers separation hR hN hf)
    (M.prod_mem pairing unions powers separation missing singleton)

theorem groundEmbeddable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {R N : ZFSet.{u}} (hR : R ∈ M.sets) (hN : N ∈ M.sets)
    (nonempty : R.Nonempty) (small : M.groundEmbeddable R N) :
    ∃ g ∈ M.sets, ZFSet.IsFunc N R g ∧
      ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g := by
  obtain ⟨d, hd⟩ := nonempty
  obtain ⟨f, hf, code⟩ := small
  exact ⟨defaultInverse R N f d,
    M.defaultInverse_mem pairing unions powers separation hR hN hf (M.transitive hR hd),
    defaultInverse_isFunc code hd, defaultInverse_onto code d⟩

theorem groundCountable_enumeration
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets) (nonempty : R.Nonempty)
    (small : M.groundEmbeddable R ZFSet.omega) :
    ∃ g ∈ M.sets, ZFSet.IsFunc ZFSet.omega R g ∧
      ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g :=
  M.groundEmbeddable_enumeration pairing unions powers separation hR
    (M.omega_mem separation infinite) nonempty small

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem enumerated_union_embeds_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B N g : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc N R g) (onto : ∀ p ∈ R, ∃ n ∈ N, ZFSet.pair n p ∈ g)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p N) :
    M.groundEmbeddable (⋃₀ R) (ZFSet.prod N N) := by
  obtain ⟨F, hF, family, codes⟩ := M.uniform_size_witnesses pairing unions powers separation choice
    hR hB hN subsets small
  have hW := M.groundRelations_mem pairing unions powers separation hB hN
  have hU := M.union_mem unions hR
  have graph := M.indexedSizeRelation_mem pairing unions powers separation hU hR hW hN hg hF
  exact M.groundEmbeddable_of_partial_surjection pairing unions powers separation choice
    (M.prod_mem pairing unions powers separation hN hN) hU graph
    (indexedSizeRelation_partial enumeration family codes) (indexedSizeRelation_onto onto family codes)

theorem countable_enumerated_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R B g : ZFSet.{u}} (hR : R ∈ M.sets) (hB : B ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc ZFSet.omega R g)
    (onto : ∀ p ∈ R, ∃ n ∈ ZFSet.omega, ZFSet.pair n p ∈ g)
    (subsets : ∀ p ∈ R, p ⊆ B) (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  have hw := M.omega_mem separation infinite
  have hww := M.prod_mem pairing unions powers separation hw hw
  obtain ⟨f, hf, code⟩ := M.enumerated_union_embeds_product pairing unions powers separation choice
    hR hB hw hg enumeration onto subsets small
  obtain ⟨c, hc, ccode⟩ := M.omega_product_countable pairing unions powers separation infinite
  exact ⟨relationCompose (⋃₀ R) (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega f c,
    M.relationCompose_mem pairing unions powers separation (M.union_mem unions hR) hww hw hf hc,
    code.compose ccode⟩

theorem countable_union_of_sequence_graph
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {Q B g : ZFSet.{u}} (hQ : Q ∈ M.sets) (hB : B ∈ M.sets) (hg : g ∈ M.sets)
    (enumeration : ZFSet.IsFunc ZFSet.omega Q g)
    (subsets : ∀ p ∈ Q, p ⊆ B) (small : ∀ p ∈ Q, M.groundEmbeddable p ZFSet.omega) :
    (⋃₀ relationImage ZFSet.omega Q g) ∈ M.sets ∧
      M.groundEmbeddable (⋃₀ relationImage ZFSet.omega Q g) ZFSet.omega := by
  let R := relationImage ZFSet.omega Q g
  have hR := M.relationImage_mem separation (M.omega_mem separation infinite) hQ hg
  have restricted : ZFSet.IsFunc ZFSet.omega R g := by
    refine ⟨?_, enumeration.2⟩
    intro z hz
    obtain ⟨n, hn, p, hp, rfl⟩ := ZFSet.mem_prod.1 (enumeration.1 hz)
    exact ZFSet.pair_mem_prod.2 ⟨hn, (mem_relationImage ZFSet.omega Q g p).2 ⟨hp, n, hn, hz⟩⟩
  exact ⟨M.union_mem unions hR,
    M.countable_enumerated_union pairing unions powers separation infinite choice hR hB hg restricted
      (fun p hp => ((mem_relationImage ZFSet.omega Q g p).1 hp).2)
      (fun p hp => subsets p ((mem_relationImage ZFSet.omega Q g p).1 hp).1)
      (fun p hp => small p ((mem_relationImage ZFSet.omega Q g p).1 hp).1)⟩






theorem groundCountable_family_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {R : ZFSet.{u}} (hR : R ∈ M.sets)
    (countR : M.groundEmbeddable R ZFSet.omega)
    (small : ∀ p ∈ R, M.groundEmbeddable p ZFSet.omega) :
    M.groundEmbeddable (⋃₀ R) ZFSet.omega := by
  classical
  by_cases nonempty : R.Nonempty
  · obtain ⟨g, hg, enumeration, onto⟩ :=
      M.groundCountable_enumeration pairing unions powers separation infinite hR nonempty countR
    exact M.countable_enumerated_union pairing unions powers separation infinite choice
      hR (M.union_mem unions hR) hg enumeration onto
      (fun p hp _ hz => ZFSet.mem_sUnion.2 ⟨p, hp, hz⟩) small
  · have empty : R = ∅ := by
      apply ZFSet.ext
      intro p
      exact ⟨fun hp => False.elim (nonempty ⟨p, hp⟩), fun hp => False.elim (ZFSet.notMem_empty p hp)⟩
    rw [empty, ZFSet.sUnion_empty]
    exact M.empty_groundEmbeddable ZFSet.omega ⟨R, hR⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing

open SetRealization
universe u

noncomputable def groundSequenceGraph {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) : ZFSet.{u} :=
  natPresentation.graph (SetMembers.presentation Q) (fun n => seq n.down)

noncomputable def groundSequenceUnion {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) : ZFSet.{u} :=
  ⋃₀ relationImage ZFSet.omega Q (groundSequenceGraph seq)

theorem mem_groundSequenceUnion {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (z : ZFSet.{u}) :
    z ∈ groundSequenceUnion seq ↔ ∃ n, z ∈ SetMembers.raw (seq n) := by
  rw [groundSequenceUnion, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨p, hp, zp⟩
    obtain ⟨_, n, _, np⟩ := (mem_relationImage ZFSet.omega Q (groundSequenceGraph seq) p).1 hp
    obtain ⟨k, eq⟩ := (natPresentation.mem_graph (SetMembers.presentation Q) (fun n => seq n.down) _).1 np
    have second := (ZFSet.pair_inj.1 eq).2
    change SetMembers.raw (seq k.down) = p at second
    exact ⟨k.down, second.symm ▸ zp⟩
  · rintro ⟨n, hn⟩
    exact ⟨SetMembers.raw (seq n), (mem_relationImage ZFSet.omega Q (groundSequenceGraph seq) _).2
      ⟨SetMembers.raw_mem _, natSetCode n, natSetCode_mem_omega _,
        (natPresentation.pair_mem_graph (SetMembers.presentation Q) (fun k => seq k.down) ⟨n⟩ (seq n)).2 rfl⟩, hn⟩

theorem groundSequenceUnion_extends {Q : ZFSet.{u}} (seq : Nat → SetMembers Q) (n : Nat) :
    SetMembers.raw (seq n) ⊆ groundSequenceUnion seq :=
  fun _ hz => (mem_groundSequenceUnion seq _).2 ⟨n, hz⟩

def InternallyCountablyClosed (M : TransitiveGround.{u}) {P : Type u} [Preorder P]
    (s : Presentation P) : Prop :=
  ∀ seq : Nat → P, natPresentation.graph s (fun n => seq n.down) ∈ M.sets →
    Antitone seq → ∃ p, ∀ n, p ≤ seq n

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem descending_function_union_partial (X Y : ZFSet.{u}) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      Antitone seq → PartialFunctionCode X Y (groundSequenceUnion seq) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq decreasing
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq z).1 hz
    exact (M.smallFunction_raw_properties X Y ZFSet.omega (seq n)).2.1.shape hn
  · intro x y z xy xz
    obtain ⟨n, hn⟩ := (mem_groundSequenceUnion seq _).1 xy
    obtain ⟨m, hm⟩ := (mem_groundSequenceUnion seq _).1 xz
    have code := (M.smallFunction_raw_properties X Y ZFSet.omega (seq (max n m))).2.1
    exact code.unique x y z
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_left n m)) hn)
      ((M.smallFunction_le_iff X Y ZFSet.omega _ _).1 (decreasing (Nat.le_max_right n m)) hm)

theorem descending_function_union_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        groundSequenceUnion seq ∈ M.smallPartialFunctions X Y ZFSet.omega := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have hQ := M.countablePartialFunctions_mem pairing unions powers separation infinite hX hY
  obtain ⟨ground, small⟩ := M.countable_union_of_sequence_graph pairing unions powers separation infinite choice
    hQ (M.prod_mem pairing unions powers separation hX hY) graph
    (natPresentation.graph_isFunc (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega))
      (fun n => seq n.down))
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.1.shape)
    (fun p hp => ((M.mem_smallPartialFunctions X Y ZFSet.omega p).1 hp).2.2)
  exact (M.mem_smallPartialFunctions X Y ZFSet.omega _).2
    ⟨ground, M.descending_function_union_partial X Y seq decreasing, small⟩

theorem countable_function_lower_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    ∀ seq : Nat → SetMembers (M.smallPartialFunctions X Y ZFSet.omega),
      groundSequenceGraph seq ∈ M.sets → Antitone seq →
        ∃ p, SetMembers.raw p = groundSequenceUnion seq ∧ ∀ n, p ≤ seq n := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  have member := M.descending_function_union_mem pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  let p := SetMembers.ofMem (groundSequenceUnion seq) member
  have raw : SetMembers.raw p = groundSequenceUnion seq := SetMembers.raw_ofMem _ _
  refine ⟨p, raw, fun n => (M.smallFunction_le_iff X Y ZFSet.omega p (seq n)).2 ?_⟩
  rw [raw]
  exact groundSequenceUnion_extends seq n

theorem countable_function_internally_closed
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    letI := M.smallFunctionOrder X Y ZFSet.omega
    InternallyCountablyClosed M (SetMembers.presentation (M.smallPartialFunctions X Y ZFSet.omega)) := by
  let smallOrder := M.smallFunctionOrder X Y ZFSet.omega
  intro seq graph decreasing
  obtain ⟨p, _, lower⟩ := M.countable_function_lower_bound pairing unions powers separation infinite choice
    hX hY seq graph decreasing
  exact ⟨p, lower⟩

end TransitiveGround

end PartitionPilot.Forcing

end OAI
