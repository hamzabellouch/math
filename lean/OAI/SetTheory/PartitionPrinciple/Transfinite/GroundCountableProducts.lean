import OAI.SetTheory.PartitionPrinciple.Definability.BatchAttachmentRealization

namespace OAI

section

namespace PartitionPilot.Forcing

universe u

noncomputable def relationProduct (A B C D f g : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D,
    z = ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∧
      ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g)
    (ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D))

theorem mem_relationProduct (A B C D f g z : ZFSet.{u}) :
    z ∈ relationProduct A B C D f g ↔
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, ∃ d ∈ D,
        z = ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∧
          ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g := by
  constructor
  · exact fun h => (ZFSet.mem_sep.1 h).2
  · rintro ⟨a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2
      ⟨ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, ZFSet.pair_mem_prod.2 ⟨hc, hd⟩⟩,
      a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩

theorem pair_mem_relationProduct (A B C D f g a b c d : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair a b) (ZFSet.pair c d) ∈ relationProduct A B C D f g ↔
      a ∈ A ∧ b ∈ B ∧ c ∈ C ∧ d ∈ D ∧ ZFSet.pair a c ∈ f ∧ ZFSet.pair b d ∈ g := by
  rw [mem_relationProduct]
  constructor
  · rintro ⟨a', ha, b', hb, c', hc, d', hd, equal, fac, gbd⟩
    obtain ⟨left, right⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 left
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 right
    exact ⟨ha, hb, hc, hd, fac, gbd⟩
  · rintro ⟨ha, hb, hc, hd, fac, gbd⟩
    exact ⟨a, ha, b, hb, c, hc, d, hd, rfl, fac, gbd⟩

theorem relationProduct_function {A B C D f g : ZFSet.{u}}
    (first : ZFSet.IsFunc A C f) (second : ZFSet.IsFunc B D g) :
    ZFSet.IsFunc (ZFSet.prod A B) (ZFSet.prod C D) (relationProduct A B C D f g) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := ZFSet.mem_prod.1 hx
  obtain ⟨c, fac, uniqueC⟩ := first.2 a ha
  obtain ⟨d, gbd, uniqueD⟩ := second.2 b hb
  have hc := (ZFSet.pair_mem_prod.1 (first.1 fac)).2
  have hd := (ZFSet.pair_mem_prod.1 (second.1 gbd)).2
  refine ⟨ZFSet.pair c d, (pair_mem_relationProduct A B C D f g a b c d).2
    ⟨ha, hb, hc, hd, fac, gbd⟩, ?_⟩
  intro z hz
  obtain ⟨c', _, d', _, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hz).1).2
  obtain ⟨_, _, _, _, fac', gbd'⟩ := (pair_mem_relationProduct A B C D f g a b c' d').1 hz
  exact congrArg₂ ZFSet.pair (uniqueC c' fac') (uniqueD d' gbd')

theorem relationProduct_injection {A B C D f g : ZFSet.{u}}
    (first : InjectionCode A C f) (second : InjectionCode B D g) :
    InjectionCode (ZFSet.prod A B) (ZFSet.prod C D) (relationProduct A B C D f g) := by
  refine ⟨relationProduct_function first.function second.function, ?_⟩
  intro x y z hx hy
  have shapeX := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hx).1
  have shapeY := ZFSet.pair_mem_prod.1 (ZFSet.mem_sep.1 hy).1
  obtain ⟨a, _, b, _, rfl⟩ := ZFSet.mem_prod.1 shapeX.1
  obtain ⟨a', _, b', _, rfl⟩ := ZFSet.mem_prod.1 shapeY.1
  obtain ⟨c, _, d, _, rfl⟩ := ZFSet.mem_prod.1 shapeX.2
  obtain ⟨_, _, _, _, fac, gbd⟩ := (pair_mem_relationProduct A B C D f g a b c d).1 hx
  obtain ⟨_, _, _, _, fa'c, gb'd⟩ := (pair_mem_relationProduct A B C D f g a' b' c d).1 hy
  exact congrArg₂ ZFSet.pair (first.injective a a' c fac fa'c) (second.injective b b' d gbd gb'd)

namespace BoundedFormula

def relationProductEntryFormula {n} (z a b c d f g : Fin n) : BoundedFormula n :=
  let lift (i : Fin n) := i.succ.succ.succ.succ
  exMem a (exMem b.succ (exMem c.succ.succ (exMem d.succ.succ.succ
    (.conj (pairOfPairsFormula (lift z) 3 2 1 0)
      (.conj (pairMembershipFormula 3 1 (lift f)) (pairMembershipFormula 2 0 (lift g)))))))

theorem truth_relationProductEntryFormula {n} (z a b c d f g : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationProductEntryFormula z a b c d f g) env ↔
      ∃ x ∈ env a, ∃ y ∈ env b, ∃ p ∈ env c, ∃ q ∈ env d,
        env z = ZFSet.pair (ZFSet.pair x y) (ZFSet.pair p q) ∧
          ZFSet.pair x p ∈ env f ∧ ZFSet.pair y q ∈ env g := by
  simp only [relationProductEntryFormula, truth_exMem, Truth,
    truth_pairOfPairsFormula, truth_pairMembershipFormula]
  rfl

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem relationProduct_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C D f g : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hC : C ∈ M.sets) (hD : D ∈ M.sets) (hf : f ∈ M.sets) (hg : g ∈ M.sets) :
    relationProduct A B C D f g ∈ M.sets := by
  let params := extend A (extend B (extend C (extend D (extend f (extend g Fin.elim0)))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6) params
    (Fin.cases hA (Fin.cases hB (Fin.cases hC (Fin.cases hD
      (Fin.cases hf (Fin.cases hg (fun i => Fin.elim0 i)))))))
    (M.prod_mem pairing unions powers separation
      (M.prod_mem pairing unions powers separation hA hB)
      (M.prod_mem pairing unions powers separation hC hD))
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.relationProductEntryFormula 0 1 2 3 4 5 6) (extend z params))
      (ZFSet.prod (ZFSet.prod A B) (ZFSet.prod C D)) = relationProduct A B C D f g := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationProduct, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_relationProductEntryFormula 0 1 2 3 4 5 6 _)
  exact equal ▸ selected

theorem countableProduct_injection
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B f g : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hf : f ∈ M.sets) (hg : g ∈ M.sets)
    (first : InjectionCode A ZFSet.omega f) (second : InjectionCode B ZFSet.omega g) :
    ∃ h ∈ M.sets, InjectionCode (ZFSet.prod A B) ZFSet.omega h := by
  have hw := M.omega_mem separation infinite
  have hAB := M.prod_mem pairing unions powers separation hA hB
  have hww := M.prod_mem pairing unions powers separation hw hw
  have product := M.relationProduct_mem pairing unions powers separation hA hB hw hw hf hg
  obtain ⟨c, hc, pairingCode⟩ := M.omega_product_countable pairing unions powers separation infinite
  exact ⟨relationCompose (ZFSet.prod A B) (ZFSet.prod ZFSet.omega ZFSet.omega) ZFSet.omega
      (relationProduct A B ZFSet.omega ZFSet.omega f g) c,
    M.relationCompose_mem pairing unions powers separation hAB hww hw product hc,
    (relationProduct_injection first second).compose pairingCode⟩

theorem groundEmbeddable_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets SetFormula.infinity Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (first : M.groundEmbeddable A ZFSet.omega) (second : M.groundEmbeddable B ZFSet.omega) :
    M.groundEmbeddable (ZFSet.prod A B) ZFSet.omega := by
  obtain ⟨f, hf, firstCode⟩ := first
  obtain ⟨g, hg, secondCode⟩ := second
  exact M.countableProduct_injection pairing unions powers separation infinite hA hB hf hg firstCode secondCode

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
