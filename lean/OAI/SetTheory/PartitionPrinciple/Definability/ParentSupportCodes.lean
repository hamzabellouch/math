import OAI.SetTheory.PartitionPrinciple.Definability.GroundPairCompositions

namespace OAI


namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def orderedRightTripleFormula {n} (w x c q : Fin n) : BoundedFormula n :=
  exMem w (exMem 0 (.conj (orderedPairFormula 0 c.succ.succ q.succ.succ)
    (orderedPairFormula w.succ.succ x.succ.succ 0)))

def rightTripleMembershipFormula {n} (x c q f : Fin n) : BoundedFormula n :=
  exMem f (orderedRightTripleFormula 0 x.succ c.succ q.succ)

theorem truth_orderedRightTripleFormula {n} (w x c q : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (orderedRightTripleFormula w x c q) env ↔
      env w = ZFSet.pair (env x) (ZFSet.pair (env c) (env q)) := by
  simp only [orderedRightTripleFormula, truth_exMem, Truth, truth_orderedPairFormula]
  change (∃ a ∈ env w, ∃ b ∈ a, b = ZFSet.pair (env c) (env q) ∧
    env w = ZFSet.pair (env x) b) ↔ _
  constructor
  · rintro ⟨_, _, _, _, rfl, equal⟩
    exact equal
  · intro equal
    refine ⟨{env x, ZFSet.pair (env c) (env q)}, ?_, ZFSet.pair (env c) (env q),
      ZFSet.mem_pair.2 (Or.inr rfl), rfl, equal⟩
    rw [equal]
    exact ZFSet.mem_pair.2 (Or.inr rfl)

theorem truth_rightTripleMembershipFormula {n} (x c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (rightTripleMembershipFormula x c q f) env ↔
      ZFSet.pair (env x) (ZFSet.pair (env c) (env q)) ∈ env f := by
  simp only [rightTripleMembershipFormula, truth_exMem, truth_orderedRightTripleFormula]
  change (∃ w ∈ env f, w = ZFSet.pair (env x) (ZFSet.pair (env c) (env q))) ↔ _
  constructor
  · rintro ⟨w, hw, heq⟩
    exact heq ▸ hw
  · intro hw
    exact ⟨_, hw, rfl⟩

def relationToProductFormula {n} (a c q f : Fin n) : BoundedFormula n :=
  .allMem f (exMem a.succ (exMem c.succ.succ
    (exMem q.succ.succ.succ (orderedRightTripleFormula 3 2 1 0))))

def functionToProductFormula {n} (a c q f : Fin n) : BoundedFormula n :=
  .conj (relationToProductFormula a c q f)
    (.allMem a (exMem c.succ (exMem q.succ.succ
      (.conj (rightTripleMembershipFormula 2 1 0 f.succ.succ.succ)
        (.allMem c.succ.succ.succ (.allMem q.succ.succ.succ.succ
          (imp (rightTripleMembershipFormula 4 1 0 f.succ.succ.succ.succ.succ)
            (.conj (.equal 1 3) (.equal 0 2)))))))))

theorem truth_relationToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationToProductFormula a c q f) env ↔
      env f ⊆ ZFSet.prod (env a) (ZFSet.prod (env c) (env q)) := by
  simp only [relationToProductFormula, Truth, truth_exMem, truth_orderedRightTripleFormula]
  constructor
  · intro h w hw
    obtain ⟨x, hx, d, hd, v, hv, equal⟩ := h w hw
    exact ZFSet.mem_prod.2 ⟨x, hx, ZFSet.pair d v, ZFSet.pair_mem_prod.2 ⟨hd, hv⟩, equal⟩
  · intro h w hw
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 (h hw)
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 hy
    exact ⟨x, hx, d, hd, v, hv, equal⟩

theorem truth_functionToProductFormula {n} (a c q f : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (functionToProductFormula a c q f) env ↔
      ZFSet.IsFunc (env a) (ZFSet.prod (env c) (env q)) (env f) := by
  simp only [functionToProductFormula, Truth, truth_relationToProductFormula, truth_exMem,
    truth_rightTripleMembershipFormula, truth_imp]
  constructor
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨d, _, v, _, entry, unique⟩ := total x hx
    refine ⟨ZFSet.pair d v, entry, ?_⟩
    intro y hy
    obtain ⟨b, hb, z, hz, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape hy)).2
    have both : b = d ∧ z = v := unique b hb z hz hy
    obtain ⟨rfl, rfl⟩ := both
    rfl
  · rintro ⟨shape, total⟩
    refine ⟨shape, ?_⟩
    intro x hx
    obtain ⟨y, entry, unique⟩ := total x hx
    obtain ⟨d, hd, v, hv, rfl⟩ := ZFSet.mem_prod.1 (ZFSet.pair_mem_prod.1 (shape entry)).2
    refine ⟨d, hd, v, hv, entry, ?_⟩
    intro b _ z _ hz
    exact ZFSet.pair_injective (unique _ hz)

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing

open scoped ZFSet

universe u

structure ChoiceFunctionCode (A f : ZFSet.{u}) : Prop where
  function : ZFSet.IsFunc A (⋃₀ A) f
  chosen : ∀ x y, ZFSet.pair x y ∈ f → y ∈ x

namespace BoundedFormula

open SetFormula

theorem truth_nonemptyFormula {n} (x : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (nonemptyFormula x) env ↔ (env x).Nonempty := by
  simp only [nonemptyFormula, truth_exMem, Truth]
  exact ⟨fun ⟨y, hy, _⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy, True.intro⟩⟩

theorem truth_choiceFunctionFormula {n} (a f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (choiceFunctionFormula a f) env ↔ ChoiceFunctionCode (env a) (env f) := by
  simp only [choiceFunctionFormula, Truth, truth_exMem, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_imp]
  change ((∀ z ∈ env f, ∃ x ∈ env a, ∃ y ∈ x, z = ZFSet.pair x y) ∧
    ∀ x ∈ env a, ∃ y ∈ x, ZFSet.pair x y ∈ env f ∧
      ∀ z ∈ x, ZFSet.pair x z ∈ env f → z = y) ↔ _
  constructor
  · rintro ⟨shape, total⟩
    have chosen : ∀ x y, ZFSet.pair x y ∈ env f → y ∈ x := by
      intro x y rel
      obtain ⟨x', _, y', hy', eq⟩ := shape _ rel
      obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
      exact hy'
    refine ⟨⟨?_, ?_⟩, chosen⟩
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := shape z hz
      exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_sUnion.2 ⟨x, hx, hy⟩⟩
    · intro x hx
      obtain ⟨y, _, rel, unique⟩ := total x hx
      exact ⟨y, rel, fun z hz => unique z (chosen x z hz) hz⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro z hz
      obtain ⟨x, hx, y, _, eq⟩ := ZFSet.mem_prod.1 (h.function.1 hz)
      exact ⟨x, hx, y, h.chosen x y (eq ▸ hz), eq⟩
    · intro x hx
      obtain ⟨y, rel, unique⟩ := h.function.2 x hx
      exact ⟨y, h.chosen x y rel, rel, fun z _ hz => unique z hz⟩

end BoundedFormula


namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem choice_witness (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) (nonempty : ∀ x ∈ A, x.Nonempty) :
    ∃ f ∈ M.sets, ChoiceFunctionCode A f := by
  have selected := (realize_imp M.sets _ _ _).1 (choice A hA)
  have premise : Realize M.sets
      (BoundedFormula.allMem 0 (BoundedFormula.nonemptyFormula 0)).toFormula (extend A Fin.elim0) := by
    apply (BoundedFormula.realize_toFormula M _ _ (Fin.cases hA (fun i => Fin.elim0 i))).2
    intro x hx
    exact (BoundedFormula.truth_nonemptyFormula 0 _).2 (nonempty x hx)
  obtain ⟨f, hf, rel⟩ := (realize_ex M.sets _ _).1 (selected premise)
  exact ⟨f, hf, (BoundedFormula.truth_choiceFunctionFormula 1 0 _).1
    ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hf (Fin.cases hA (fun i => Fin.elim0 i)))).1 rel)⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing

universe u

noncomputable def relationFiber (B r x : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ZFSet.pair x y ∈ r) B

theorem mem_relationFiber (B r x y : ZFSet.{u}) :
    y ∈ relationFiber B r x ↔ y ∈ B ∧ ZFSet.pair x y ∈ r := ZFSet.mem_sep

noncomputable def choiceUniformGraph (A B r F c : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, z = ZFSet.pair x y ∧
    relationFiber B r x ∈ F ∧ ZFSet.pair (relationFiber B r x) y ∈ c) (ZFSet.prod A B)

theorem pair_mem_choiceUniformGraph (A B r F c x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ choiceUniformGraph A B r F c ↔
      x ∈ A ∧ y ∈ B ∧ relationFiber B r x ∈ F ∧ ZFSet.pair (relationFiber B r x) y ∈ c := by
  rw [choiceUniformGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, a, ha, b, hb, eq, hf, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, hf, rel⟩
  · rintro ⟨hx, hy, hf, rel⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hx, hy⟩, x, hx, y, hy, rfl, hf, rel⟩

theorem choiceUniformGraph_function {A B r F c : ZFSet.{u}} (choice : ChoiceFunctionCode F c)
    (fibers : ∀ x ∈ A, relationFiber B r x ∈ F) :
    ZFSet.IsFunc A B (choiceUniformGraph A B r F c) ∧ choiceUniformGraph A B r F c ⊆ r := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, rel, unique⟩ := choice.function.2 (relationFiber B r x) (fibers x hx)
    have hy := (mem_relationFiber B r x y).1 (choice.chosen _ _ rel)
    exact ⟨y, (pair_mem_choiceUniformGraph A B r F c x y).2 ⟨hx, hy.1, fibers x hx, rel⟩,
      fun z hz => unique z ((pair_mem_choiceUniformGraph A B r F c x z).1 hz).2.2.2⟩
  · intro z hz
    obtain ⟨_, x, _, y, _, eq, _, rel⟩ := ZFSet.mem_sep.1 hz
    exact eq.symm ▸ ((mem_relationFiber B r x y).1 (choice.chosen _ _ rel)).2

namespace BoundedFormula

open SetFormula

def fiberFormula {n} (f x b r : Fin n) : BoundedFormula n :=
  .conj (.allMem f (.mem 0 b.succ)) (.allMem b
    (.conj (imp (.mem 0 f.succ) (pairMembershipFormula x.succ 0 r.succ))
      (imp (pairMembershipFormula x.succ 0 r.succ) (.mem 0 f.succ))))

theorem truth_fiberFormula {n} (f x b r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (fiberFormula f x b r) env ↔ env f = relationFiber (env b) (env r) (env x) := by
  simp only [fiberFormula, Truth, truth_imp, truth_pairMembershipFormula]
  change ((∀ y ∈ env f, y ∈ env b) ∧ ∀ y ∈ env b,
    (y ∈ env f → ZFSet.pair (env x) y ∈ env r) ∧ (ZFSet.pair (env x) y ∈ env r → y ∈ env f)) ↔ _
  constructor
  · rintro ⟨subset, spec⟩
    apply ZFSet.ext
    intro y
    rw [mem_relationFiber]
    exact ⟨fun hy => ⟨subset y hy, (spec y (subset y hy)).1 hy⟩,
      fun ⟨hy, rel⟩ => (spec y hy).2 rel⟩
  · intro eq
    rw [eq]
    exact ⟨fun _ hy => (ZFSet.mem_sep.1 hy).1,
      fun y hy => ⟨fun rel => (ZFSet.mem_sep.1 rel).2, fun rel => ZFSet.mem_sep.2 ⟨hy, rel⟩⟩⟩

def choiceUniformEntryFormula {n} (z a b r f c : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (exMem f.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 1)
      (.conj (fiberFormula 0 2 b.succ.succ.succ r.succ.succ.succ)
        (pairMembershipFormula 0 1 c.succ.succ.succ)))))

theorem truth_choiceUniformEntryFormula {n} (z a b r f c : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (choiceUniformEntryFormula z a b r f c) env ↔
      ∃ x ∈ env a, ∃ y ∈ env b, env z = ZFSet.pair x y ∧
        relationFiber (env b) (env r) x ∈ env f ∧ ZFSet.pair (relationFiber (env b) (env r) x) y ∈ env c := by
  simp only [choiceUniformEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_fiberFormula, truth_pairMembershipFormula]
  change (∃ x ∈ env a, ∃ y ∈ env b, ∃ F ∈ env f, env z = ZFSet.pair x y ∧
    F = relationFiber (env b) (env r) x ∧ ZFSet.pair F y ∈ env c) ↔ _
  constructor
  · rintro ⟨x, hx, y, hy, F, hF, eq, rfl, rel⟩
    exact ⟨x, hx, y, hy, eq, hF, rel⟩
  · rintro ⟨x, hx, y, hy, eq, hF, rel⟩
    exact ⟨x, hx, y, hy, relationFiber (env b) (env r) x, hF, eq, rfl, rel⟩

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem relationFiber_mem (separation : SeparationSchema M.sets) {B r x : ZFSet.{u}}
    (hB : B ∈ M.sets) (hr : r ∈ M.sets) (hx : x ∈ M.sets) : relationFiber B r x ∈ M.sets := by
  let params := extend x (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.pairMembershipFormula 1 0 2)
    params (Fin.cases hx (Fin.cases hr (fun i => Fin.elim0 i))) hB
  have eq : ZFSet.sep (fun y => BoundedFormula.Truth (BoundedFormula.pairMembershipFormula 1 0 2)
      (extend y params)) B = relationFiber B r x := by
    apply ZFSet.ext
    intro y
    rw [ZFSet.mem_sep, mem_relationFiber]
    exact and_congr Iff.rfl (BoundedFormula.truth_pairMembershipFormula 1 0 2 _)
  exact eq ▸ selected

noncomputable def nonemptyGroundSubsets (B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep ZFSet.Nonempty (M.groundPower B)

theorem mem_nonemptyGroundSubsets (B F : ZFSet.{u}) :
    F ∈ M.nonemptyGroundSubsets B ↔ F ∈ M.sets ∧ F ⊆ B ∧ F.Nonempty := by
  rw [nonemptyGroundSubsets, ZFSet.mem_sep, M.mem_groundPower]
  exact and_assoc

theorem nonemptyGroundSubsets_mem (powers : Realize M.sets powerSet Fin.elim0)
    (separation : SeparationSchema M.sets) {B : ZFSet.{u}} (hB : B ∈ M.sets) :
    M.nonemptyGroundSubsets B ∈ M.sets := by
  have selected := M.bounded_separation_mem separation (BoundedFormula.nonemptyFormula 0)
    Fin.elim0 (fun i => Fin.elim0 i) (M.groundPower_mem powers hB)
  have eq : ZFSet.sep (fun F => BoundedFormula.Truth (BoundedFormula.nonemptyFormula 0)
      (extend F Fin.elim0)) (M.groundPower B) = M.nonemptyGroundSubsets B := by
    apply ZFSet.ext
    intro F
    rw [ZFSet.mem_sep, nonemptyGroundSubsets, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_nonemptyFormula 0 _)
  exact eq ▸ selected

theorem choiceUniformGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B r F c : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets)
    (hr : r ∈ M.sets) (hF : F ∈ M.sets) (hc : c ∈ M.sets) : choiceUniformGraph A B r F c ∈ M.sets := by
  let params := extend A (extend B (extend r (extend F (extend c Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.choiceUniformEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hr (Fin.cases hF (Fin.cases hc (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hA hB)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.choiceUniformEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod A B) = choiceUniformGraph A B r F c := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, choiceUniformGraph, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_choiceUniformEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem uniformize_relation
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (choice : Realize M.sets SetFormula.choice Fin.elim0)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets)
    (total : ∀ x ∈ A, ∃ y ∈ B, ZFSet.pair x y ∈ r) :
    ∃ f ∈ M.sets, ZFSet.IsFunc A B f ∧ f ⊆ r := by
  have family := M.nonemptyGroundSubsets_mem powers separation hB
  obtain ⟨c, hc, code⟩ := M.choice_witness choice family
    (fun F hF => ((M.mem_nonemptyGroundSubsets B F).1 hF).2.2)
  have fibers (x : ZFSet.{u}) (hx : x ∈ A) : relationFiber B r x ∈ M.nonemptyGroundSubsets B := by
    obtain ⟨y, hy, rel⟩ := total x hx
    exact (M.mem_nonemptyGroundSubsets B _).2
      ⟨M.relationFiber_mem separation hB hr (M.transitive hA hx), fun _ hz => (ZFSet.mem_sep.1 hz).1,
        y, (mem_relationFiber B r x y).2 ⟨hy, rel⟩⟩
  exact ⟨choiceUniformGraph A B r (M.nonemptyGroundSubsets B) c,
    M.choiceUniformGraph_mem pairing unions powers separation hA hB hr family hc,
    choiceUniformGraph_function code fibers⟩

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace BoundedFormula
def relationFiberFamilyEntryFormula {n} (z I W B R : Fin n) : BoundedFormula n :=
  exMem I (exMem W.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (fiberFormula 0 1 B.succ.succ R.succ.succ)))

theorem truth_relationFiberFamilyEntryFormula {n} (z I W B R : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (relationFiberFamilyEntryFormula z I W B R) env ↔
      ∃ i ∈ env I, ∃ f ∈ env W, env z = ZFSet.pair i f ∧
        f = relationFiber (env B) (env R) i := by
  simp only [relationFiberFamilyEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_fiberFormula]
  rfl
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def relationFiberFamily (I B R : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ i ∈ I, ∃ f ∈ M.groundPower B,
    z = ZFSet.pair i f ∧ f = relationFiber B R i) (ZFSet.prod I (M.groundPower B))

theorem pair_mem_relationFiberFamily (I B R i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.relationFiberFamily I B R ↔
      i ∈ I ∧ f ∈ M.groundPower B ∧ f = relationFiber B R i := by
  rw [relationFiberFamily, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨_, j, hj, g, hg, equal, value⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hj, hg, value⟩
  · rintro ⟨hi, hf, equal⟩
    exact ⟨⟨hi, hf⟩, i, hi, f, hf, rfl, equal⟩

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {I B R : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets) (hR : R ∈ M.sets)

include pairing unions powers separation hI hB hR in
theorem relationFiberFamily_mem : M.relationFiberFamily I B R ∈ M.sets := by
  have hW := M.groundPower_mem powers hB
  let params := extend I (extend (M.groundPower B) (extend B (extend R Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.relationFiberFamilyEntryFormula 0 1 2 3 4) params
    (Fin.cases hI (Fin.cases hW (Fin.cases hB (Fin.cases hR (fun j => Fin.elim0 j)))))
    (M.prod_mem pairing unions powers separation hI hW)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.relationFiberFamilyEntryFormula 0 1 2 3 4) (extend z params))
      (ZFSet.prod I (M.groundPower B)) = M.relationFiberFamily I B R := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationFiberFamily, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_relationFiberFamilyEntryFormula 0 1 2 3 4 _)
  exact equal ▸ selected

include separation hI hB hR in
theorem relationFiberFamily_function :
    ZFSet.IsFunc I (M.groundPower B) (M.relationFiberFamily I B R) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro i hi
  have bound := (M.mem_groundPower B (relationFiber B R i)).2
    ⟨M.relationFiber_mem separation hB hR (M.transitive hI hi),
      fun _ hz => (mem_relationFiber _ _ _ _).1 hz |>.1⟩
  exact ⟨relationFiber B R i,
    (M.pair_mem_relationFiberFamily I B R i _).2 ⟨hi, bound, rfl⟩,
    fun f entry => ((M.pair_mem_relationFiberFamily I B R i f).1 entry).2.2⟩

include separation hI hB hR in
theorem relationFiberFamily_entries (i f : ZFSet.{u}) :
    ZFSet.pair i f ∈ M.relationFiberFamily I B R ↔ i ∈ I ∧ f = relationFiber B R i := by
  constructor
  · intro entry
    have parts := (M.pair_mem_relationFiberFamily I B R i f).1 entry
    exact ⟨parts.1, parts.2.2⟩
  · rintro ⟨hi, rfl⟩
    obtain ⟨f, entry, _⟩ := (M.relationFiberFamily_function separation hI hB hR).2 i hi
    have equal := ((M.pair_mem_relationFiberFamily I B R i f).1 entry).2.2
    exact equal ▸ entry

end TransitiveGround





def ExternalCosetSupport (E U C classifier copies zero v y : ZFSet.{u}) : Prop :=
  ∃ c ∈ C, ∃ w ∈ E, ∃ x ∈ U, v = ZFSet.pair zero c ∧
    ZFSet.pair w c ∈ classifier ∧ ZFSet.pair (ZFSet.pair w x) y ∈ copies

def ExternalTileSupport (E Q Requests localPoints action first v y : ZFSet.{u}) : Prop :=
  ∃ w ∈ E, ∃ r ∈ Requests, ∃ x ∈ Q, v = ZFSet.pair first (ZFSet.pair w r) ∧
    ZFSet.pair r x ∈ localPoints ∧ ZFSet.pair (ZFSet.pair w x) y ∈ action

def externalStarSupportGraph (V Q E U C Requests classifier copies localPoints action zero first : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ y ∈ Q, z = ZFSet.pair v y ∧
    (ExternalCosetSupport E U C classifier copies zero v y ∨
      ExternalTileSupport E Q Requests localPoints action first v y)) (ZFSet.prod V Q)

theorem pair_mem_externalStarSupportGraph (V Q E U C Requests classifier copies localPoints action zero first v y : ZFSet.{u}) :
    ZFSet.pair v y ∈ externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first ↔
      v ∈ V ∧ y ∈ Q ∧ (ExternalCosetSupport E U C classifier copies zero v y ∨
        ExternalTileSupport E Q Requests localPoints action first v y) := by
  rw [externalStarSupportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, y', hy, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, hy, body⟩
  · rintro ⟨hv, hy, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, hy⟩, v, hv, y, hy, rfl, body⟩

namespace BoundedFormula

def externalCosetSupportFormula {n} (E U C classifier copies zero v y : Fin n) : BoundedFormula n :=
  exMem C (exMem E.succ (exMem U.succ.succ
    (.conj (orderedPairFormula v.succ.succ.succ zero.succ.succ.succ 2)
      (.conj (pairMembershipFormula 1 2 classifier.succ.succ.succ)
        (tripleMembershipFormula 1 0 y.succ.succ.succ copies.succ.succ.succ)))))

theorem truth_externalCosetSupportFormula {n} (E U C classifier copies zero v y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalCosetSupportFormula E U C classifier copies zero v y) env ↔
      ExternalCosetSupport (env E) (env U) (env C) (env classifier) (env copies) (env zero) (env v) (env y) := by
  simp only [externalCosetSupportFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalCosetSupport]
  rfl

def externalTileSupportFormula {n} (E Q Requests localPoints action first v y : Fin n) : BoundedFormula n :=
  exMem E (exMem Requests.succ (exMem Q.succ.succ
    (.conj (orderedRightTripleFormula v.succ.succ.succ first.succ.succ.succ 2 1)
      (.conj (pairMembershipFormula 1 0 localPoints.succ.succ.succ)
        (tripleMembershipFormula 2 0 y.succ.succ.succ action.succ.succ.succ)))))

theorem truth_externalTileSupportFormula {n} (E Q Requests localPoints action first v y : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (externalTileSupportFormula E Q Requests localPoints action first v y) env ↔
      ExternalTileSupport (env E) (env Q) (env Requests) (env localPoints) (env action) (env first) (env v) (env y) := by
  simp only [externalTileSupportFormula, truth_exMem, Truth, truth_orderedRightTripleFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, ExternalTileSupport]
  rfl

def externalStarSupportEntryFormula {n} (z V Q E U C Requests classifier copies localPoints action zero first : Fin n) : BoundedFormula n :=
  exMem V (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.disj (externalCosetSupportFormula E.succ.succ U.succ.succ C.succ.succ
      classifier.succ.succ copies.succ.succ zero.succ.succ 1 0)
      (externalTileSupportFormula E.succ.succ Q.succ.succ Requests.succ.succ
        localPoints.succ.succ action.succ.succ first.succ.succ 1 0))))

theorem truth_externalStarSupportEntryFormula {n} (z V Q E U C Requests classifier copies localPoints action zero first : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (externalStarSupportEntryFormula z V Q E U C Requests classifier copies localPoints action zero first) env ↔
      env z ∈ externalStarSupportGraph (env V) (env Q) (env E) (env U) (env C) (env Requests)
        (env classifier) (env copies) (env localPoints) (env action) (env zero) (env first) := by
  simp only [externalStarSupportEntryFormula, truth_exMem, Truth, truth_disj, truth_orderedPairFormula,
    truth_externalCosetSupportFormula, truth_externalTileSupportFormula, externalStarSupportGraph, ZFSet.mem_sep]
  refine ⟨fun body => ⟨?_, body⟩, And.right⟩
  obtain ⟨v, hv, y, hy, equal, _⟩ := body
  change env z = ZFSet.pair v y at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hv, hy⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem externalStarSupportGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {V Q E U C Requests classifier copies localPoints action zero first : ZFSet.{u}}
    (hV : V ∈ M.sets) (hQ : Q ∈ M.sets) (hE : E ∈ M.sets) (hU : U ∈ M.sets)
    (hC : C ∈ M.sets) (hRequests : Requests ∈ M.sets) (hClassifier : classifier ∈ M.sets)
    (hCopies : copies ∈ M.sets) (hLocal : localPoints ∈ M.sets) (hAction : action ∈ M.sets)
    (hZero : zero ∈ M.sets) (hFirst : first ∈ M.sets) :
    externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first ∈ M.sets := by
  let params := extend V (extend Q (extend E (extend U (extend C (extend Requests (extend classifier (extend copies (extend localPoints (extend action (extend zero (extend first (Fin.elim0))))))))))))
  have members : ∀ i, params i ∈ M.sets := Fin.cases hV (Fin.cases hQ (Fin.cases hE (Fin.cases hU (Fin.cases hC (Fin.cases hRequests (Fin.cases hClassifier (Fin.cases hCopies (Fin.cases hLocal (Fin.cases hAction (Fin.cases hZero (Fin.cases hFirst ((fun i => Fin.elim0 i)))))))))))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.externalStarSupportEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) params members
    (M.prod_mem pairing unions powers separation hV hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.externalStarSupportEntryFormula 0 1 2 3 4 5 6 7 8 9 10 11 12) (extend z params))
      (ZFSet.prod V Q) = externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_externalStarSupportEntryFormula]
    change (z ∈ ZFSet.prod V Q ∧ z ∈ externalStarSupportGraph V Q E U C Requests classifier copies localPoints action zero first) ↔ _
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

end TransitiveGround





def parentSupportGraph (V Q supports parents : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ v ∈ V, ∃ y ∈ Q, z = ZFSet.pair v y ∧ ZFSet.pair v y ∈ supports ∧
    ∃ p ∈ V, ZFSet.pair v p ∈ parents ∧ ZFSet.pair p y ∈ supports) (ZFSet.prod V Q)

def freshSupportGraph (V Q supports parents : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => z ∉ parentSupportGraph V Q supports parents) supports

theorem pair_mem_parentSupportGraph (V Q supports parents v y : ZFSet.{u}) :
    ZFSet.pair v y ∈ parentSupportGraph V Q supports parents ↔ v ∈ V ∧ y ∈ Q ∧
      ZFSet.pair v y ∈ supports ∧ ∃ p ∈ V, ZFSet.pair v p ∈ parents ∧ ZFSet.pair p y ∈ supports := by
  rw [parentSupportGraph, ZFSet.mem_sep]
  constructor
  · rintro ⟨_, v', hv, y', hy, equal, body⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨hv, hy, body⟩
  · rintro ⟨hv, hy, body⟩
    exact ⟨ZFSet.pair_mem_prod.2 ⟨hv, hy⟩, v, hv, y, hy, rfl, body⟩

theorem pair_mem_parentSupportGraph_of_parent {V Q supports parents v p y : ZFSet.{u}}
    (function : ZFSet.IsFunc V V parents) (parent : ZFSet.pair v p ∈ parents) :
    ZFSet.pair v y ∈ parentSupportGraph V Q supports parents ↔
      y ∈ Q ∧ ZFSet.pair v y ∈ supports ∧ ZFSet.pair p y ∈ supports := by
  have shape := ZFSet.pair_mem_prod.1 (function.1 parent)
  rw [pair_mem_parentSupportGraph]
  constructor
  · rintro ⟨_, hy, supported, p', _, atParent, supportedParent⟩
    have equal := (show FunctionGraphOn V parents from ⟨V, function⟩).unique atParent parent
    exact ⟨hy, supported, equal ▸ supportedParent⟩
  · rintro ⟨hy, supported, supportedParent⟩
    exact ⟨shape.1, hy, supported, p, shape.2, parent, supportedParent⟩

theorem pair_mem_freshSupportGraph (V Q supports parents v y : ZFSet.{u}) :
    ZFSet.pair v y ∈ freshSupportGraph V Q supports parents ↔
      ZFSet.pair v y ∈ supports ∧ ZFSet.pair v y ∉ parentSupportGraph V Q supports parents := by
  exact ZFSet.mem_sep

namespace BoundedFormula
def parentSupportEntryFormula {n} (z V Q supports parents : Fin n) : BoundedFormula n :=
  exMem V (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (.conj (pairMembershipFormula 1 0 supports.succ.succ)
      (exMem V.succ.succ (.conj (pairMembershipFormula 2 0 parents.succ.succ.succ)
        (pairMembershipFormula 0 1 supports.succ.succ.succ))))))

theorem truth_parentSupportEntryFormula {n} (z V Q supports parents : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (parentSupportEntryFormula z V Q supports parents) env ↔
      env z ∈ parentSupportGraph (env V) (env Q) (env supports) (env parents) := by
  simp only [parentSupportEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, parentSupportGraph, ZFSet.mem_sep]
  refine ⟨fun h => ⟨?_, h⟩, And.right⟩
  obtain ⟨v, hv, y, hy, equal, _⟩ := h
  change env z = ZFSet.pair v y at equal
  rw [equal]
  exact ZFSet.pair_mem_prod.2 ⟨hv, hy⟩
end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
variable {V Q supports parents : ZFSet.{u}} (hV : V ∈ M.sets) (hQ : Q ∈ M.sets)
variable (hSupports : supports ∈ M.sets) (hParents : parents ∈ M.sets)
include pairing unions powers separation hV hQ hSupports hParents

theorem parentSupportGraph_mem : parentSupportGraph V Q supports parents ∈ M.sets := by
  let params := extend V (extend Q (extend supports (extend parents Fin.elim0)))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.parentSupportEntryFormula 0 1 2 3 4) params
    (Fin.cases hV (Fin.cases hQ (Fin.cases hSupports (Fin.cases hParents (fun i => Fin.elim0 i)))))
    (M.prod_mem pairing unions powers separation hV hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.parentSupportEntryFormula 0 1 2 3 4) (extend z params)) (ZFSet.prod V Q) =
      parentSupportGraph V Q supports parents := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_parentSupportEntryFormula]
    exact ⟨And.right, fun hz => ⟨(ZFSet.mem_sep.1 hz).1, hz⟩⟩
  exact equal ▸ selected

theorem freshSupportGraph_mem : freshSupportGraph V Q supports parents ∈ M.sets := by
  have parentGround := M.parentSupportGraph_mem pairing unions powers separation hV hQ hSupports hParents
  exact M.bounded_separation_mem separation (BoundedFormula.neg (.mem 0 1))
    (extend (parentSupportGraph V Q supports parents) Fin.elim0)
    (Fin.cases parentGround (fun i => Fin.elim0 i)) hSupports

end TransitiveGround

end PartitionPilot.Forcing

end OAI
