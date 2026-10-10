import OAI.SetTheory.PartitionPrinciple.Definability.NonemptyTupleFields

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def relationImage (D B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun y => ∃ x ∈ D, ZFSet.pair x y ∈ r) B

theorem mem_relationImage (D B r y : ZFSet.{u}) :
    y ∈ relationImage D B r ↔ y ∈ B ∧ ∃ x ∈ D, ZFSet.pair x y ∈ r := ZFSet.mem_sep

noncomputable def relationConverse (A B r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B,
    z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ r) (ZFSet.prod B A)

theorem mem_relationConverse (A B r z : ZFSet.{u}) :
    z ∈ relationConverse A B r ↔ ∃ x ∈ A, ∃ y ∈ B,
      z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ r := by
  rw [relationConverse, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, hx, y, hy, eq, rel⟩
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hy, hx⟩, x, hx, y, hy, eq, rel⟩

theorem pair_mem_relationConverse (A B r x y : ZFSet.{u}) :
    ZFSet.pair y x ∈ relationConverse A B r ↔
      x ∈ A ∧ y ∈ B ∧ ZFSet.pair x y ∈ r := by
  rw [mem_relationConverse]
  constructor
  · rintro ⟨a, ha, b, hb, eq, rel⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, rel⟩
  · rintro ⟨hx, hy, rel⟩
    exact ⟨x, hx, y, hy, rfl, rel⟩

noncomputable def relationCompose (A B C r f : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C,
    z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ r ∧ ZFSet.pair y w ∈ f) (ZFSet.prod A C)

theorem mem_relationCompose (A B C r f z : ZFSet.{u}) :
    z ∈ relationCompose A B C r f ↔ ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C,
      z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ r ∧ ZFSet.pair y w ∈ f := by
  rw [relationCompose, ZFSet.mem_sep]
  constructor
  · exact And.right
  · rintro ⟨x, hx, y, hy, w, hw, eq, xr, yf⟩
    exact ⟨eq.symm ▸ ZFSet.pair_mem_prod.2 ⟨hx, hw⟩, x, hx, y, hy, w, hw, eq, xr, yf⟩

theorem pair_mem_relationCompose (A B C r f x z : ZFSet.{u}) :
    ZFSet.pair x z ∈ relationCompose A B C r f ↔
      x ∈ A ∧ z ∈ C ∧ ∃ y ∈ B, ZFSet.pair x y ∈ r ∧ ZFSet.pair y z ∈ f := by
  rw [mem_relationCompose]
  constructor
  · rintro ⟨a, ha, y, hy, b, hb, eq, ar, yf⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 eq
    exact ⟨ha, hb, y, hy, ar, yf⟩
  · rintro ⟨hx, hz, y, hy, xr, yf⟩
    exact ⟨x, hx, y, hy, z, hz, rfl, xr, yf⟩

theorem relationImage_restrict (D B r : ZFSet.{u}) :
    relationImage D B (ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r) = relationImage D B r := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hy, x, hx, rel⟩
    exact ⟨hy, x, hx, (ZFSet.mem_sep.1 rel).1⟩
  · rintro ⟨hy, x, hx, rel⟩
    exact ⟨hy, x, hx, ZFSet.mem_sep.2 ⟨rel, ZFSet.pair_mem_prod.2 ⟨hx, hy⟩⟩⟩

namespace InjectionCode

theorem converse_image {A B r : ZFSet.{u}} (h : InjectionCode A B r) :
    InjectionCode (relationImage A B r) A (relationConverse A B r) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro z hz
    obtain ⟨x, hx, y, hy, eq, rel⟩ := (mem_relationConverse A B r z).1 hz
    exact eq.symm ▸ ZFSet.pair_mem_prod.2
      ⟨(mem_relationImage A B r y).2 ⟨hy, x, hx, rel⟩, hx⟩
  · intro y hy
    obtain ⟨hyB, x, hx, rel⟩ := (mem_relationImage A B r y).1 hy
    refine ⟨x, (pair_mem_relationConverse A B r x y).2 ⟨hx, hyB, rel⟩, ?_⟩
    intro z hz
    exact h.injective z x y ((pair_mem_relationConverse A B r z y).1 hz).2.2 rel
  · intro x y z hx hy
    have zx := (pair_mem_relationConverse A B r z x).1 hx
    have zy := (pair_mem_relationConverse A B r z y).1 hy
    obtain ⟨w, _, unique⟩ := h.function.2 z zx.1
    exact (unique x zx.2.2).trans (unique y zy.2.2).symm

theorem compose {A B C r f : ZFSet.{u}} (hr : InjectionCode A B r) (hf : InjectionCode B C f) :
    InjectionCode A C (relationCompose A B C r f) := by
  refine ⟨⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨y, xy, uniqueY⟩ := hr.function.2 x hx
    have hy := (ZFSet.pair_mem_prod.1 (hr.function.1 xy)).2
    obtain ⟨z, yz, uniqueZ⟩ := hf.function.2 y hy
    have hz := (ZFSet.pair_mem_prod.1 (hf.function.1 yz)).2
    refine ⟨z, (pair_mem_relationCompose A B C r f x z).2 ⟨hx, hz, y, hy, xy, yz⟩, ?_⟩
    intro w hw
    obtain ⟨_, _, y', _, xy', y'w⟩ := (pair_mem_relationCompose A B C r f x w).1 hw
    exact uniqueZ w (uniqueY y' xy' ▸ y'w)
  · intro x y z hx hy
    obtain ⟨_, _, a, _, xa, az⟩ := (pair_mem_relationCompose A B C r f x z).1 hx
    obtain ⟨_, _, b, _, yb, bz⟩ := (pair_mem_relationCompose A B C r f y z).1 hy
    exact hr.injective x y b (hf.injective a b z az bz ▸ xa) yb

end InjectionCode

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
universe u
variable {X Y f h : ZFSet.{u}}

theorem disjointFunction_union (first : ZFSet.IsFunc X X f) (second : ZFSet.IsFunc Y Y h)
    (apart : ∀ z, z ∈ X → z ∈ Y → False) : ZFSet.IsFunc (X ∪ Y) (X ∪ Y) (f ∪ h) := by
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases ZFSet.mem_union.1 hz with left | right
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (first.1 left)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_union.2 (Or.inl hx), ZFSet.mem_union.2 (Or.inl hy)⟩
    · obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (second.1 right)
      exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_union.2 (Or.inr hx), ZFSet.mem_union.2 (Or.inr hy)⟩
  · intro x hx
    rcases ZFSet.mem_union.1 hx with left | right
    · obtain ⟨y, entry, unique⟩ := first.2 x left
      refine ⟨y, ZFSet.mem_union.2 (Or.inl entry), ?_⟩
      intro z hz
      rcases ZFSet.mem_union.1 hz with same | other
      · exact unique z same
      · exact False.elim (apart x left (ZFSet.pair_mem_prod.1 (second.1 other)).1)
    · obtain ⟨y, entry, unique⟩ := second.2 x right
      refine ⟨y, ZFSet.mem_union.2 (Or.inr entry), ?_⟩
      intro z hz
      rcases ZFSet.mem_union.1 hz with other | same
      · exact False.elim (apart x (ZFSet.pair_mem_prod.1 (first.1 other)).1 right)
      · exact unique z same

theorem disjointInjection_union (first : InjectionCode X X f) (second : InjectionCode Y Y h)
    (apart : ∀ z, z ∈ X → z ∈ Y → False) : InjectionCode (X ∪ Y) (X ∪ Y) (f ∪ h) := by
  refine ⟨disjointFunction_union first.function second.function apart, ?_⟩
  intro x y z hx hy
  rcases ZFSet.mem_union.1 hx with left | right
  · rcases ZFSet.mem_union.1 hy with same | other
    · exact first.injective x y z left same
    · exact False.elim (apart z (ZFSet.pair_mem_prod.1 (first.function.1 left)).2
        (ZFSet.pair_mem_prod.1 (second.function.1 other)).2)
  · rcases ZFSet.mem_union.1 hy with other | same
    · exact False.elim (apart z (ZFSet.pair_mem_prod.1 (first.function.1 other)).2
        (ZFSet.pair_mem_prod.1 (second.function.1 right)).2)
    · exact second.injective x y z right same

theorem relationImage_union_graph (first : ZFSet.IsFunc X X f) (second : ZFSet.IsFunc Y Y h)
    (A : ZFSet.{u}) :
    relationImage A (X ∪ Y) (f ∪ h) = relationImage A X f ∪ relationImage A Y h := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨_, x, hx, entry⟩ := (mem_relationImage _ _ _ z).1 member
    rcases ZFSet.mem_union.1 entry with left | right
    · exact ZFSet.mem_union.2 (Or.inl ((mem_relationImage A X f z).2
        ⟨(ZFSet.pair_mem_prod.1 (first.1 left)).2, x, hx, left⟩))
    · exact ZFSet.mem_union.2 (Or.inr ((mem_relationImage A Y h z).2
        ⟨(ZFSet.pair_mem_prod.1 (second.1 right)).2, x, hx, right⟩))
  · intro member
    rcases ZFSet.mem_union.1 member with left | right
    · obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A X f z).1 left
      exact (mem_relationImage _ _ _ z).2 ⟨ZFSet.mem_union.2 (Or.inl hz), x, hx,
        ZFSet.mem_union.2 (Or.inl entry)⟩
    · obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A Y h z).1 right
      exact (mem_relationImage _ _ _ z).2 ⟨ZFSet.mem_union.2 (Or.inr hz), x, hx,
        ZFSet.mem_union.2 (Or.inr entry)⟩

theorem relationImage_source_selection (function : ZFSet.IsFunc X X f) (A : ZFSet.{u}) :
    relationImage A X f = relationImage (ZFSet.sep (fun z => z ∈ X) A) X f := by
  apply ZFSet.ext
  intro z
  rw [mem_relationImage, mem_relationImage]
  constructor
  · rintro ⟨hz, x, hx, entry⟩
    exact ⟨hz, x, ZFSet.mem_sep.2 ⟨hx, (ZFSet.pair_mem_prod.1 (function.1 entry)).1⟩, entry⟩
  · rintro ⟨hz, x, hx, entry⟩
    exact ⟨hz, x, (ZFSet.mem_sep.1 hx).1, entry⟩

theorem relationImage_source_union (A B X f : ZFSet.{u}) :
    relationImage (A ∪ B) X f = relationImage A X f ∪ relationImage B X f := by
  apply ZFSet.ext
  intro z
  constructor
  · intro member
    obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage _ _ _ z).1 member
    rcases ZFSet.mem_union.1 hx with left | right
    · exact ZFSet.mem_union.2 (Or.inl ((mem_relationImage A X f z).2 ⟨hz, x, left, entry⟩))
    · exact ZFSet.mem_union.2 (Or.inr ((mem_relationImage B X f z).2 ⟨hz, x, right, entry⟩))
  · intro member
    rcases ZFSet.mem_union.1 member with left | right
    · obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage A X f z).1 left
      exact (mem_relationImage _ _ _ z).2 ⟨hz, x, ZFSet.mem_union.2 (Or.inl hx), entry⟩
    · obtain ⟨hz, x, hx, entry⟩ := (mem_relationImage B X f z).1 right
      exact (mem_relationImage _ _ _ z).2 ⟨hz, x, ZFSet.mem_union.2 (Or.inr hx), entry⟩

theorem disjointRelationImage_selection (apart : ∀ z, z ∈ X → z ∈ Y → False)
    (A : ZFSet.{u}) :
    ZFSet.sep (fun z => z ∈ X) (relationImage A X f ∪ relationImage A Y h) =
      relationImage A X f := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_sep, ZFSet.mem_union]
  constructor
  · rintro ⟨left | right, member⟩
    · exact left
    · exact False.elim (apart z member ((mem_relationImage A Y h z).1 right).1)
  · intro member
    exact ⟨Or.inl member, ((mem_relationImage A X f z).1 member).1⟩

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def imageMemberFormula {n} (y d r : Fin n) : BoundedFormula n :=
  exMem d (pairMembershipFormula 0 y.succ r.succ)

def converseEntryFormula {n} (z a b r : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (.conj (orderedPairFormula z.succ.succ 0 1)
    (pairMembershipFormula 1 0 r.succ.succ)))

def composeEntryFormula {n} (z a b c r f : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (exMem c.succ.succ
    (.conj (orderedPairFormula z.succ.succ.succ 2 0)
      (.conj (pairMembershipFormula 2 1 r.succ.succ.succ)
        (pairMembershipFormula 1 0 f.succ.succ.succ)))))

theorem truth_imageMemberFormula {n} (y d r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (imageMemberFormula y d r) env ↔ ∃ x ∈ env d, ZFSet.pair x (env y) ∈ env r := by
  simp only [imageMemberFormula, truth_exMem, truth_pairMembershipFormula]
  rfl

theorem truth_converseEntryFormula {n} (z a b r : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (converseEntryFormula z a b r) env ↔ ∃ x ∈ env a, ∃ y ∈ env b,
      env z = ZFSet.pair y x ∧ ZFSet.pair x y ∈ env r := by
  simp only [converseEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

theorem truth_composeEntryFormula {n} (z a b c r f : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (composeEntryFormula z a b c r f) env ↔ ∃ x ∈ env a, ∃ y ∈ env b, ∃ w ∈ env c,
      env z = ZFSet.pair x w ∧ ZFSet.pair x y ∈ env r ∧ ZFSet.pair y w ∈ env f := by
  simp only [composeEntryFormula, truth_exMem, Truth,
    truth_orderedPairFormula, truth_pairMembershipFormula]
  rfl

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem bounded_separation_mem (separation : SeparationSchema M.sets)
    {n} (φ : BoundedFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {D : ZFSet.{u}} (hD : D ∈ M.sets) :
    ZFSet.sep (fun z => BoundedFormula.Truth φ (extend z params)) D ∈ M.sets := by
  have selected := M.separation_mem separation φ.toFormula params members hD
  have eq : ZFSet.sep (fun z => Realize M.sets φ.toFormula (extend z params)) D =
      ZFSet.sep (fun z => BoundedFormula.Truth φ (extend z params)) D := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, ZFSet.mem_sep]
    exact and_congr_right (fun hz => BoundedFormula.realize_toFormula M φ _
      (Fin.cases (M.transitive hD hz) members))
  exact eq ▸ selected

theorem relationImage_mem (separation : SeparationSchema M.sets)
    {D B r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets) :
    relationImage D B r ∈ M.sets := by
  let params := extend D (extend r Fin.elim0)
  have selected := M.bounded_separation_mem separation (BoundedFormula.imageMemberFormula 0 1 2)
    params (Fin.cases hD (Fin.cases hr (fun i => Fin.elim0 i))) hB
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.imageMemberFormula 0 1 2)
      (extend z params)) B = relationImage D B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, mem_relationImage]
    exact and_congr Iff.rfl (BoundedFormula.truth_imageMemberFormula 0 1 2 _)
  exact eq ▸ selected

theorem relationConverse_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B r : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hr : r ∈ M.sets) :
    relationConverse A B r ∈ M.sets := by
  let params := extend A (extend B (extend r Fin.elim0))
  have selected := M.bounded_separation_mem separation (BoundedFormula.converseEntryFormula 0 1 2 3)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hr (fun i => Fin.elim0 i))))
    (M.prod_mem pairing unions powers separation hB hA)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.converseEntryFormula 0 1 2 3)
      (extend z params)) (ZFSet.prod B A) = relationConverse A B r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationConverse, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_converseEntryFormula 0 1 2 3 _)
  exact eq ▸ selected

theorem relationCompose_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B C r f : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) (hC : C ∈ M.sets)
    (hr : r ∈ M.sets) (hf : f ∈ M.sets) : relationCompose A B C r f ∈ M.sets := by
  let params := extend A (extend B (extend C (extend r (extend f Fin.elim0))))
  have selected := M.bounded_separation_mem separation (BoundedFormula.composeEntryFormula 0 1 2 3 4 5)
    params (Fin.cases hA (Fin.cases hB (Fin.cases hC (Fin.cases hr
      (Fin.cases hf (fun i => Fin.elim0 i)))))) (M.prod_mem pairing unions powers separation hA hC)
  have eq : ZFSet.sep (fun z => BoundedFormula.Truth (BoundedFormula.composeEntryFormula 0 1 2 3 4 5)
      (extend z params)) (ZFSet.prod A C) = relationCompose A B C r f := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, relationCompose, ZFSet.mem_sep]
    exact and_congr Iff.rfl (BoundedFormula.truth_composeEntryFormula 0 1 2 3 4 5 _)
  exact eq ▸ selected

theorem groundEmbeddable_image
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B D N r : ZFSet.{u}} (hD : D ∈ M.sets) (hB : B ∈ M.sets) (hN : N ∈ M.sets)
    (hr : r ∈ M.sets) (code : InjectionCode A B r) (subset : D ⊆ A)
    (small : M.groundEmbeddable D N) : M.groundEmbeddable (relationImage D B r) N := by
  obtain ⟨f, hf, fcode⟩ := small
  let rD := ZFSet.sep (fun z => z ∈ ZFSet.prod D B) r
  have hrD := M.injection_restriction_mem separation hD hB hr
  have image := M.relationImage_mem separation hD hB hrD
  have inverse := M.relationConverse_mem pairing unions powers separation hD hB hrD
  have witness := M.relationCompose_mem pairing unions powers separation image hD hN inverse hf
  rw [← relationImage_restrict D B r]
  exact ⟨relationCompose (relationImage D B rD) D N (relationConverse D B rD) f,
    witness, (code.restrict subset).converse_image.compose fcode⟩

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing
universe u

theorem relationImage_commuting_square {A X N f f' action rename : ZFSet.{u}}
    (source : ZFSet.IsFunc A N f) (moved : ZFSet.IsFunc (relationImage A X action) N f')
    (assignments : ∀ x ∈ A, ∃ y ∈ X, ZFSet.pair x y ∈ action)
    (names : ZFSet.IsFunc N N rename)
    (commutes : ∀ x ∈ A, ∀ y z w,
      ZFSet.pair x y ∈ f → ZFSet.pair x z ∈ action →
      ZFSet.pair y w ∈ rename → ZFSet.pair z w ∈ f') :
    relationImage (relationImage A N f) N rename = relationImage (relationImage A X action) N f' := by
  apply ZFSet.ext
  intro w
  constructor
  · intro member
    obtain ⟨hw, y, hy, renamed⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_hyN, x, hx, requested⟩ := (mem_relationImage _ _ _ _).1 hy
    obtain ⟨z, hz, acted⟩ := assignments x hx
    exact (mem_relationImage _ _ _ _).2
      ⟨hw, z, (mem_relationImage _ _ _ _).2 ⟨hz, x, hx, acted⟩,
        commutes x hx y z w requested acted renamed⟩
  · intro member
    obtain ⟨hw, z, hz, requested'⟩ := (mem_relationImage _ _ _ _).1 member
    obtain ⟨_hzX, x, hx, acted⟩ := (mem_relationImage _ _ _ _).1 hz
    obtain ⟨y, requested, _⟩ := source.2 x hx
    have hy : y ∈ N := (ZFSet.pair_mem_prod.1 (source.1 requested)).2
    obtain ⟨w', renamed, _⟩ := names.2 y hy
    have requestedMoved := commutes x hx y z w' requested acted renamed
    obtain ⟨value, _edge, unique⟩ := moved.2 z hz
    have equal : w' = w := (unique w' requestedMoved).trans (unique w requested').symm
    exact (mem_relationImage _ _ _ _).2
      ⟨hw, y, (mem_relationImage _ _ _ _).2 ⟨hy, x, hx, requested⟩, equal ▸ renamed⟩

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
universe u

def flatCopyOrderGraph (E U Q classifier r : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
    ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
      ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
      ZFSet.pair (ZFSet.pair w y) b ∈ classifier) (ZFSet.prod Q Q)

def flatCopyActionGraph (E U Q classifier m : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ g ∈ E, ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair (ZFSet.pair g a) b ∧
    ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U, ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
      ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
      ZFSet.pair (ZFSet.pair v x) b ∈ classifier) (ZFSet.prod (ZFSet.prod E Q) Q)

theorem mem_flatCopyOrderGraph (E U Q classifier r z : ZFSet.{u}) :
    z ∈ flatCopyOrderGraph E U Q classifier r ↔
      ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair a b ∧
        ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
          ZFSet.pair (ZFSet.pair w y) b ∈ classifier := by
  rw [flatCopyOrderGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨a, ha, b, hb, equal, rest⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ha, hb⟩, a, ha, b, hb, equal, rest⟩

theorem mem_flatCopyActionGraph (E U Q classifier m z : ZFSet.{u}) :
    z ∈ flatCopyActionGraph E U Q classifier m ↔
      ∃ g ∈ E, ∃ a ∈ Q, ∃ b ∈ Q, z = ZFSet.pair (ZFSet.pair g a) b ∧
        ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U, ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧
          ZFSet.pair (ZFSet.pair v x) b ∈ classifier := by
  rw [flatCopyActionGraph, ZFSet.mem_sep]
  refine ⟨And.right, ?_⟩
  rintro ⟨g, hg, a, ha, b, hb, equal, rest⟩
  exact ⟨equal.symm ▸ ZFSet.pair_mem_prod.2 ⟨ZFSet.pair_mem_prod.2 ⟨hg, ha⟩, hb⟩,
    g, hg, a, ha, b, hb, equal, rest⟩

theorem pair_mem_flatCopyOrderGraph (E U Q classifier r a b : ZFSet.{u}) :
    ZFSet.pair a b ∈ flatCopyOrderGraph E U Q classifier r ↔
      a ∈ Q ∧ b ∈ Q ∧ ∃ w ∈ E, ∃ x ∈ U, ∃ y ∈ U, ZFSet.pair x y ∈ r ∧
        ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧ ZFSet.pair (ZFSet.pair w y) b ∈ classifier := by
  rw [mem_flatCopyOrderGraph]
  constructor
  · rintro ⟨a', ha, b', hb, equal, rest⟩
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 equal
    exact ⟨ha, hb, rest⟩
  · rintro ⟨ha, hb, rest⟩
    exact ⟨a, ha, b, hb, rfl, rest⟩

theorem pair_mem_flatCopyActionGraph (E U Q classifier m g a b : ZFSet.{u}) :
    ZFSet.pair (ZFSet.pair g a) b ∈ flatCopyActionGraph E U Q classifier m ↔
      g ∈ E ∧ a ∈ Q ∧ b ∈ Q ∧ ∃ w ∈ E, ∃ v ∈ E, ∃ x ∈ U,
        ZFSet.pair (ZFSet.pair g w) v ∈ m ∧
          ZFSet.pair (ZFSet.pair w x) a ∈ classifier ∧ ZFSet.pair (ZFSet.pair v x) b ∈ classifier := by
  rw [mem_flatCopyActionGraph]
  constructor
  · rintro ⟨g', hg, a', ha, b', hb, equal, rest⟩
    obtain ⟨ga, rfl⟩ := ZFSet.pair_inj.1 equal
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 ga
    exact ⟨hg, ha, hb, rest⟩
  · rintro ⟨hg, ha, hb, rest⟩
    exact ⟨g, hg, a, ha, b, hb, rfl, rest⟩

namespace BoundedFormula

def flatCopyOrderEntryFormula {n} (z E U Q classifier r : Fin n) : BoundedFormula n :=
  exMem Q (exMem Q.succ (.conj (orderedPairFormula z.succ.succ 1 0)
    (exMem E.succ.succ (exMem U.succ.succ.succ (exMem U.succ.succ.succ.succ
      (.conj (pairMembershipFormula 1 0 r.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 2 1 4 classifier.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 2 0 3 classifier.succ.succ.succ.succ.succ))))))))

theorem truth_flatCopyOrderEntryFormula {n} (z E U Q classifier r : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyOrderEntryFormula z E U Q classifier r) env ↔
      env z ∈ flatCopyOrderGraph (env E) (env U) (env Q) (env classifier) (env r) := by
  simp only [flatCopyOrderEntryFormula, truth_exMem, Truth, truth_orderedPairFormula,
    truth_pairMembershipFormula, truth_tripleMembershipFormula, mem_flatCopyOrderGraph]
  rfl

def flatCopyActionEntryFormula {n} (z E U Q classifier m : Fin n) : BoundedFormula n :=
  exMem E (exMem Q.succ (exMem Q.succ.succ (.conj (orderedTripleFormula z.succ.succ.succ 2 1 0)
    (exMem E.succ.succ.succ (exMem E.succ.succ.succ.succ (exMem U.succ.succ.succ.succ.succ
      (.conj (tripleMembershipFormula 5 2 1 m.succ.succ.succ.succ.succ.succ)
        (.conj (tripleMembershipFormula 2 0 4 classifier.succ.succ.succ.succ.succ.succ)
          (tripleMembershipFormula 1 0 3 classifier.succ.succ.succ.succ.succ.succ)))))))))

theorem truth_flatCopyActionEntryFormula {n} (z E U Q classifier m : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (flatCopyActionEntryFormula z E U Q classifier m) env ↔
      env z ∈ flatCopyActionGraph (env E) (env U) (env Q) (env classifier) (env m) := by
  simp only [flatCopyActionEntryFormula, truth_exMem, Truth, truth_orderedTripleFormula,
    truth_tripleMembershipFormula, mem_flatCopyActionGraph]
  rfl

end BoundedFormula





namespace SetFormula
def relationCompositionCodeFormula : SetFormula 6 :=
  exactSetFormula 0 (BoundedFormula.composeEntryFormula 0 2 3 4 5 6).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_relationCompositionCodeFormula (env : Fin 5 → ZFSet.{u})
    (members : ∀ j, env j ∈ M.sets) (z : ZFSet.{u}) (hz : z ∈ M.sets) :
    Realize M.sets relationCompositionCodeFormula (extend z env) ↔
      z = relationCompose (env 0) (env 1) (env 2) (env 3) (env 4) := by
  apply M.realize_exactSetFormula 0 _ _ hz
    (fun _ member => M.transitive (M.relationCompose_mem pairing unions powers separation
      (members 0) (members 1) (members 2) (members 3) (members 4)) member)
  intro w hw
  rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members)),
    BoundedFormula.truth_composeEntryFormula, mem_relationCompose]
  rfl

noncomputable def definable_relationCompose : GroundDefinableFunction M
    (fun env : Fin 5 → ZFSet.{u} => relationCompose (env 0) (env 1) (env 2) (env 3) (env 4)) where
  formula := relationCompositionCodeFormula
  closed := fun _ members => M.relationCompose_mem pairing unions powers separation
    (members 0) (members 1) (members 2) (members 3) (members 4)
  correct := M.realize_relationCompositionCodeFormula pairing unions powers separation

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def functionGraphRange (A f : ZFSet.{u}) : ZFSet.{u} :=
  relationImage A (⋃₀ ⋃₀ f) f

theorem mem_functionGraphRange (A f y : ZFSet.{u}) :
    y ∈ functionGraphRange A f ↔ ∃ x ∈ A, ZFSet.pair x y ∈ f := by
  rw [functionGraphRange, mem_relationImage]
  exact ⟨And.right, fun h => ⟨pair_second_mem_doubleUnion h.choose_spec.2, h⟩⟩

theorem functionGraphRange_function {A f : ZFSet.{u}} (function : FunctionGraphOn A f) :
    ZFSet.IsFunc A (functionGraphRange A f) f := by
  refine ⟨?_, function.to_isFunc.2⟩
  intro z hz
  obtain ⟨x, hx, y, rfl⟩ := function.shape z hz
  exact ZFSet.pair_mem_prod.2 ⟨hx, (mem_functionGraphRange A f y).2 ⟨x, hx, hz⟩⟩

theorem functionGraphRange_rank_le (A f : ZFSet.{u}) :
    ZFSet.rank (functionGraphRange A f) ≤ ZFSet.rank f := by
  have subset : functionGraphRange A f ⊆ ⋃₀ ⋃₀ f :=
    fun _ hy => (mem_relationImage _ _ _ _).1 hy |>.1
  exact (ZFSet.rank_mono subset).trans
    ((ZFSet.rank_sUnion_le (⋃₀ f)).trans (ZFSet.rank_sUnion_le f))

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem functionGraphRange_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    functionGraphRange A f ∈ M.sets :=
  M.relationImage_mem separation hA (M.union_mem unions (M.union_mem unions hf)) hf

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

include pairing unions powers separation in
theorem flatCopyOrderGraph_mem {E U Q classifier r : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hQ : Q ∈ M.sets)
    (hClassifier : classifier ∈ M.sets) (hr : r ∈ M.sets) :
    flatCopyOrderGraph E U Q classifier r ∈ M.sets := by
  let params := extend E (extend U (extend Q (extend classifier (extend r Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.flatCopyOrderEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hE (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hr (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation hQ hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.flatCopyOrderEntryFormula 0 1 2 3 4 5) (extend z params)) (ZFSet.prod Q Q) =
      flatCopyOrderGraph E U Q classifier r := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_flatCopyOrderEntryFormula]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

include pairing unions powers separation in
theorem flatCopyActionGraph_mem {E U Q classifier m : ZFSet.{u}}
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hQ : Q ∈ M.sets)
    (hClassifier : classifier ∈ M.sets) (hm : m ∈ M.sets) :
    flatCopyActionGraph E U Q classifier m ∈ M.sets := by
  let params := extend E (extend U (extend Q (extend classifier (extend m Fin.elim0))))
  have selected := M.bounded_separation_mem separation
    (BoundedFormula.flatCopyActionEntryFormula 0 1 2 3 4 5) params
    (Fin.cases hE (Fin.cases hU (Fin.cases hQ (Fin.cases hClassifier (Fin.cases hm (fun i => Fin.elim0 i))))))
    (M.prod_mem pairing unions powers separation (M.prod_mem pairing unions powers separation hE hQ) hQ)
  have equal : ZFSet.sep (fun z => BoundedFormula.Truth
      (BoundedFormula.flatCopyActionEntryFormula 0 1 2 3 4 5) (extend z params))
      (ZFSet.prod (ZFSet.prod E Q) Q) = flatCopyActionGraph E U Q classifier m := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, BoundedFormula.truth_flatCopyActionEntryFormula]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.1 h).1, h⟩⟩
  exact equal ▸ selected

end PartitionPilot.Forcing.TransitiveGround

end OAI
