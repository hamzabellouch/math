import OAI.SetTheory.PartitionPrinciple.Transfinite.GroundMainStageFromCodes

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def twoPointHeight (a b c d0 d1 : ZFSet.{u}) : ZFSet.{u} :=
  {ZFSet.pair a (ZFSet.pair c d0), ZFSet.pair b (ZFSet.pair c d1)}

theorem twoPointHeight_entry (a b c d0 d1 x y : ZFSet.{u}) :
    ZFSet.pair x y ∈ twoPointHeight a b c d0 d1 ↔
      (x = a ∧ y = ZFSet.pair c d0) ∨ (x = b ∧ y = ZFSet.pair c d1) := by
  simp only [twoPointHeight, ZFSet.mem_pair, ZFSet.pair_inj]

theorem twoPointHeight_function {a b c d0 d1 C D : ZFSet.{u}}
    (different : a ≠ b) (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    ZFSet.IsFunc {a, b} (ZFSet.prod C D) (twoPointHeight a b c d0 d1) := by
  constructor
  · intro z hz
    rcases ZFSet.mem_pair.1 hz with rfl | rfl
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_pair.2 (Or.inl rfl), ZFSet.pair_mem_prod.2 ⟨hc, h0⟩⟩
    · exact ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_pair.2 (Or.inr rfl), ZFSet.pair_mem_prod.2 ⟨hc, h1⟩⟩
  · intro x hx
    rcases ZFSet.mem_pair.1 hx with hx | hx
    · subst x
      refine ⟨ZFSet.pair c d0, ZFSet.mem_pair.2 (Or.inl rfl), ?_⟩
      intro y hy
      rcases (twoPointHeight_entry a b c d0 d1 a y).1 hy with ⟨_, equal⟩ | ⟨bad, _⟩
      · exact equal
      · exact False.elim (different bad)
    · subst x
      refine ⟨ZFSet.pair c d1, ZFSet.mem_pair.2 (Or.inr rfl), ?_⟩
      intro y hy
      rcases (twoPointHeight_entry a b c d0 d1 b y).1 hy with ⟨bad, _⟩ | ⟨_, equal⟩
      · exact False.elim (different bad.symm)
      · exact equal

theorem twoPointHeight_strict {a b c d0 d1 C D rD : ZFSet.{u}}
    (different : a ≠ b) (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D)
    (gap : ZFSet.pair d0 d1 ∈ rD) :
    StrictLexHeightCode {a, b} C D
      {ZFSet.pair a a, ZFSet.pair a b, ZFSet.pair b b} (twoPointHeight a b c d0 d1) rD := by
  refine ⟨twoPointHeight_function different hc h0 h1, ?_⟩
  intro x _ y _ c' q d' v ordered ne hx hy
  have endpoints : x = a ∧ y = b := by
    simp only [ZFSet.mem_insert_iff, ZFSet.mem_singleton, ZFSet.pair_inj] at ordered
    rcases ordered with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact False.elim (ne rfl)
    · exact ⟨rfl, rfl⟩
    · exact False.elim (ne rfl)
  obtain ⟨hxEq, hyEq⟩ := endpoints
  subst x y
  have first : ZFSet.pair c' q = ZFSet.pair c d0 := by
    rcases (twoPointHeight_entry a b c d0 d1 a _).1 hx with ⟨_, h⟩ | ⟨bad, _⟩
    · exact h
    · exact False.elim (different bad)
  have second : ZFSet.pair d' v = ZFSet.pair c d1 := by
    rcases (twoPointHeight_entry a b c d0 d1 b _).1 hy with ⟨bad, _⟩ | ⟨_, h⟩
    · exact False.elim (different bad.symm)
    · exact h
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 first
  obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.1 second
  exact Or.inr ⟨rfl, gap⟩

theorem twoPointHeight_image {a b c d0 d1 C D : ZFSet.{u}}
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    relationImage {a, b} (ZFSet.prod C D) (twoPointHeight a b c d0 d1) =
      {ZFSet.pair c d0, ZFSet.pair c d1} := by
  apply ZFSet.ext
  intro y
  rw [mem_relationImage, ZFSet.mem_pair]
  constructor
  · rintro ⟨_, x, _, entry⟩
    exact ((twoPointHeight_entry a b c d0 d1 x y).1 entry).elim
      (fun h => Or.inl h.2) (fun h => Or.inr h.2)
  · rintro (rfl | rfl)
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hc, h0⟩, a, ZFSet.mem_pair.2 (Or.inl rfl),
        ZFSet.mem_pair.2 (Or.inl rfl)⟩
    · exact ⟨ZFSet.pair_mem_prod.2 ⟨hc, h1⟩, b, ZFSet.mem_pair.2 (Or.inr rfl),
        ZFSet.mem_pair.2 (Or.inr rfl)⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem twoPointHeight_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {a b c d0 d1 : ZFSet.{u}} (ha : a ∈ M.sets) (hb : b ∈ M.sets)
    (hc : c ∈ M.sets) (h0 : d0 ∈ M.sets) (h1 : d1 ∈ M.sets) :
    twoPointHeight a b c d0 d1 ∈ M.sets :=
  M.unorderedPair_mem pairing (M.orderedPair_mem pairing ha (M.orderedPair_mem pairing hc h0))
    (M.orderedPair_mem pairing hb (M.orderedPair_mem pairing hc h1))

theorem unorderedPair_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {a b : ZFSet.{u}} (ha : a ∈ M.sets) (hb : b ∈ M.sets) :
    M.groundEmbeddable ({a, b} : ZFSet.{u}) ZFSet.omega := by
  have nonempty : M.sets.Nonempty := ⟨a, ha⟩
  have zero := M.empty_mem nonempty
  have single := M.groundEmbeddable_insert pairing unions powers separation infinite zero hb
    (M.empty_groundEmbeddable ZFSet.omega nonempty)
  exact M.groundEmbeddable_insert pairing unions powers separation infinite
    (M.insert_mem pairing unions hb zero) ha single

theorem twoPointHeight_range_countable
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {a b c d0 d1 C D : ZFSet.{u}} (hC : C ∈ M.sets) (hD : D ∈ M.sets)
    (hc : c ∈ C) (h0 : d0 ∈ D) (h1 : d1 ∈ D) :
    M.groundEmbeddable (relationImage {a, b} (ZFSet.prod C D)
      (twoPointHeight a b c d0 d1)) ZFSet.omega := by
  rw [twoPointHeight_image hc h0 h1]
  exact M.unorderedPair_countable pairing unions powers separation infinite
    (M.orderedPair_mem pairing (M.transitive hC hc) (M.transitive hD h0))
    (M.orderedPair_mem pairing (M.transitive hC hc) (M.transitive hD h1))

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
