import OAI.SetTheory.PartitionPrinciple.Forcing.IndexedTupleNames

namespace OAI


namespace PartitionPilot.Forcing
open SetFormula
universe u

namespace SetFormula

def orderedPairNameFamilyMemberFormula {n} (z one X Y : Fin n) : SetFormula n :=
  ex (.conj (.mem 0 X.succ) (ex (.conj (.mem 0 Y.succ.succ)
    (orderedPairNameCodeFormula z.succ.succ 1 0 one.succ.succ))))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

noncomputable def pairNameFamilyBound (one X Y : ZFSet.{u}) : ZFSet.{u} :=
  M.groundPower (ZFSet.prod (M.groundPower (ZFSet.prod (X ∪ Y) {one})) {one})

theorem pairNameFamilyBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    M.pairNameFamilyBound one X Y ∈ M.sets := by
  have hs : ({one} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hone hone
  exact M.groundPower_mem powers
    (M.prod_mem pairing unions powers separation
      (M.groundPower_mem powers (M.prod_mem pairing unions powers separation
        (M.binary_union_mem pairing unions hX hY) hs)) hs)

theorem orderedPairNameFamily_subset_bound
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    orderedPairNameFamily one X Y ⊆ M.pairNameFamilyBound one X Y := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := (mem_orderedPairNameFamily one X Y z).1 hz
  have hxM := M.transitive hX hx
  have hyM := M.transitive hY hy
  have hxB : x ∈ X ∪ Y := ZFSet.mem_union.2 (Or.inl hx)
  have hyB : y ∈ X ∪ Y := ZFSet.mem_union.2 (Or.inr hy)
  have first : pairNameCode one x x ∈ M.groundPower (ZFSet.prod (X ∪ Y) {one}) :=
    (M.mem_groundPower _ _).2 ⟨M.pairNameCode_mem pairing hone hxM hxM,
      pairNameCode_subset hxB hxB⟩
  have second : pairNameCode one x y ∈ M.groundPower (ZFSet.prod (X ∪ Y) {one}) :=
    (M.mem_groundPower _ _).2 ⟨M.pairNameCode_mem pairing hone hxM hyM,
      pairNameCode_subset hxB hyB⟩
  exact (M.mem_groundPower _ _).2
    ⟨M.orderedPairNameCode_mem pairing hone hxM hyM, pairNameCode_subset first second⟩

theorem realize_orderedPairNameFamilyMemberFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n} (z one X Y : Fin n) (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (orderedPairNameFamilyMemberFormula z one X Y) env ↔
      env z ∈ orderedPairNameFamily (env one) (env X) (env Y) := by
  rw [orderedPairNameFamilyMemberFormula, realize_ex, mem_orderedPairNameFamily]
  constructor
  · rintro ⟨x, hxM, hx, rest⟩
    obtain ⟨y, hyM, hy, named⟩ := (realize_ex M.sets _ _).1 rest
    exact ⟨x, hx, y, hy, (M.realize_orderedPairNameCodeFormula pairing
      z.succ.succ 1 0 one.succ.succ _ (Fin.cases hyM (Fin.cases hxM members))).1 named⟩
  · rintro ⟨x, hx, y, hy, equal⟩
    have hxM := M.transitive (members X) hx
    have hyM := M.transitive (members Y) hy
    refine ⟨x, hxM, hx, ?_⟩
    rw [realize_ex]
    exact ⟨y, hyM, hy, (M.realize_orderedPairNameCodeFormula pairing
      z.succ.succ 1 0 one.succ.succ _ (Fin.cases hyM (Fin.cases hxM members))).2 equal⟩

theorem orderedPairNameFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one X Y : ZFSet.{u}} (hone : one ∈ M.sets) (hX : X ∈ M.sets) (hY : Y ∈ M.sets) :
    orderedPairNameFamily one X Y ∈ M.sets := by
  let params := extend one (extend X (extend Y Fin.elim0))
  have members : ∀ j, params j ∈ M.sets :=
    Fin.cases hone (Fin.cases hX (Fin.cases hY (fun i => Fin.elim0 i)))
  have hBound := M.pairNameFamilyBound_mem pairing unions powers separation hone hX hY
  have subset := M.orderedPairNameFamily_subset_bound pairing hone hX hY
  have selected := M.separation_mem separation (orderedPairNameFamilyMemberFormula 0 1 2 3)
    params members hBound
  have equal : ZFSet.sep (fun z => Realize M.sets (orderedPairNameFamilyMemberFormula 0 1 2 3)
      (extend z params)) (M.pairNameFamilyBound one X Y) = orderedPairNameFamily one X Y := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, formula⟩
      exact (M.realize_orderedPairNameFamilyMemberFormula pairing 0 1 2 3 _
        (Fin.cases (M.transitive hBound hz) members)).1 formula
    · intro hz
      exact ⟨subset hz, (M.realize_orderedPairNameFamilyMemberFormula pairing 0 1 2 3 _
        (Fin.cases (M.transitive hBound (subset hz)) members)).2 hz⟩
  exact equal ▸ selected

theorem iteratedPairNameFamily_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {one T : ZFSet.{u}} (hone : one ∈ M.sets) (hT : T ∈ M.sets) (n : Nat) :
    iteratedPairNameFamily one T n ∈ M.sets := by
  induction n with
  | zero => exact hT
  | succ n ih => exact M.orderedPairNameFamily_mem pairing unions powers separation hone ih hT

end TransitiveGround
end PartitionPilot.Forcing

end OAI
