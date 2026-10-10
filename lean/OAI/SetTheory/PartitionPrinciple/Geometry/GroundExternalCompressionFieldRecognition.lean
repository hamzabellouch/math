import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionExternalTileOverlaps

namespace OAI

section

namespace PartitionPilot.Forcing
open SetFormula
universe u

theorem mem_externalCompressionField (I V F z : ZFSet.{u}) :
    z ∈ externalCompressionField I V F ↔
      ∃ i ∈ I, ∃ y ∈ V, z = ZFSet.pair (ZFSet.pair (natSetCode 0) i) y ∧
        ZFSet.pair i y ∈ F := by
  rw [externalCompressionField, mem_relationCompose]
  constructor
  · rintro ⟨x, _, i, hi, y, hy, equal, projection, entry⟩
    obtain ⟨t, ht, j, _, projected⟩ := (mem_productSecond _ _ _).1 projection
    have values := ZFSet.pair_inj.1 projected
    have zero : t = natSetCode 0 := ZFSet.mem_singleton.1 ht
    exact ⟨i, hi, y, hy, by simpa only [values.1, zero, ← values.2] using equal, entry⟩
  · rintro ⟨i, hi, y, hy, equal, entry⟩
    exact ⟨ZFSet.pair (natSetCode 0) i,
      ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hi⟩, i, hi, y, hy, equal,
      (mem_productSecond _ _ _).2 ⟨natSetCode 0, ZFSet.mem_singleton.2 rfl, i, hi, rfl⟩, entry⟩

namespace BoundedFormula

def externalCompressionFieldEntryFormula {n} (z I V F zero : Fin n) : BoundedFormula n :=
  exMem I (exMem V.succ (.conj (orderedTripleFormula z.succ.succ zero.succ.succ 1 0)
    (pairMembershipFormula 1 0 F.succ.succ)))

theorem truth_externalCompressionFieldEntryFormula {n} (z I V F zero : Fin n)
    (env : Fin n → ZFSet.{u}) (empty : env zero = natSetCode 0) :
    Truth (externalCompressionFieldEntryFormula z I V F zero) env ↔
      env z ∈ externalCompressionField (env I) (env V) (env F) := by
  simp only [externalCompressionFieldEntryFormula, truth_exMem, Truth,
    truth_orderedTripleFormula, truth_pairMembershipFormula]
  change (∃ i ∈ env I, ∃ y ∈ env V,
    env z = ZFSet.pair (ZFSet.pair (env zero) i) y ∧ ZFSet.pair i y ∈ env F) ↔ _
  rw [empty, mem_externalCompressionField]

end BoundedFormula

namespace SetFormula

def externalCompressionFieldFormula {n} (output I V F : Fin n) : SetFormula n :=
  ex (.conj (BoundedFormula.emptyFormula 0).toFormula
    (exactSetFormula output.succ
      (BoundedFormula.externalCompressionFieldEntryFormula 0 I.succ.succ V.succ.succ F.succ.succ 1).toFormula))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
variable (unions : Realize M.sets SetFormula.union Fin.elim0)
variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
include pairing unions powers separation

theorem realize_externalCompressionFieldFormula {n} (output I V F : Fin n)
    (env : Fin n → ZFSet.{u}) (members : ∀ j, env j ∈ M.sets) :
    Realize M.sets (externalCompressionFieldFormula output I V F) env ↔
      env output = externalCompressionField (env I) (env V) (env F) := by
  have meaning (zero : ZFSet.{u}) (hzero : zero ∈ M.sets) (empty : zero = natSetCode 0) :
      Realize M.sets (exactSetFormula output.succ
        (BoundedFormula.externalCompressionFieldEntryFormula 0 I.succ.succ V.succ.succ F.succ.succ 1).toFormula)
        (extend zero env) ↔ env output = externalCompressionField (env I) (env V) (env F) := by
    apply M.realize_exactBoundedSetFormula output.succ _ (extend zero env) (Fin.cases hzero members)
      (M.externalCompressionField_mem pairing unions powers separation (members I) (members V) (members F))
    intro z
    exact BoundedFormula.truth_externalCompressionFieldEntryFormula _ _ _ _ _ _ empty
  rw [externalCompressionFieldFormula, realize_ex]
  constructor
  · rintro ⟨zero, hzero, empty, correct⟩
    have zeroEq : zero = natSetCode 0 := (BoundedFormula.truth_emptyFormula 0 _).1
      ((BoundedFormula.realize_toFormula M _ _ (Fin.cases hzero members)).1 empty)
    exact (meaning zero hzero zeroEq).1 correct
  · intro equal
    have hzero : (natSetCode 0 : ZFSet.{u}) ∈ M.sets := M.empty_mem ⟨env I, members I⟩
    refine ⟨natSetCode 0, hzero, ?_, (meaning _ hzero rfl).2 equal⟩
    exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hzero members)).2
      ((BoundedFormula.truth_emptyFormula 0 _).2 rfl)

noncomputable def definable_externalCompressionField : GroundDefinableFunction M
    (fun env : Fin 3 → ZFSet.{u} => externalCompressionField (env 0) (env 1) (env 2)) where
  formula := externalCompressionFieldFormula 0 1 2 3
  closed := fun _ members => M.externalCompressionField_mem pairing unions powers separation
    (members 0) (members 1) (members 2)
  correct := fun env members z hz => M.realize_externalCompressionFieldFormula
    pairing unions powers separation 0 1 2 3 (extend z env) (Fin.cases hz members)

end TransitiveGround

end PartitionPilot.Forcing

end

end OAI
