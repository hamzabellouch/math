import OAI.SetTheory.PartitionPrinciple.Definability.PresentedGroupCodes

namespace OAI


namespace PartitionPilot.Forcing

open SetFormula
universe u

structure GroundDefinableFunction (M : TransitiveGround.{u}) {n : Nat}
    (f : (Fin n → ZFSet.{u}) → ZFSet.{u}) where
  formula : SetFormula (n + 1)
  closed : ∀ env, (∀ i, env i ∈ M.sets) → f env ∈ M.sets
  correct : ∀ env, (∀ i, env i ∈ M.sets) → ∀ z ∈ M.sets,
    Realize M.sets formula (extend z env) ↔ z = f env

namespace GroundDefinableFunction

def projection (M : TransitiveGround.{u}) {n : Nat} (j : Fin n) :
    GroundDefinableFunction M (fun env => env j) where
  formula := .equal 0 j.succ
  closed := fun _ members => members j
  correct := fun _ _ _ _ => Iff.rfl

def reindex {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}} (defined : GroundDefinableFunction M f)
    (slots : Fin k → Fin n) : GroundDefinableFunction M (fun env => f (fun j => env (slots j))) where
  formula := SetFormula.reindex (liftIndex slots) defined.formula
  closed := fun env members => defined.closed _ (fun j => members (slots j))
  correct := by
    intro env members z hz
    rw [realize_reindex, extend_liftIndex]
    exact defined.correct _ (fun j => members (slots j)) z hz

def compFormula {n k : Nat} (outer : SetFormula (k + 1))
    (inner : Fin k → SetFormula (n + 1)) : SetFormula (n + 1) :=
  exBlock k (.conj
    (conjBlock k (fun j => SetFormula.reindex
      (extend (prefixIndex (n + 1) k j) (fun i => suffixIndex (n + 1) k i.succ)) (inner j)))
    (SetFormula.reindex (extend (suffixIndex (n + 1) k 0) (prefixIndex (n + 1) k)) outer))

def comp {M : TransitiveGround.{u}} {n k : Nat}
    {f : (Fin k → ZFSet.{u}) → ZFSet.{u}}
    {g : Fin k → (Fin n → ZFSet.{u}) → ZFSet.{u}}
    (outer : GroundDefinableFunction M f) (inner : ∀ j, GroundDefinableFunction M (g j)) :
    GroundDefinableFunction M (fun env => f (fun j => g j env)) where
  formula := compFormula outer.formula (fun j => (inner j).formula)
  closed := fun env members => outer.closed _ (fun j => (inner j).closed env members)
  correct := by
    intro env members z hz
    rw [compFormula, realize_exBlock]
    constructor
    · rintro ⟨fields, fieldMembers, clauses, result⟩
      have each := (realize_conjBlock M.sets _ _ _).1 clauses
      have values : fields = fun j => g j env := by
        funext j
        have meaning := (realize_reindex M.sets _ _ _).1 (each j)
        rw [map_extend] at meaning
        simp only [extendMany_prefix, extendMany_suffix] at meaning
        exact ((inner j).correct env members (fields j) (fieldMembers j)).1 meaning
      have meaning := (realize_reindex M.sets _ _ _).1 result
      rw [map_extend] at meaning
      simp only [extendMany_prefix, extendMany_suffix] at meaning
      have output := (outer.correct fields fieldMembers z hz).1 meaning
      exact values ▸ output
    · intro equal
      let fields : Fin k → ZFSet.{u} := fun j => g j env
      have fieldMembers : ∀ j, fields j ∈ M.sets := fun j => (inner j).closed env members
      refine ⟨fields, fieldMembers, ?_, ?_⟩
      · apply (realize_conjBlock M.sets _ _ _).2
        intro j
        rw [realize_reindex, map_extend]
        simp only [extendMany_prefix, extendMany_suffix]
        exact ((inner j).correct env members (fields j) (fieldMembers j)).2 rfl
      · rw [realize_reindex, map_extend]
        simp only [extendMany_prefix, extendMany_suffix]
        exact (outer.correct fields fieldMembers z hz).2 equal

end GroundDefinableFunction

end PartitionPilot.Forcing


section

namespace PartitionPilot.Forcing.BoundedFormula

open SetFormula
universe u

def productElementFormula {n} (z a b : Fin n) : BoundedFormula n :=
  exMem a (exMem b.succ (orderedPairFormula z.succ.succ 1 0))

theorem truth_productElementFormula {n} (z a b : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (productElementFormula z a b) env ↔ env z ∈ ZFSet.prod (env a) (env b) := by
  simp only [productElementFormula, truth_exMem, truth_orderedPairFormula]
  exact ZFSet.mem_prod.symm

end PartitionPilot.Forcing.BoundedFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem mem_groundPower (B p : ZFSet.{u}) : p ∈ M.groundPower B ↔ p ∈ M.sets ∧ p ⊆ B := by
  rw [groundPower, ZFSet.mem_sep, ZFSet.mem_powerset]
  exact and_comm

theorem groundPower_mem (powers : Realize M.sets powerSet Fin.elim0)
    {B : ZFSet.{u}} (hB : B ∈ M.sets) : M.groundPower B ∈ M.sets := by
  obtain ⟨W, hW, spec⟩ := M.power_witness powers hB
  have eq : W = M.groundPower B := by
    apply ZFSet.ext
    intro p
    rw [M.mem_groundPower]
    exact ⟨fun hp => ⟨M.transitive hW hp, (spec p (M.transitive hW hp)).1 hp⟩,
      fun ⟨hp, subset⟩ => (spec p hp).2 subset⟩
  exact eq ▸ hW

theorem prod_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : ZFSet.prod A B ∈ M.sets := by
  obtain ⟨W, hW, bounds⟩ := M.exists_pair_bound pairing unions powers hA hB
  let params := extend A (extend B Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.productElementFormula 0 1 2).toFormula
    params (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))) hW
  have correct (z : ZFSet.{u}) (hz : z ∈ M.sets) :
      Realize M.sets (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params) ↔
        z ∈ ZFSet.prod A B :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hz (Fin.cases hA (Fin.cases hB (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_productElementFormula 0 1 2 _)
  have eq : ZFSet.sep (fun z => Realize M.sets
      (BoundedFormula.productElementFormula 0 1 2).toFormula (extend z params)) W = ZFSet.prod A B := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz, rel⟩
      exact (correct z (M.transitive hW hz)).1 rel
    · intro hz
      have hzW : z ∈ W := by
        obtain ⟨x, hx, y, hy, eq⟩ := ZFSet.mem_prod.1 hz
        exact eq.symm ▸ bounds x hx y hy
      exact ⟨hzW, (correct z (M.transitive hW hzW)).2 hz⟩
  exact eq ▸ selected

noncomputable def groundRelations (A B : ZFSet.{u}) : ZFSet.{u} := M.groundPower (ZFSet.prod A B)

theorem mem_groundRelations (A B p : ZFSet.{u}) :
    p ∈ M.groundRelations A B ↔ p ∈ M.sets ∧ p ⊆ ZFSet.prod A B := M.mem_groundPower _ _

theorem groundRelations_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : M.groundRelations A B ∈ M.sets :=
  M.groundPower_mem powers (M.prod_mem pairing unions powers separation hA hB)

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing

universe u

structure PartialFunctionCode (X Y p : ZFSet.{u}) : Prop where
  shape : p ⊆ ZFSet.prod X Y
  unique : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ p → y = z

namespace PartialFunctionCode

theorem empty (X Y : ZFSet.{u}) : PartialFunctionCode X Y ∅ :=
  ⟨ZFSet.empty_subset _, fun _ _ _ hp _ => False.elim (ZFSet.notMem_empty _ hp)⟩

theorem mono {X Y p q : ZFSet.{u}} (h : PartialFunctionCode X Y p) (subset : q ⊆ p) :
    PartialFunctionCode X Y q := ⟨fun _ hz => h.shape (subset hz), fun _ _ _ hy hz => h.unique _ _ _ (subset hy) (subset hz)⟩

theorem union {X Y p q : ZFSet.{u}} (hp : PartialFunctionCode X Y p) (hq : PartialFunctionCode X Y q)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) :
    PartialFunctionCode X Y (p ∪ q) := by
  refine ⟨fun _ hz => (ZFSet.mem_union.1 hz).elim (fun h => hp.shape h) (fun h => hq.shape h), ?_⟩
  intro x y z hy hz
  rcases ZFSet.mem_union.1 hy with hy | hy
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact hp.unique x y z hy hz
    · exact agree x y z hy hz
  · rcases ZFSet.mem_union.1 hz with hz | hz
    · exact (agree x z y hz hy).symm
    · exact hq.unique x y z hy hz

end PartialFunctionCode

namespace BoundedFormula

open SetFormula

def partialFunctionFormula {n} (x y p : Fin n) : BoundedFormula n :=
  .conj (relationBetweenFormula x y p) (.allMem x (.allMem y.succ (.allMem y.succ.succ
    (imp (.conj (pairMembershipFormula 2 1 p.succ.succ.succ)
      (pairMembershipFormula 2 0 p.succ.succ.succ)) (.equal 1 0)))))

theorem truth_partialFunctionFormula {n} (x y p : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (partialFunctionFormula x y p) env ↔ PartialFunctionCode (env x) (env y) (env p) := by
  simp only [partialFunctionFormula, Truth, truth_relationBetweenFormula, truth_imp, truth_pairMembershipFormula]
  constructor
  · rintro ⟨shape, unique⟩
    refine ⟨shape, ?_⟩
    intro a b c hb hc
    have ab := ZFSet.pair_mem_prod.1 (shape hb)
    have ac := ZFSet.pair_mem_prod.1 (shape hc)
    exact unique a ab.1 b ab.2 c ac.2 ⟨hb, hc⟩
  · intro h
    exact ⟨h.shape, fun a _ b _ c _ ⟨hb, hc⟩ => h.unique a b c hb hc⟩

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def definable_product
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) (env 1)) where
  formula := exactSetFormula 0 (BoundedFormula.productElementFormula 0 2 3).toFormula
  closed := fun _ members => M.prod_mem pairing unions powers separation (members 0) (members 1)
  correct := by
    intro env members z hz
    have ground := M.prod_mem pairing unions powers separation (members 0) (members 1)
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w hw
    exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))).trans
      (BoundedFormula.truth_productElementFormula 0 2 3 _)

noncomputable def definable_groundPower (powers : Realize M.sets powerSet Fin.elim0) :
    GroundDefinableFunction M (fun env : Fin 1 → ZFSet.{u} => M.groundPower (env 0)) where
  formula := exactSetFormula 0 (BoundedFormula.allMem 0 (.mem 0 3)).toFormula
  closed := fun _ members => M.groundPower_mem powers (members 0)
  correct := by
    intro env members z hz
    apply M.realize_exactSetFormula 0 _ (extend z env) hz
      (fun w h => ((M.mem_groundPower (env 0) w).1 h).1)
    intro w hw
    rw [M.mem_groundPower, and_iff_right hw]
    rw [BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))]
    rfl

noncomputable def definable_groundRelations
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => M.groundRelations (env 0) (env 1)) :=
  (M.definable_groundPower powers).comp
    (fun _ => M.definable_product pairing unions powers separation)

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u
namespace BoundedFormula

def familySetEntryFormula {n} (z T one : Fin n) : BoundedFormula n :=
  exMem T (orderedPairFormula z.succ 0 one.succ)

theorem truth_familySetEntryFormula {n} (z T one : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (familySetEntryFormula z T one) env ↔ env z ∈ ZFSet.prod (env T) {env one} := by
  rw [familySetEntryFormula, truth_exMem]
  simp only [truth_orderedPairFormula]
  change (∃ x ∈ env T, env z = ZFSet.pair x (env one)) ↔ _
  constructor
  · rintro ⟨x, hx, equal⟩
    rw [equal]
    exact ZFSet.pair_mem_prod.2 ⟨hx, ZFSet.mem_singleton.2 rfl⟩
  · intro member
    obtain ⟨x, hx, y, hy, equal⟩ := ZFSet.mem_prod.1 member
    have same := ZFSet.mem_singleton.1 hy
    rw [same] at equal
    exact ⟨x, hx, equal⟩

end BoundedFormula

namespace SetFormula

def familySetCodeFormula : SetFormula 3 :=
  exactSetFormula 0 (BoundedFormula.familySetEntryFormula 0 2 3).toFormula

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

def definable_familySetCode
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets) :
    GroundDefinableFunction M (fun env : Fin 2 → ZFSet.{u} => ZFSet.prod (env 0) {env 1}) where
  formula := familySetCodeFormula
  closed := fun _ members => M.prod_mem pairing unions powers separation (members 0)
    (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 1) (members 1))
  correct := by
    intro env members z hz
    have ground := M.prod_mem pairing unions powers separation (members 0)
      (by simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing (members 1) (members 1))
    apply M.realize_exactSetFormula 0 _ (extend z env) hz (fun _ h => M.transitive ground h)
    intro w hw
    exact (BoundedFormula.realize_toFormula M _ _ (Fin.cases hw (Fin.cases hz members))).trans
      (BoundedFormula.truth_familySetEntryFormula 0 2 3 _)

end TransitiveGround
end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

noncomputable def partialFunctions (X Y : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun p => PartialFunctionCode X Y p) (M.groundRelations X Y)

theorem mem_partialFunctions (X Y p : ZFSet.{u}) :
    p ∈ M.partialFunctions X Y ↔ p ∈ M.sets ∧ PartialFunctionCode X Y p := by
  rw [partialFunctions, ZFSet.mem_sep, M.mem_groundRelations]
  exact ⟨fun ⟨⟨ground, _⟩, code⟩ => ⟨ground, code⟩, fun ⟨ground, code⟩ => ⟨⟨ground, code.shape⟩, code⟩⟩

theorem partialFunctions_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {X Y : ZFSet.{u}} (hX : X ∈ M.sets) (hY : Y ∈ M.sets) : M.partialFunctions X Y ∈ M.sets := by
  have space := M.groundRelations_mem pairing unions powers separation hX hY
  let params := extend X (extend Y Fin.elim0)
  have selected := M.separation_mem separation (BoundedFormula.partialFunctionFormula 1 2 0).toFormula
    params (Fin.cases hX (Fin.cases hY (fun j => Fin.elim0 j))) space
  have correct (p : ZFSet.{u}) (hp : p ∈ M.sets) :
      Realize M.sets (BoundedFormula.partialFunctionFormula 1 2 0).toFormula (extend p params) ↔
        PartialFunctionCode X Y p :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hp (Fin.cases hX (Fin.cases hY (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_partialFunctionFormula 1 2 0 _)
  have eq : ZFSet.sep (fun p => Realize M.sets
      (BoundedFormula.partialFunctionFormula 1 2 0).toFormula (extend p params)) (M.groundRelations X Y) =
        M.partialFunctions X Y := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, M.mem_partialFunctions]
    constructor
    · rintro ⟨hp, rel⟩
      have ground := M.transitive space hp
      exact ⟨ground, (correct p ground).1 rel⟩
    · rintro ⟨ground, code⟩
      exact ⟨(M.mem_groundRelations X Y p).2 ⟨ground, code.shape⟩, (correct p ground).2 code⟩
  exact eq ▸ selected

theorem empty_mem_partialFunctions (X Y : ZFSet.{u}) (nonempty : M.sets.Nonempty) :
    (∅ : ZFSet.{u}) ∈ M.partialFunctions X Y :=
  (M.mem_partialFunctions X Y ∅).2 ⟨M.empty_mem nonempty, PartialFunctionCode.empty X Y⟩

theorem partialFunctions_restrict {X Y p q : ZFSet.{u}}
    (hp : p ∈ M.partialFunctions X Y) (hq : q ∈ M.sets) (subset : q ⊆ p) : q ∈ M.partialFunctions X Y := by
  exact (M.mem_partialFunctions X Y q).2 ⟨hq, ((M.mem_partialFunctions X Y p).1 hp).2.mono subset⟩

theorem partialFunctions_union
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {X Y p q : ZFSet.{u}} (hp : p ∈ M.partialFunctions X Y) (hq : q ∈ M.partialFunctions X Y)
    (agree : ∀ x y z, ZFSet.pair x y ∈ p → ZFSet.pair x z ∈ q → y = z) : p ∪ q ∈ M.partialFunctions X Y := by
  obtain ⟨hpM, hpCode⟩ := (M.mem_partialFunctions X Y p).1 hp
  obtain ⟨hqM, hqCode⟩ := (M.mem_partialFunctions X Y q).1 hq
  exact (M.mem_partialFunctions X Y (p ∪ q)).2
    ⟨M.binary_union_mem pairing unions hpM hqM, hpCode.union hqCode agree⟩

end PartitionPilot.Forcing.TransitiveGround

end OAI
