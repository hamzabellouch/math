import OAI.SetTheory.PartitionPrinciple.Models.GroundInjectionRestrictions

namespace OAI


namespace PartitionPilot.Forcing

universe u

noncomputable def nonemptyTupleCode : (k : Nat) → (Fin (k + 1) → ZFSet.{u}) → ZFSet.{u}
  | 0, fields => fields 0
  | k + 1, fields => ZFSet.pair (fields 0) (nonemptyTupleCode k (fun i => fields i.succ))

theorem nonemptyTupleCode_injective (k : Nat) : Function.Injective (nonemptyTupleCode.{u} k) := by
  induction k with
  | zero =>
    intro fields fields' equal
    funext i
    exact Fin.cases equal (fun j => Fin.elim0 j) i
  | succ k ih =>
    intro fields fields' equal
    obtain ⟨head, tail⟩ := ZFSet.pair_inj.1 equal
    have same := ih tail
    funext i
    exact Fin.cases head (fun j => congrFun same j) i

namespace BoundedFormula

open SetFormula

def nonemptyTupleFormula : (k : Nat) → {n : Nat} →
    Fin n → (Fin (k + 1) → Fin n) → BoundedFormula n
  | 0, _, z, fields => .equal z (fields 0)
  | k + 1, _, z, fields => exMem z (exMem 0
      (.conj (orderedPairFormula z.succ.succ (fields 0).succ.succ 0)
        (nonemptyTupleFormula k 0 (fun i => (fields i.succ).succ.succ))))

theorem truth_nonemptyTupleFormula (k : Nat) {n : Nat} (z : Fin n)
    (fields : Fin (k + 1) → Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (nonemptyTupleFormula k z fields) env ↔
      env z = nonemptyTupleCode k (fun i => env (fields i)) := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    simp only [nonemptyTupleFormula, truth_exMem, Truth, truth_orderedPairFormula, ih]
    change (∃ a ∈ env z, ∃ b ∈ a, env z = ZFSet.pair (env (fields 0)) b ∧
      b = nonemptyTupleCode k (fun i => env (fields i.succ))) ↔ _
    constructor
    · rintro ⟨_, _, b, _, outer, tail⟩
      rw [outer, tail]
      rfl
    · intro equal
      let tail := nonemptyTupleCode k (fun i => env (fields i.succ))
      have outer : env z = ZFSet.pair (env (fields 0)) tail := equal
      refine ⟨{env (fields 0), tail}, ?_, tail, ZFSet.mem_pair.2 (Or.inr rfl), outer, rfl⟩
      rw [outer]
      exact ZFSet.mem_pair.2 (Or.inr rfl)

end BoundedFormula

namespace TransitiveGround

open SetFormula
variable (M : TransitiveGround.{u})

theorem nonemptyTupleCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (k : Nat) (fields : Fin (k + 1) → ZFSet.{u}) (ground : ∀ i, fields i ∈ M.sets) :
    nonemptyTupleCode k fields ∈ M.sets := by
  induction k with
  | zero => exact ground 0
  | succ k ih => exact M.orderedPair_mem pairing (ground 0) (ih _ (fun i => ground i.succ))

theorem nonemptyTupleCode_field_mem (k : Nat) (fields : Fin (k + 1) → ZFSet.{u})
    (ground : nonemptyTupleCode k fields ∈ M.sets) : ∀ i, fields i ∈ M.sets := by
  induction k with
  | zero => exact Fin.cases ground (fun i => Fin.elim0 i)
  | succ k ih =>
    have pairGround : ZFSet.pair (fields 0) (nonemptyTupleCode k (fun i => fields i.succ)) ∈ M.sets := ground
    have both : ({fields 0, nonemptyTupleCode k (fun i => fields i.succ)} : ZFSet.{u}) ∈ M.sets :=
      M.transitive pairGround (ZFSet.mem_pair.2 (Or.inr rfl))
    have head := M.transitive both (ZFSet.mem_pair.2 (Or.inl rfl))
    have tail := M.transitive both (ZFSet.mem_pair.2 (Or.inr rfl))
    exact Fin.cases head (ih _ tail)

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.BoundedFormula
open SetFormula
universe u

def reindex : {n m : Nat} → (Fin n → Fin m) → BoundedFormula n → BoundedFormula m
  | _, _, f, .equal i j => .equal (f i) (f j)
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .neg φ => .neg (reindex f φ)
  | _, _, f, .conj φ ψ => .conj (reindex f φ) (reindex f ψ)
  | _, _, f, .allMem b φ => .allMem (f b) (reindex (liftIndex f) φ)

theorem truth_reindex {n m} (f : Fin n → Fin m) (φ : BoundedFormula n)
    (env : Fin m → ZFSet.{u}) :
    Truth (reindex f φ) env ↔ Truth φ (fun i => env (f i)) := by
  induction φ generalizing m with
  | equal i j => rfl
  | mem i j => rfl
  | neg φ ih => exact not_congr (ih f env)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ f env) (ihψ f env)
  | allMem b φ ih =>
    change (∀ x ∈ env (f b), Truth (reindex (liftIndex f) φ) (extend x env)) ↔ _
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    rw [ih, extend_liftIndex]

def exPairFields {n} (z : Fin n) (body : BoundedFormula (n + 2)) : BoundedFormula n :=
  exMem z (exMem 0 (exMem z.succ.succ (exMem 0
    (.conj (orderedPairFormula z.succ.succ.succ.succ 2 0)
      (reindex (Fin.cases 0 (Fin.cases 2 (fun i => i.succ.succ.succ.succ))) body)))))

theorem truth_exPairFields {n} (z : Fin n) (body : BoundedFormula (n + 2))
    (env : Fin n → ZFSet.{u}) :
    Truth (exPairFields z body) env ↔
      ∃ x y, env z = ZFSet.pair x y ∧ Truth body (extend y (extend x env)) := by
  simp only [exPairFields, truth_exMem, Truth, truth_orderedPairFormula, truth_reindex]
  have rearrange (a x b y : ZFSet.{u}) :
      (fun i => extend y (extend b (extend x (extend a env)))
        (Fin.cases 0 (Fin.cases 2 (fun j => j.succ.succ.succ.succ)) i)) =
        extend y (extend x env) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl
  simp only [rearrange]
  change (∃ a ∈ env z, ∃ x ∈ a, ∃ b ∈ env z, ∃ y ∈ b,
    env z = ZFSet.pair x y ∧ Truth body (extend y (extend x env))) ↔ _
  constructor
  · rintro ⟨a, _, x, _, b, _, y, _, equal, holds⟩
    exact ⟨x, y, equal, holds⟩
  · rintro ⟨x, y, equal, holds⟩
    have both : ({x, y} : ZFSet.{u}) ∈ env z := by
      rw [equal]
      exact ZFSet.mem_pair.2 (Or.inr rfl)
    exact ⟨{x,y}, both, x, ZFSet.mem_pair.2 (Or.inl rfl),
      {x,y}, both, y, ZFSet.mem_pair.2 (Or.inr rfl), equal, holds⟩

def tupleShapeFormula : (k : Nat) → {n : Nat} → Fin n → BoundedFormula n
  | 0, _, z => .equal z z
  | k + 1, _, z => exPairFields z (tupleShapeFormula k 0)

theorem truth_tupleShapeFormula (k : Nat) {n} (z : Fin n) (env : Fin n → ZFSet.{u}) :
    Truth (tupleShapeFormula k z) env ↔ ∃ fields, env z = nonemptyTupleCode k fields := by
  induction k generalizing n with
  | zero =>
    change env z = env z ↔ ∃ fields : Fin 1 → ZFSet.{u}, env z = fields 0
    exact ⟨fun _ => ⟨fun _ => env z, rfl⟩, fun _ => rfl⟩
  | succ k ih =>
    rw [tupleShapeFormula, truth_exPairFields]
    constructor
    · rintro ⟨x, y, equal, shape⟩
      obtain ⟨fields, tail⟩ := (ih 0 (extend y (extend x env))).1 shape
      refine ⟨Fin.cases x fields, ?_⟩
      change env z = ZFSet.pair x (nonemptyTupleCode k fields)
      exact equal.trans (congrArg (ZFSet.pair x) tail)
    · rintro ⟨fields, equal⟩
      exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), equal,
        (ih 0 _).2 ⟨fun i => fields i.succ, rfl⟩⟩

end PartitionPilot.Forcing.BoundedFormula



namespace PartitionPilot.Forcing
universe u

noncomputable def refinementIndexCode (level C E U Rf Rc : ZFSet.{u}) : ZFSet.{u} :=
  nonemptyTupleCode 5 ![level, C, E, U, Rf, Rc]

theorem refinementIndexCode_eq_iff (level C E U Rf Rc level' C' E' U' Rf' Rc' : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc = refinementIndexCode level' C' E' U' Rf' Rc' ↔
      level = level' ∧ C = C' ∧ E = E' ∧ U = U' ∧ Rf = Rf' ∧ Rc = Rc' := by
  simp only [refinementIndexCode, nonemptyTupleCode, Matrix.cons_val_zero,
    Matrix.cons_val_succ, ZFSet.pair_inj]

noncomputable def refinementIndexBound (L P V W : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod L (ZFSet.prod P (ZFSet.prod P (ZFSet.prod V (ZFSet.prod W W))))

theorem mem_refinementIndexBound (L P V W z : ZFSet.{u}) :
    z ∈ refinementIndexBound L P V W ↔
      ∃ level ∈ L, ∃ C ∈ P, ∃ E ∈ P, ∃ U ∈ V, ∃ Rf ∈ W, ∃ Rc ∈ W,
        z = refinementIndexCode level C E U Rf Rc := by
  simp only [refinementIndexBound, ZFSet.mem_prod]
  constructor
  · rintro ⟨level, hlevel, rest, ⟨C, hC, rest', ⟨E, hE, rest'', ⟨U, hU,
      rest''', ⟨Rf, hRf, Rc, hRc, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩
    exact ⟨level, hlevel, C, hC, E, hE, U, hU, Rf, hRf, Rc, hRc, rfl⟩
  · rintro ⟨level, hlevel, C, hC, E, hE, U, hU, Rf, hRf, Rc, hRc, rfl⟩
    exact ⟨level, hlevel, _, ⟨C, hC, _, ⟨E, hE, _, ⟨U, hU, _,
      ⟨Rf, hRf, Rc, hRc, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem refinementIndexCode_mem_bound (L P V W level C E U Rf Rc : ZFSet.{u}) :
    refinementIndexCode level C E U Rf Rc ∈ refinementIndexBound L P V W ↔
      level ∈ L ∧ C ∈ P ∧ E ∈ P ∧ U ∈ V ∧ Rf ∈ W ∧ Rc ∈ W := by
  rw [mem_refinementIndexBound]
  constructor
  · rintro ⟨l, hl, c, hc, e, he, a, ha, r, hr, t, ht, equal⟩
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := (refinementIndexCode_eq_iff _ _ _ _ _ _ _ _ _ _ _ _).1 equal
    exact ⟨hl, hc, he, ha, hr, ht⟩
  · rintro ⟨hl, hc, he, hu, hf, hr⟩
    exact ⟨level, hl, C, hc, E, he, U, hu, Rf, hf, Rc, hr, rfl⟩

namespace BoundedFormula

def refinementIndexFormula {n : Nat} (z level C E U Rf Rc : Fin n) : BoundedFormula n :=
  nonemptyTupleFormula 5 z ![level, C, E, U, Rf, Rc]

theorem truth_refinementIndexFormula {n : Nat} (z level C E U Rf Rc : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (refinementIndexFormula z level C E U Rf Rc) env ↔
      env z = refinementIndexCode (env level) (env C) (env E) (env U) (env Rf) (env Rc) := by
  rw [refinementIndexFormula, truth_nonemptyTupleFormula]
  rfl

end BoundedFormula

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround
open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem refinementIndexCode_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {level C E U Rf Rc : ZFSet.{u}} (hl : level ∈ M.sets) (hC : C ∈ M.sets)
    (hE : E ∈ M.sets) (hU : U ∈ M.sets) (hf : Rf ∈ M.sets) (hc : Rc ∈ M.sets) :
    refinementIndexCode level C E U Rf Rc ∈ M.sets :=
  M.nonemptyTupleCode_mem pairing 5 _
    (Fin.cases hl (Fin.cases hC (Fin.cases hE (Fin.cases hU
      (Fin.cases hf (Fin.cases hc (fun j => Fin.elim0 j)))))))

theorem refinementIndexCode_fields_mem {level C E U Rf Rc : ZFSet.{u}}
    (ground : refinementIndexCode level C E U Rf Rc ∈ M.sets) :
    level ∈ M.sets ∧ C ∈ M.sets ∧ E ∈ M.sets ∧ U ∈ M.sets ∧
      Rf ∈ M.sets ∧ Rc ∈ M.sets := by
  have fields := M.nonemptyTupleCode_field_mem 5 ![level, C, E, U, Rf, Rc] ground
  exact ⟨fields 0, fields 1, fields 2, fields 3, fields 4, fields 5⟩

theorem refinementIndexBound_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {L P V W : ZFSet.{u}} (hL : L ∈ M.sets) (hP : P ∈ M.sets)
    (hV : V ∈ M.sets) (hW : W ∈ M.sets) : refinementIndexBound L P V W ∈ M.sets :=
  M.prod_mem pairing unions powers separation hL
    (M.prod_mem pairing unions powers separation hP
      (M.prod_mem pairing unions powers separation hP
        (M.prod_mem pairing unions powers separation hV
          (M.prod_mem pairing unions powers separation hW hW))))

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
universe u

noncomputable def refinementIndexFieldGraph (I B : ZFSet.{u}) (j : Fin 6) : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ fields : Fin 6 → ZFSet.{u},
    nonemptyTupleCode 5 fields ∈ I ∧ z = ZFSet.pair (nonemptyTupleCode 5 fields) (fields j))
      (ZFSet.prod I B)

theorem pair_mem_refinementIndexFieldGraph (I B x y : ZFSet.{u}) (j : Fin 6) :
    ZFSet.pair x y ∈ refinementIndexFieldGraph I B j ↔
      x ∈ I ∧ y ∈ B ∧ ∃ fields : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 fields ∧ y = fields j := by
  rw [refinementIndexFieldGraph, ZFSet.mem_sep, ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨hx, hy⟩, fields, _, eq⟩
    exact ⟨hx, hy, fields, ZFSet.pair_inj.1 eq⟩
  · rintro ⟨hx, hy, fields, rfl, rfl⟩
    exact ⟨⟨hx, hy⟩, fields, hx, rfl⟩

theorem refinementIndexFieldGraph_entry (I B : ZFSet.{u}) (fields : Fin 6 → ZFSet.{u})
    (j : Fin 6) (y : ZFSet.{u}) :
    ZFSet.pair (nonemptyTupleCode 5 fields) y ∈ refinementIndexFieldGraph I B j ↔
      nonemptyTupleCode 5 fields ∈ I ∧ y ∈ B ∧ y = fields j := by
  rw [pair_mem_refinementIndexFieldGraph]
  constructor
  · rintro ⟨hi, hy, fields', equal, value⟩
    have same := nonemptyTupleCode_injective 5 equal
    exact ⟨hi, hy, value.trans (congrFun same j).symm⟩
  · rintro ⟨hi, hy, value⟩
    exact ⟨hi, hy, fields, rfl, value⟩

theorem refinementIndexFieldGraph_function (I B : ZFSet.{u}) (j : Fin 6)
    (fields : ∀ x ∈ I, ∃ v : Fin 6 → ZFSet.{u}, x = nonemptyTupleCode 5 v ∧ v j ∈ B) :
    ZFSet.IsFunc I B (refinementIndexFieldGraph I B j) := by
  refine ⟨fun _ hz => (ZFSet.mem_sep.1 hz).1, ?_⟩
  intro x hx
  obtain ⟨v, rfl, hv⟩ := fields x hx
  refine ⟨v j, (refinementIndexFieldGraph_entry I B v j _).2 ⟨hx, hv, rfl⟩, ?_⟩
  intro y hy
  exact ((refinementIndexFieldGraph_entry I B v j y).1 hy).2.2

namespace SetFormula

def refinementIndexFieldFormula {n} (z I : Fin n) (j : Fin 6) : SetFormula n :=
  let old := suffixIndex n 7
  let w := prefixIndex n 7
  exBlock 7 (.conj (.mem (w 0) (old I))
    (.conj (BoundedFormula.nonemptyTupleFormula 5 (w 0) (fun k => w k.succ)).toFormula
      (BoundedFormula.orderedPairFormula (old z) (w 0) (w j.succ)).toFormula))

end SetFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem realize_refinementIndexFieldFormula {n} (z I : Fin n) (j : Fin 6)
    (env : Fin n → ZFSet.{u}) (members : ∀ k, env k ∈ M.sets) :
    Realize M.sets (refinementIndexFieldFormula z I j) env ↔
      ∃ fields : Fin 6 → ZFSet.{u}, nonemptyTupleCode 5 fields ∈ env I ∧
        env z = ZFSet.pair (nonemptyTupleCode 5 fields) (fields j) := by
  rw [refinementIndexFieldFormula, realize_exBlock]
  have actual (w : Fin 7 → ZFSet.{u}) (ground : ∀ k, w k ∈ M.sets) :
      Realize M.sets (.conj (.mem (prefixIndex n 7 0) (suffixIndex n 7 I))
        (.conj (BoundedFormula.nonemptyTupleFormula 5 (prefixIndex n 7 0)
          (fun k => prefixIndex n 7 k.succ)).toFormula
          (BoundedFormula.orderedPairFormula (suffixIndex n 7 z) (prefixIndex n 7 0)
            (prefixIndex n 7 j.succ)).toFormula)) (extendMany 7 w env) ↔
      w 0 ∈ env I ∧ w 0 = nonemptyTupleCode 5 (fun k => w k.succ) ∧
        env z = ZFSet.pair (w 0) (w j.succ) := by
    simp only [Realize, BoundedFormula.realize_toFormula M _ _
      (extendMany_members 7 w env ground members), BoundedFormula.truth_nonemptyTupleFormula,
      BoundedFormula.truth_orderedPairFormula, extendMany_prefix, extendMany_suffix]
  constructor
  · rintro ⟨w, ground, holds⟩
    obtain ⟨hi, eq, pair⟩ := (actual w ground).1 holds
    exact ⟨fun k => w k.succ, eq ▸ hi, eq ▸ pair⟩
  · rintro ⟨fields, hi, pair⟩
    have hcode := M.transitive (members I) hi
    have hf := M.nonemptyTupleCode_field_mem 5 fields hcode
    let w := extend (nonemptyTupleCode 5 fields) fields
    have ground : ∀ k, w k ∈ M.sets := Fin.cases hcode hf
    exact ⟨w, ground, (actual w ground).2 ⟨hi, rfl, pair⟩⟩

theorem refinementIndexFieldGraph_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {I B : ZFSet.{u}} (hI : I ∈ M.sets) (hB : B ∈ M.sets) (j : Fin 6) :
    refinementIndexFieldGraph I B j ∈ M.sets := by
  have hp := M.prod_mem pairing unions powers separation hI hB
  let params := extend I Fin.elim0
  have ground := M.separation_mem separation (refinementIndexFieldFormula 0 1 j)
    params (Fin.cases hI (fun k => Fin.elim0 k)) hp
  have equal : ZFSet.sep (fun z => Realize M.sets (refinementIndexFieldFormula 0 1 j)
      (extend z params)) (ZFSet.prod I B) = refinementIndexFieldGraph I B j := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep, refinementIndexFieldGraph, ZFSet.mem_sep]
    apply and_congr_right
    intro hz
    exact M.realize_refinementIndexFieldFormula 0 1 j _
      (Fin.cases (M.transitive hp hz) (Fin.cases hI (fun k => Fin.elim0 k)))
  exact equal ▸ ground

end TransitiveGround

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
open scoped ZFSet
universe u
variable (M : TransitiveGround.{u})

theorem graphRestriction_mem
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (separation : SeparationSchema M.sets)
    {A f : ZFSet.{u}} (hA : A ∈ M.sets) (hf : f ∈ M.sets) :
    graphRestriction A f ∈ M.sets :=
  M.injection_restriction_mem separation hA (M.union_mem unions (M.union_mem unions hf)) hf

theorem functionGraphOn_ground_range
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {A f : ZFSet.{u}} (hf : f ∈ M.sets) (h : FunctionGraphOn A f) :
    ∃ B ∈ M.sets, ZFSet.IsFunc A B f :=
  ⟨⋃₀ ⋃₀ f, M.union_mem unions (M.union_mem unions hf), h.to_isFunc⟩

end PartitionPilot.Forcing.TransitiveGround



namespace PartitionPilot.Forcing
open SetFormula
open scoped ZFSet
universe u

noncomputable def tupleFieldBound : Nat → ZFSet.{u} → ZFSet.{u}
  | 0, B => B
  | k + 1, B => (⋃₀ ⋃₀ B) ∪ tupleFieldBound k (⋃₀ ⋃₀ B)

theorem nonemptyTupleCode_field_mem_bound (k : Nat) (fields : Fin (k + 1) → ZFSet.{u})
    {B : ZFSet.{u}} (member : nonemptyTupleCode k fields ∈ B) :
    ∀ j, fields j ∈ tupleFieldBound k B := by
  induction k generalizing B with
  | zero => exact Fin.cases member (fun j => Fin.elim0 j)
  | succ k ih =>
    have pair : ZFSet.pair (fields 0) (nonemptyTupleCode k (fun j => fields j.succ)) ∈ B := member
    exact Fin.cases (ZFSet.mem_union.2 (Or.inl (pair_first_mem_doubleUnion pair)))
      (fun j => ZFSet.mem_union.2 (Or.inr (ih _ (pair_second_mem_doubleUnion pair) j)))

namespace BoundedFormula
noncomputable def tupleFieldFormula : (k : Nat) → {n : Nat} → Fin n → Fin n → Fin (k + 1) → BoundedFormula n
  | 0, _, z, y, _ => .equal y z
  | k + 1, _, z, y, j => exPairFields z
      (Fin.cases (.conj (.equal y.succ.succ 1) (tupleShapeFormula k 0))
        (fun i => tupleFieldFormula k 0 y.succ.succ i) j)

theorem truth_tupleFieldFormula (k : Nat) {n : Nat} (z y : Fin n) (j : Fin (k + 1))
    (env : Fin n → ZFSet.{u}) :
    Truth (tupleFieldFormula k z y j) env ↔
      ∃ fields : Fin (k + 1) → ZFSet.{u}, env z = nonemptyTupleCode k fields ∧ env y = fields j := by
  induction k generalizing n with
  | zero =>
    change env y = env z ↔ ∃ fields : Fin 1 → ZFSet.{u}, env z = fields 0 ∧ env y = fields j
    constructor
    · intro equal
      exact ⟨fun _ => env z, rfl, equal⟩
    · rintro ⟨fields, first, second⟩
      have eq : j = 0 := Fin.cases rfl (fun i => Fin.elim0 i) j
      exact (eq ▸ second).trans first.symm
  | succ k ih =>
    rw [tupleFieldFormula, truth_exPairFields]
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [Fin.cases_zero, Truth, truth_tupleShapeFormula]
      constructor
      · rintro ⟨head, tail, pair, value, fields, tuple⟩
        let all : Fin (k + 2) → ZFSet.{u} := Fin.cases head fields
        refine ⟨all, ?_, ?_⟩
        · change env z = ZFSet.pair head (nonemptyTupleCode k fields)
          exact pair.trans (congrArg (ZFSet.pair head) tuple)
        · exact value
      · rintro ⟨fields, pair, value⟩
        exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), pair,
          value, fun i => fields i.succ, rfl⟩
    · simp only [Fin.cases_succ, ih]
      constructor
      · rintro ⟨head, tail, pair, fields, tuple, value⟩
        let all : Fin (k + 2) → ZFSet.{u} := Fin.cases head fields
        refine ⟨all, ?_, ?_⟩
        · change env z = ZFSet.pair head (nonemptyTupleCode k fields)
          exact pair.trans (congrArg (ZFSet.pair head) tuple)
        · exact value
      · rintro ⟨fields, pair, value⟩
        exact ⟨fields 0, nonemptyTupleCode k (fun i => fields i.succ), pair,
          fun i => fields i.succ, rfl, value⟩

end BoundedFormula

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem tupleFieldBound_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (k : Nat) {B : ZFSet.{u}} (ground : B ∈ M.sets) : tupleFieldBound k B ∈ M.sets := by
  induction k generalizing B with
  | zero => exact ground
  | succ k ih =>
    have hB := M.union_mem unions (M.union_mem unions ground)
    exact M.binary_union_mem pairing unions hB (ih hB)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
