import OAI.SetTheory.PartitionPrinciple.Models.GroundSuccessorInjections

namespace OAI


namespace PartitionPilot.Forcing

open SetRealization
universe u

theorem natSetCode_injective : Function.Injective (natSetCode : Nat → ZFSet.{u}) := by
  intro m n eq
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ n => exact False.elim (setSuccessor_ne_empty (natSetCode n) eq.symm)
  | succ m ih =>
    cases n with
    | zero => exact False.elim (setSuccessor_ne_empty (natSetCode m) eq)
    | succ n => exact congrArg Nat.succ (ih (setSuccessor_injective eq))

theorem natSetCode_mem_iff (m n : Nat) : natSetCode m ∈ natSetCode n ↔ m < n := by
  induction n with
  | zero =>
    exact ⟨fun h => False.elim (ZFSet.notMem_empty _ h), fun h => False.elim (Nat.not_lt_zero m h)⟩
  | succ n ih =>
    rw [natSetCode_succ, ZFSet.mem_insert_iff, natSetCode_injective.eq_iff, ih]
    omega

theorem mem_natSetCode (x : ZFSet.{u}) (n : Nat) :
    x ∈ natSetCode n ↔ ∃ m < n, x = natSetCode m := by
  constructor
  · intro hx
    have natural := naturalSetProperty_member ((naturalSetProperty_iff (natSetCode n)).2 ⟨n, rfl⟩) hx
    obtain ⟨m, eq⟩ := (naturalSetProperty_iff x).1 natural
    exact ⟨m, (natSetCode_mem_iff m n).1 (eq ▸ hx), eq⟩
  · rintro ⟨m, hm, rfl⟩
    exact (natSetCode_mem_iff m n).2 hm

def natPresentation : Presentation (ULift.{u} Nat) where
  carrier := ZFSet.omega
  encode n := natSetCode n.down
  injective := fun _ _ eq => ULift.ext _ _ (natSetCode_injective eq)
  mem_carrier x := by
    rw [mem_omega_iff_natSetCode]
    exact ⟨fun ⟨n, eq⟩ => ⟨⟨n⟩, eq.symm⟩, fun ⟨n, eq⟩ => ⟨n.down, eq.symm⟩⟩

def natInitialPresentation (n : Nat) : Presentation (ULift.{u} (Fin n)) where
  carrier := natSetCode n
  encode i := natSetCode i.down.val
  injective := fun _ _ eq => ULift.ext _ _ (Fin.ext (natSetCode_injective eq))
  mem_carrier x := by
    rw [mem_natSetCode]
    exact ⟨fun ⟨m, hm, eq⟩ => ⟨⟨⟨m, hm⟩⟩, eq.symm⟩,
      fun ⟨m, eq⟩ => ⟨m.down.val, m.down.isLt, eq.symm⟩⟩

theorem natSetCode_finite (n : Nat) : (natSetCode n : ZFSet.{u}).toSet.Finite := by
  have eq : (natSetCode n : ZFSet.{u}).toSet = Set.range (fun i : Fin n => natSetCode i.val) := by
    apply Set.ext
    intro x
    change x ∈ natSetCode n ↔ _
    rw [mem_natSetCode]
    exact ⟨fun ⟨m, hm, eq⟩ => ⟨⟨m, hm⟩, eq.symm⟩, fun ⟨m, eq⟩ => ⟨m.val, m.isLt, eq.symm⟩⟩
  rw [eq]
  simpa only [Set.image_univ] using Set.finite_univ.image (fun i : Fin n => (natSetCode i.val : ZFSet.{u}))

end PartitionPilot.Forcing



namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def externalSignCode (b : Bool) : ZFSet.{u} := natSetCode (if b then 1 else 0)

theorem externalSignCode_injective : Function.Injective (externalSignCode : Bool → ZFSet.{u}) := by
  intro a b eq
  cases a <;> cases b <;> simp only [externalSignCode, Bool.false_eq_true, ite_false, ite_true,
    natSetCode_injective.eq_iff] at eq ⊢
  · exact False.elim (Nat.zero_ne_one eq)
  · exact False.elim (Nat.zero_ne_one eq.symm)

theorem mem_natTwo_iff_externalSignCode (x : ZFSet.{u}) :
    x ∈ natSetCode 2 ↔ ∃ b : Bool, x = externalSignCode b := by
  constructor
  · intro hx
    obtain ⟨n, hn, rfl⟩ := (mem_natSetCode x 2).1 hx
    have cases : n = 0 ∨ n = 1 := by omega
    rcases cases with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩
  · rintro ⟨b, rfl⟩
    cases b <;> exact (natSetCode_mem_iff _ 2).2 (by decide)

def externalActorSymbol (g : ZFSet.{u}) : ZFSet.{u} := ZFSet.pair (natSetCode 0) g

def externalLetterSymbol (s : ZFSet.{u}) (b : Bool) : ZFSet.{u} :=
  ZFSet.pair (natSetCode 1) (ZFSet.pair s (externalSignCode b))

def externalGeneratorAlphabet (G S : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSetCode 0} G ∪ ZFSet.prod {natSetCode 1} (ZFSet.prod S (natSetCode 2))

theorem externalActorSymbol_injective : Function.Injective (externalActorSymbol : ZFSet.{u} → ZFSet.{u}) :=
  fun _ _ eq => (ZFSet.pair_inj.1 eq).2

theorem externalLetterSymbol_inj {s t : ZFSet.{u}} {b c : Bool} :
    externalLetterSymbol s b = externalLetterSymbol t c ↔ s = t ∧ b = c := by
  constructor
  · intro eq
    have parts := ZFSet.pair_inj.1 (ZFSet.pair_inj.1 eq).2
    exact ⟨parts.1, externalSignCode_injective parts.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem externalActorSymbol_ne_letterSymbol (g s : ZFSet.{u}) (b : Bool) :
    externalActorSymbol g ≠ externalLetterSymbol s b := by
  intro eq
  have tags : (0 : Nat) = 1 := natSetCode_injective (ZFSet.pair_inj.1 eq).1
  exact Nat.zero_ne_one tags

theorem mem_externalGeneratorAlphabet (G S z : ZFSet.{u}) :
    z ∈ externalGeneratorAlphabet G S ↔
      (∃ g ∈ G, z = externalActorSymbol g) ∨
        ∃ s ∈ S, ∃ b : Bool, z = externalLetterSymbol s b := by
  rw [externalGeneratorAlphabet, ZFSet.mem_union]
  constructor
  · rintro (old | signed)
    · obtain ⟨tag, htag, g, hg, eq⟩ := ZFSet.mem_prod.1 old
      have tagEq := ZFSet.mem_singleton.1 htag
      subst tag
      exact Or.inl ⟨g, hg, eq⟩
    · obtain ⟨tag, htag, p, hp, eq⟩ := ZFSet.mem_prod.1 signed
      have tagEq := ZFSet.mem_singleton.1 htag
      subst tag
      obtain ⟨s, hs, sign, hsign, rfl⟩ := ZFSet.mem_prod.1 hp
      obtain ⟨b, rfl⟩ := (mem_natTwo_iff_externalSignCode sign).1 hsign
      exact Or.inr ⟨s, hs, b, eq⟩
  · rintro (⟨g, hg, rfl⟩ | ⟨s, hs, b, rfl⟩)
    · exact Or.inl (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl, hg⟩)
    · exact Or.inr (ZFSet.pair_mem_prod.2 ⟨ZFSet.mem_singleton.2 rfl,
        ZFSet.pair_mem_prod.2 ⟨hs, (mem_natTwo_iff_externalSignCode _).2 ⟨b, rfl⟩⟩⟩)

theorem externalActorSymbol_mem (G S g : ZFSet.{u}) :
    externalActorSymbol g ∈ externalGeneratorAlphabet G S ↔ g ∈ G := by
  rw [mem_externalGeneratorAlphabet]
  constructor
  · rintro (⟨h, hh, eq⟩ | ⟨s, _, b, eq⟩)
    · exact externalActorSymbol_injective eq ▸ hh
    · exact False.elim (externalActorSymbol_ne_letterSymbol g s b eq)
  · intro hg
    exact Or.inl ⟨g, hg, rfl⟩

theorem externalLetterSymbol_mem (G S s : ZFSet.{u}) (b : Bool) :
    externalLetterSymbol s b ∈ externalGeneratorAlphabet G S ↔ s ∈ S := by
  rw [mem_externalGeneratorAlphabet]
  constructor
  · rintro (⟨g, _, eq⟩ | ⟨t, ht, c, eq⟩)
    · exact False.elim (externalActorSymbol_ne_letterSymbol g s b eq.symm)
    · exact (externalLetterSymbol_inj.1 eq).1 ▸ ht
  · intro hs
    exact Or.inr ⟨s, hs, b, rfl⟩

def externalAlphabetEncode {J L : Type u} (s : Presentation J) (t : Presentation L) :
    J ⊕ (L × Bool) → ZFSet.{u}
  | .inl g => externalActorSymbol (s.encode g)
  | .inr p => externalLetterSymbol (t.encode p.1) p.2

theorem externalAlphabetEncode_injective {J L : Type u} (s : Presentation J) (t : Presentation L) :
    Function.Injective (externalAlphabetEncode s t) := by
  intro x y eq
  cases x with
  | inl g =>
    cases y with
    | inl h => exact congrArg Sum.inl (s.injective (externalActorSymbol_injective eq))
    | inr p => exact False.elim (externalActorSymbol_ne_letterSymbol _ _ _ eq)
  | inr p =>
    cases y with
    | inl g => exact False.elim (externalActorSymbol_ne_letterSymbol _ _ _ eq.symm)
    | inr q =>
      have parts := externalLetterSymbol_inj.1 eq
      exact congrArg Sum.inr (Prod.ext (t.injective parts.1) parts.2)

def externalGeneratorAlphabetPresentation {J L : Type u} (s : Presentation J) (t : Presentation L) :
    Presentation (J ⊕ (L × Bool)) where
  carrier := externalGeneratorAlphabet s.carrier t.carrier
  encode := externalAlphabetEncode s t
  injective := externalAlphabetEncode_injective s t
  mem_carrier z := by
    rw [mem_externalGeneratorAlphabet]
    constructor
    · rintro (⟨g, hg, eq⟩ | ⟨l, hl, b, eq⟩)
      · obtain ⟨j, rfl⟩ := (s.mem_carrier g).1 hg
        exact ⟨.inl j, eq.symm⟩
      · obtain ⟨l, rfl⟩ := (t.mem_carrier l).1 hl
        exact ⟨.inr (l, b), eq.symm⟩
    · rintro ⟨x, rfl⟩
      cases x with
      | inl g => exact Or.inl ⟨s.encode g, s.encode_mem g, rfl⟩
      | inr p => exact Or.inr ⟨t.encode p.1, t.encode_mem p.1, p.2, rfl⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})

theorem externalGeneratorAlphabet_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {G S : ZFSet.{u}} (hG : G ∈ M.sets) (hS : S ∈ M.sets) :
    externalGeneratorAlphabet G S ∈ M.sets := by
  have hZero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨G, hG⟩
  have hOne : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions hZero hZero
  have hTwo : natSetCode 2 ∈ M.sets := M.insert_mem pairing unions hOne hOne
  have hTagZero : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hZero hZero
  have hTagOne : ({natSetCode 1} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hOne hOne
  exact M.binary_union_mem pairing unions
    (M.prod_mem pairing unions powers separation hTagZero hG)
    (M.prod_mem pairing unions powers separation hTagOne
      (M.prod_mem pairing unions powers separation hS hTwo))

end TransitiveGround






namespace BoundedFormula

def finiteWordFormula {n} (omega alphabet graph : Fin n) : BoundedFormula n :=
  exMem omega (functionFormula 0 alphabet.succ graph.succ)

theorem truth_finiteWordFormula {n} (omega alphabet graph : Fin n)
    (env : Fin n → ZFSet.{u}) :
    Truth (finiteWordFormula omega alphabet graph) env ↔
      ∃ N ∈ env omega, ZFSet.IsFunc N (env alphabet) (env graph) := by
  simp only [finiteWordFormula, truth_exMem, truth_functionFormula]
  rfl

end BoundedFormula

theorem finiteWord_domain_unique {m n : Nat} {A B f : ZFSet.{u}}
    (first : ZFSet.IsFunc (natSetCode m) A f)
    (second : ZFSet.IsFunc (natSetCode n) B f) : m = n := by
  apply natSetCode_injective
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, entry, _⟩ := first.2 x hx
    exact (ZFSet.pair_mem_prod.1 (second.1 entry)).1
  · intro hx
    obtain ⟨y, entry, _⟩ := second.2 x hx
    exact (ZFSet.pair_mem_prod.1 (first.1 entry)).1

namespace TransitiveGround

variable (M : TransitiveGround.{u})

noncomputable def finiteWords (A : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.sep (fun f => ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f)
    (M.groundRelations ZFSet.omega A)

theorem mem_finiteWords_iff (A f : ZFSet.{u}) :
    f ∈ M.finiteWords A ↔ f ∈ M.sets ∧ ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f := by
  rw [finiteWords, ZFSet.mem_sep, M.mem_groundRelations]
  constructor
  · exact fun ⟨⟨ground, _⟩, code⟩ => ⟨ground, code⟩
  · rintro ⟨ground, n, hn, function⟩
    refine ⟨⟨ground, ?_⟩, n, hn, function⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := ZFSet.mem_prod.1 (function.1 hz)
    obtain ⟨j, _, rfl⟩ := (mem_natSetCode x k).1 hx
    exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega j, hy⟩

theorem mem_finiteWords (A f : ZFSet.{u}) :
    f ∈ M.finiteWords A ↔
      f ∈ M.sets ∧ ∃ n : Nat, ZFSet.IsFunc (natSetCode n) A f := by
  rw [M.mem_finiteWords_iff]
  constructor
  · rintro ⟨ground, n, hn, function⟩
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    exact ⟨ground, k, function⟩
  · rintro ⟨ground, n, function⟩
    exact ⟨ground, natSetCode n, natSetCode_mem_omega n, function⟩

theorem finiteWords_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    (infinite : Realize M.sets infinity Fin.elim0)
    {A : ZFSet.{u}} (hA : A ∈ M.sets) : M.finiteWords A ∈ M.sets := by
  have hOmega := M.omega_mem separation infinite
  have space := M.groundRelations_mem pairing unions powers separation hOmega hA
  let params := extend ZFSet.omega (extend A Fin.elim0)
  have selected := M.separation_mem separation
    (BoundedFormula.finiteWordFormula 1 2 0).toFormula params
    (Fin.cases hOmega (Fin.cases hA (fun j => Fin.elim0 j))) space
  have correct (f : ZFSet.{u}) (hf : f ∈ M.sets) :
      Realize M.sets (BoundedFormula.finiteWordFormula 1 2 0).toFormula (extend f params) ↔
        ∃ n ∈ ZFSet.omega, ZFSet.IsFunc n A f :=
    (BoundedFormula.realize_toFormula M _ _
      (Fin.cases hf (Fin.cases hOmega (Fin.cases hA (fun j => Fin.elim0 j))))).trans
        (BoundedFormula.truth_finiteWordFormula 1 2 0 _)
  have eq : ZFSet.sep (fun f => Realize M.sets
      (BoundedFormula.finiteWordFormula 1 2 0).toFormula (extend f params))
        (M.groundRelations ZFSet.omega A) = M.finiteWords A := by
    apply ZFSet.ext
    intro f
    rw [ZFSet.mem_sep, finiteWords, ZFSet.mem_sep]
    exact and_congr_right (fun hf => correct f (M.transitive space hf))
  exact eq ▸ selected

end TransitiveGround

end PartitionPilot.Forcing


section

namespace PartitionPilot.Compression.RecursiveMaps.RationalHeights.Fraction

theorem intCode_surjective : Function.Surjective intCode := by
  intro n
  by_cases even : n % 2 = 0
  · exact ⟨Int.ofNat (n / 2), by simp only [intCode]; omega⟩
  · exact ⟨Int.negSucc (n / 2), by simp only [intCode]; omega⟩

end PartitionPilot.Compression.RecursiveMaps.RationalHeights.Fraction

namespace PartitionPilot.Forcing

open SetRealization Compression.RecursiveMaps.RationalHeights
universe u

noncomputable def fractionCarrier : ZFSet.{u} :=
  ZFSet.prod ZFSet.omega (ZFSet.sep (fun d => d ≠ natSetCode 0) ZFSet.omega)

def fractionEncode (a : Fraction) : ZFSet.{u} :=
  ZFSet.pair (natSetCode (Fraction.intCode a.num)) (natSetCode a.den)

theorem fractionEncode_mem (a : Fraction) : fractionEncode a ∈ fractionCarrier.{u} := by
  exact ZFSet.pair_mem_prod.2 ⟨natSetCode_mem_omega _,
    ZFSet.mem_sep.2 ⟨natSetCode_mem_omega _, fun h => by
      have := natSetCode_injective h
      have := a.positive
      omega⟩⟩

theorem fractionEncode_injective : Function.Injective (fractionEncode : Fraction → ZFSet.{u}) := by
  intro a b equal
  have parts := ZFSet.pair_inj.1 equal
  have hn := Fraction.intCode_injective a.num b.num (natSetCode_injective parts.1)
  have hd := natSetCode_injective parts.2
  cases a
  cases b
  cases hn
  cases hd
  rfl

theorem mem_fractionCarrier (z : ZFSet.{u}) :
    z ∈ fractionCarrier ↔ ∃ a : Fraction, fractionEncode a = z := by
  constructor
  · intro hz
    obtain ⟨n, hn, d, hd, rfl⟩ := ZFSet.mem_prod.1 hz
    obtain ⟨k, rfl⟩ := (mem_omega_iff_natSetCode n).1 hn
    obtain ⟨hd, nonzero⟩ := ZFSet.mem_sep.1 hd
    obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode d).1 hd
    obtain ⟨a, ha⟩ := Fraction.intCode_surjective k
    have positive : 0 < m := by
      have : m ≠ 0 := fun h => nonzero (congrArg natSetCode h)
      omega
    exact ⟨⟨a, m, positive⟩, by dsimp only [fractionEncode]; rw [ha]⟩
  · rintro ⟨a, rfl⟩
    exact fractionEncode_mem a

noncomputable def fractionPresentation : Presentation (ULift.{u} Fraction) where
  carrier := fractionCarrier
  encode a := fractionEncode a.down
  injective := fun _ _ eq => ULift.ext _ _ (fractionEncode_injective eq)
  mem_carrier z := (mem_fractionCarrier z).trans
    ⟨fun ⟨a, ha⟩ => ⟨⟨a⟩, ha⟩, fun ⟨a, ha⟩ => ⟨a.down, ha⟩⟩

noncomputable def fractionEquivGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a b : Fraction,
    z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧ Fraction.Equiv a b)
    (ZFSet.prod fractionCarrier fractionCarrier)

noncomputable def fractionLtGraph : ZFSet.{u} :=
  ZFSet.sep (fun z => ∃ a b : Fraction,
    z = ZFSet.pair (fractionEncode a) (fractionEncode b) ∧ Fraction.Lt a b)
    (ZFSet.prod fractionCarrier fractionCarrier)

theorem fractionEquivGraph_subset : fractionEquivGraph.{u} ⊆ ZFSet.prod fractionCarrier fractionCarrier :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem fractionLtGraph_subset : fractionLtGraph.{u} ⊆ ZFSet.prod fractionCarrier fractionCarrier :=
  fun _ hz => (ZFSet.mem_sep.1 hz).1

theorem pair_mem_fractionEquivGraph (a b : Fraction) :
    ZFSet.pair (fractionEncode a) (fractionEncode b) ∈ fractionEquivGraph.{u} ↔ Fraction.Equiv a b := by
  constructor
  · intro h
    obtain ⟨c, d, equal, rel⟩ := (ZFSet.mem_sep.1 h).2
    have parts := ZFSet.pair_inj.1 equal
    obtain rfl := fractionEncode_injective parts.1
    obtain rfl := fractionEncode_injective parts.2
    exact rel
  · intro rel
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨fractionEncode_mem a, fractionEncode_mem b⟩,
      a, b, rfl, rel⟩

theorem pair_mem_fractionLtGraph (a b : Fraction) :
    ZFSet.pair (fractionEncode a) (fractionEncode b) ∈ fractionLtGraph.{u} ↔ Fraction.Lt a b := by
  constructor
  · intro h
    obtain ⟨c, d, equal, rel⟩ := (ZFSet.mem_sep.1 h).2
    have parts := ZFSet.pair_inj.1 equal
    obtain rfl := fractionEncode_injective parts.1
    obtain rfl := fractionEncode_injective parts.2
    exact rel
  · intro rel
    exact ZFSet.mem_sep.2 ⟨ZFSet.pair_mem_prod.2 ⟨fractionEncode_mem a, fractionEncode_mem b⟩,
      a, b, rfl, rel⟩

end PartitionPilot.Forcing

end


namespace PartitionPilot.Forcing
open SetRealization SetFormula
universe u

def taggedSumCarrier (A B : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.prod {natSetCode 0} A ∪ ZFSet.prod {natSetCode 1} B

theorem mem_taggedSumCarrier (A B z : ZFSet.{u}) :
    z ∈ taggedSumCarrier A B ↔
      (∃ a ∈ A, z = ZFSet.pair (natSetCode 0) a) ∨ ∃ b ∈ B, z = ZFSet.pair (natSetCode 1) b := by
  simp only [taggedSumCarrier, ZFSet.mem_union, ZFSet.mem_prod, ZFSet.mem_singleton]
  constructor
  · rintro (⟨_, rfl, a, ha, equal⟩ | ⟨_, rfl, b, hb, equal⟩)
    · exact Or.inl ⟨a, ha, equal⟩
    · exact Or.inr ⟨b, hb, equal⟩
  · rintro (⟨a, ha, equal⟩ | ⟨b, hb, equal⟩)
    · exact Or.inl ⟨_, rfl, a, ha, equal⟩
    · exact Or.inr ⟨_, rfl, b, hb, equal⟩

def taggedSumEncode {A B : Type u} (s : Presentation A) (t : Presentation B) : A ⊕ B → ZFSet.{u}
  | .inl a => ZFSet.pair (natSetCode 0) (s.encode a)
  | .inr b => ZFSet.pair (natSetCode 1) (t.encode b)

theorem taggedSumEncode_injective {A B : Type u} (s : Presentation A) (t : Presentation B) :
    Function.Injective (taggedSumEncode s t) := by
  intro x y equal
  cases x <;> cases y
  · exact congrArg Sum.inl (s.injective (ZFSet.pair_inj.1 equal).2)
  · exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1))
  · exact False.elim (Nat.zero_ne_one (natSetCode_injective (ZFSet.pair_inj.1 equal).1.symm))
  · exact congrArg Sum.inr (t.injective (ZFSet.pair_inj.1 equal).2)

def taggedSumPresentation {A B : Type u} (s : Presentation A) (t : Presentation B) : Presentation (A ⊕ B) where
  carrier := taggedSumCarrier s.carrier t.carrier
  encode := taggedSumEncode s t
  injective := taggedSumEncode_injective s t
  mem_carrier z := by
    rw [mem_taggedSumCarrier]
    constructor
    · rintro (⟨a, ha, equal⟩ | ⟨b, hb, equal⟩)
      · obtain ⟨a, rfl⟩ := (s.mem_carrier a).1 ha
        exact ⟨.inl a, equal.symm⟩
      · obtain ⟨b, rfl⟩ := (t.mem_carrier b).1 hb
        exact ⟨.inr b, equal.symm⟩
    · rintro ⟨a | b, rfl⟩
      · exact Or.inl ⟨s.encode a, s.encode_mem a, rfl⟩
      · exact Or.inr ⟨t.encode b, t.encode_mem b, rfl⟩

def externalSignPresentation : Presentation (ULift.{u} Bool) where
  carrier := natSetCode 2
  encode b := externalSignCode b.down
  injective := fun a b equal => ULift.ext _ _ (externalSignCode_injective equal)
  mem_carrier z := by
    rw [mem_natTwo_iff_externalSignCode]
    constructor
    · rintro ⟨b, equal⟩
      exact ⟨ULift.up b, equal.symm⟩
    · rintro ⟨b, equal⟩
      exact ⟨b.down, equal.symm⟩

namespace TransitiveGround
variable (M : TransitiveGround.{u})
theorem taggedSumCarrier_mem
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) : taggedSumCarrier A B ∈ M.sets := by
  have zero : natSetCode 0 ∈ M.sets := M.empty_mem ⟨A, hA⟩
  have one : natSetCode 1 ∈ M.sets := M.insert_mem pairing unions zero zero
  have tag0 : ({natSetCode 0} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing zero zero
  have tag1 : ({natSetCode 1} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing one one
  exact M.binary_union_mem pairing unions (M.prod_mem pairing unions powers separation tag0 hA)
    (M.prod_mem pairing unions powers separation tag1 hB)

end TransitiveGround

end PartitionPilot.Forcing

end OAI
