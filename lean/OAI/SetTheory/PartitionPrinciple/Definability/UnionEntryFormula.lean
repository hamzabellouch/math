import OAI.SetTheory.PartitionPrinciple.Forcing.NameOrbitBounds

namespace OAI


namespace PartitionPilot.Forcing.SetFormula

open SetRealization Compression.RecursiveMaps
universe u v
variable {P : Type u} {s : Presentation P}

theorem realize_pairing (U : Set ZFSet.{u})
    (pairs : ∀ x ∈ U, ∀ y ∈ U, ({x, y} : ZFSet.{u}) ∈ U) :
    Realize U pairing Fin.elim0 := by
  simp only [pairing, realize_ex, realize_imp, realize_disj, Realize]
  intro x hx y hy
  refine ⟨{x, y}, pairs x hx y hy, ?_⟩
  intro z _
  exact ⟨ZFSet.mem_pair.1, ZFSet.mem_pair.2⟩

theorem realize_union (D : Name.NameDomain s) (H : Set P)
    (unions : ∀ x ∈ D.values H, ZFSet.sUnion x ∈ D.values H) :
    Realize (D.values H) union Fin.elim0 := by
  simp only [union, realize_ex, realize_imp, Realize]
  intro x hx
  refine ⟨ZFSet.sUnion x, unions x hx, ?_⟩
  intro z _
  constructor
  · intro member
    obtain ⟨w, wx, zw⟩ := ZFSet.mem_sUnion.1 member
    exact ⟨w, D.values_transitive H hx wx, wx, zw⟩
  · rintro ⟨w, _, wx, zw⟩
    exact ZFSet.mem_sUnion.2 ⟨w, wx, zw⟩

variable {G : Type v} [Group G] [PartialOrder P]
variable (a : PosetAction G P) (D : Name.NameDomain s) (F : NormalSubgroupFamily G)

theorem realize_symmetric_pairing [OrderTop P]
    (pairs : ∀ σ ∈ D.names, ∀ τ ∈ D.names, Name.unorderedPair ⊤ σ τ ∈ D.names)
    (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s D F).values {p | H.mem p}) pairing Fin.elim0 :=
  realize_pairing _ (fun _ hx _ hy => a.symmetric_values_pair s D F pairs H hx hy)

theorem realize_symmetric_union
    (unions : ∀ τ ∈ D.names, Name.unionName τ ∈ D.names) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s D F).values {p | H.mem p}) union Fin.elim0 :=
  realize_union _ _ (fun _ hx => a.symmetric_values_union s D F unions H hx)

theorem symmetric_separation_scheme
    (closed : ∀ g τ, τ ∈ D.names → a.act s g τ ∈ D.names)
    (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily (a.symmetricDomain s D F)))
    (separated : ∀ {n} (φ : SetFormula (n + 1))
      (env : Assignment (a.symmetricDomain s D F) n) τ,
      τ ∈ (a.symmetricDomain s D F).names →
      Name.separationName (a.symmetricDomain s D F) φ env τ ∈ D.names)
    {n : Nat} (φ : SetFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ (a.symmetricDomain s D F).values {p | H.mem p})
    {x : ZFSet.{u}} (hx : x ∈ (a.symmetricDomain s D F).values {p | H.mem p}) :
    ∃ y ∈ (a.symmetricDomain s D F).values {p | H.mem p},
      ∀ z, z ∈ y ↔ z ∈ x ∧
        Realize ((a.symmetricDomain s D F).values {p | H.mem p}) φ (extend z params) := by
  refine ⟨ZFSet.sep (fun z => Realize ((a.symmetricDomain s D F).values {p | H.mem p})
      φ (extend z params)) x,
    a.symmetric_values_separation_params s D F closed H generic φ (separated φ) params members hx,
    ?_⟩
  intro z
  exact ZFSet.mem_sep

end PartitionPilot.Forcing.SetFormula



namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula Compression.RecursiveMaps
universe u v
variable (M : TransitiveGround.{u})

theorem unorderedPair_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : ({x, y} : ZFSet.{u}) ∈ M.sets := by
  simp only [SetFormula.pairing, realize_ex, realize_imp, realize_disj, Realize] at pairing
  obtain ⟨z, hz, spec⟩ := pairing x hx y hy
  have eq : z = ({x, y} : ZFSet.{u}) := by
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    constructor
    · intro hw
      exact (spec w (M.transitive hz hw)).1 hw
    · intro hw
      have hwM : w ∈ M.sets := by
        rcases hw with rfl | rfl
        · exact hx
        · exact hy
      exact (spec w hwM).2 hw
  exact eq ▸ hz

theorem orderedPair_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : ZFSet.pair x y ∈ M.sets := by
  have singleton : ({x} : ZFSet.{u}) ∈ M.sets := by
    simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hx hx
  exact M.unorderedPair_mem pairing singleton (M.unorderedPair_mem pairing hx hy)

variable {P : Type u} (s : Presentation P)

theorem pairName_code (one : P) (σ τ : Name s) :
    (Name.unorderedPair one σ τ).val =
      ({ZFSet.pair σ.val (s.encode one), ZFSet.pair τ.val (s.encode one)} : ZFSet.{u}) := by
  apply ZFSet.ext
  intro z
  change z ∈ ZFSet.range (fun b : Bool => ZFSet.pair (if b then σ else τ).val (s.encode one)) ↔ _
  rw [ZFSet.mem_range, ZFSet.mem_pair]
  constructor
  · rintro ⟨b, eq⟩
    cases b with
    | false => exact Or.inr eq.symm
    | true => exact Or.inl eq.symm
  · rintro (eq | eq)
    · exact ⟨true, eq.symm⟩
    · exact ⟨false, eq.symm⟩

theorem pairName_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (one : P) (hone : s.encode one ∈ M.sets) {σ τ : Name s}
    (hσ : σ ∈ (M.nameDomain s).names) (hτ : τ ∈ (M.nameDomain s).names) :
    Name.unorderedPair one σ τ ∈ (M.nameDomain s).names := by
  change (Name.unorderedPair one σ τ).val ∈ M.sets
  rw [pairName_code]
  exact M.unorderedPair_mem pairing (M.orderedPair_mem pairing hσ hone)
    (M.orderedPair_mem pairing hτ hone)

theorem symmetric_pairing {G : Type v} [Group G] [PartialOrder P] [OrderTop P]
    (a : PosetAction G P) (F : NormalSubgroupFamily G)
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (carrier : s.carrier ∈ M.sets) (H : ConditionFilter P) :
    Realize ((a.symmetricDomain s (M.nameDomain s) F).values {p | H.mem p})
      SetFormula.pairing Fin.elim0 :=
  realize_symmetric_pairing a (M.nameDomain s) F
    (fun _ hσ _ hτ => M.pairName_mem s pairing ⊤
      (M.transitive carrier (s.encode_mem ⊤)) hσ hτ) H

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def unorderedPairFormula {n : Nat} (z x y : Fin n) : SetFormula n :=
  .all (.conj
    (imp (.mem 0 z.succ) (disj (.equal 0 x.succ) (.equal 0 y.succ)))
    (imp (disj (.equal 0 x.succ) (.equal 0 y.succ)) (.mem 0 z.succ)))

def orderedPairFormula {n : Nat} (z x y : Fin n) : SetFormula n :=
  ex (ex (.conj (unorderedPairFormula z.succ.succ 1 0)
    (.conj (unorderedPairFormula 1 x.succ.succ x.succ.succ)
      (unorderedPairFormula 0 x.succ.succ y.succ.succ))))

def pairMembershipFormula {n : Nat} (x y z : Fin n) : SetFormula n :=
  ex (.conj (orderedPairFormula 0 x.succ y.succ) (.mem 0 z.succ))

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_unorderedPairFormula {n : Nat} (z x y : Fin n)
    (env : Fin n → ZFSet.{u}) (hz : env z ∈ M.sets) (hx : env x ∈ M.sets)
    (hy : env y ∈ M.sets) :
    Realize M.sets (unorderedPairFormula z x y) env ↔ env z = ({env x, env y} : ZFSet.{u}) := by
  simp only [unorderedPairFormula, realize_imp, realize_disj, Realize]
  constructor
  · intro spec
    apply ZFSet.ext
    intro w
    rw [ZFSet.mem_pair]
    constructor
    · intro hw
      exact (spec w (M.transitive hz hw)).1 hw
    · intro hw
      have hwM : w ∈ M.sets := by
        rcases hw with rfl | rfl
        · exact hx
        · exact hy
      exact (spec w hwM).2 hw
  · intro eq w _
    change (w ∈ env z → w = env x ∨ w = env y) ∧
      ((w = env x ∨ w = env y) → w ∈ env z)
    rw [eq]
    exact ⟨ZFSet.mem_pair.1, ZFSet.mem_pair.2⟩

theorem realize_orderedPairFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (z x y : Fin n) (env : Fin n → ZFSet.{u})
    (hz : env z ∈ M.sets) (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) :
    Realize M.sets (orderedPairFormula z x y) env ↔ env z = ZFSet.pair (env x) (env y) := by
  simp only [orderedPairFormula, realize_ex]
  constructor
  · rintro ⟨a, ha, b, hb, shape, left, right⟩
    have hzab := (M.realize_unorderedPairFormula z.succ.succ 1 0 _ hz ha hb).1 shape
    have haeq := (M.realize_unorderedPairFormula 1 x.succ.succ x.succ.succ _ ha hx hx).1 left
    have hbeq := (M.realize_unorderedPairFormula 0 x.succ.succ y.succ.succ _ hb hx hy).1 right
    change env z = ({a, b} : ZFSet.{u}) at hzab
    change a = ({env x, env x} : ZFSet.{u}) at haeq
    change b = ({env x, env y} : ZFSet.{u}) at hbeq
    rw [haeq, hbeq, ZFSet.pair_eq_singleton] at hzab
    exact hzab
  · intro eq
    have ha := M.unorderedPair_mem pairing hx hx
    have hb := M.unorderedPair_mem pairing hx hy
    refine ⟨{env x, env x}, ha, {env x, env y}, hb, ?_, ?_, ?_⟩
    · apply (M.realize_unorderedPairFormula z.succ.succ 1 0 _ hz ha hb).2
      change env z = ({{env x, env x}, {env x, env y}} : ZFSet.{u})
      simpa only [ZFSet.pair, ZFSet.pair_eq_singleton] using eq
    · exact (M.realize_unorderedPairFormula 1 x.succ.succ x.succ.succ _ ha hx hx).2 rfl
    · exact (M.realize_unorderedPairFormula 0 x.succ.succ y.succ.succ _ hb hx hy).2 rfl

theorem realize_pairMembershipFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    {n : Nat} (x y z : Fin n) (env : Fin n → ZFSet.{u})
    (hx : env x ∈ M.sets) (hy : env y ∈ M.sets) (hz : env z ∈ M.sets) :
    Realize M.sets (pairMembershipFormula x y z) env ↔ ZFSet.pair (env x) (env y) ∈ env z := by
  simp only [pairMembershipFormula, realize_ex]
  constructor
  · rintro ⟨w, hw, shape, member⟩
    have eq := (M.realize_orderedPairFormula pairing 0 x.succ y.succ _ hw hx hy).1 shape
    change w = ZFSet.pair (env x) (env y) at eq
    change w ∈ env z at member
    exact eq ▸ member
  · intro member
    have hw := M.transitive hz member
    exact ⟨ZFSet.pair (env x) (env y), hw,
      (M.realize_orderedPairFormula pairing 0 x.succ y.succ _ hw hx hy).2 rfl, member⟩

end PartitionPilot.Forcing.TransitiveGround

end



namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem union_mem (unions : Realize M.sets SetFormula.union Fin.elim0)
    {x : ZFSet.{u}} (hx : x ∈ M.sets) : ZFSet.sUnion x ∈ M.sets := by
  simp only [SetFormula.union, realize_ex, realize_imp, Realize] at unions
  obtain ⟨y, hy, spec⟩ := unions x hx
  have eq : y = ZFSet.sUnion x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sUnion]
    constructor
    · intro hz
      obtain ⟨w, _, wx, zw⟩ := (spec z (M.transitive hy hz)).1 hz
      exact ⟨w, wx, zw⟩
    · rintro ⟨w, wx, zw⟩
      have hw := M.transitive hx wx
      exact (spec z (M.transitive hw zw)).2 ⟨w, hw, wx, zw⟩
  exact eq ▸ hy

theorem binary_union_mem (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    {x y : ZFSet.{u}} (hx : x ∈ M.sets) (hy : y ∈ M.sets) : x ∪ y ∈ M.sets := by
  have h := M.union_mem unions (M.unorderedPair_mem pairing hx hy)
  simpa only [ZFSet.sUnion_pair] using h

theorem power_witness (powers : Realize M.sets powerSet Fin.elim0)
    {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ∃ y ∈ M.sets, ∀ z ∈ M.sets, z ∈ y ↔ z ⊆ x := by
  simp only [powerSet, realize_ex, realize_imp, Realize] at powers
  obtain ⟨y, hy, spec⟩ := powers x hx
  refine ⟨y, hy, fun z hz => ⟨?_, ?_⟩⟩
  · intro zy w wz
    exact (spec z hz).1 zy w (M.transitive hz wz) wz
  · intro subset
    exact (spec z hz).2 (fun w _ hw => subset hw)

theorem separation_mem (separation : SeparationSchema M.sets)
    {n : Nat} (φ : SetFormula (n + 1)) (params : Fin n → ZFSet.{u})
    (members : ∀ i, params i ∈ M.sets) {x : ZFSet.{u}} (hx : x ∈ M.sets) :
    ZFSet.sep (fun z => Realize M.sets φ (extend z params)) x ∈ M.sets := by
  obtain ⟨y, hy, spec⟩ := separation φ params members x hx
  have eq : y = ZFSet.sep (fun z => Realize M.sets φ (extend z params)) x := by
    apply ZFSet.ext
    intro z
    rw [ZFSet.mem_sep]
    constructor
    · intro hz
      exact (spec z (M.transitive hy hz)).1 hz
    · intro hz
      exact (spec z (M.transitive hx hz.1)).2 hz
  exact eq ▸ hy

theorem exists_pair_bound (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (unions : Realize M.sets SetFormula.union Fin.elim0)
    (powers : Realize M.sets powerSet Fin.elim0)
    {A B : ZFSet.{u}} (hA : A ∈ M.sets) (hB : B ∈ M.sets) :
    ∃ C ∈ M.sets, ∀ x ∈ A, ∀ y ∈ B, ZFSet.pair x y ∈ C := by
  obtain ⟨U, hU, specU⟩ := M.power_witness powers (M.binary_union_mem pairing unions hA hB)
  obtain ⟨C, hC, specC⟩ := M.power_witness powers hU
  refine ⟨C, hC, ?_⟩
  intro x hx y hy
  have hxM := M.transitive hA hx
  have hyM := M.transitive hB hy
  apply (specC _ (M.orderedPair_mem pairing hxM hyM)).2
  intro z hz
  rcases ZFSet.mem_pair.1 hz with rfl | rfl
  · have single : ({x} : ZFSet.{u}) ∈ M.sets := by
      simpa only [ZFSet.pair_eq_singleton] using M.unorderedPair_mem pairing hxM hxM
    apply (specU _ single).2
    intro w hw
    have eq := ZFSet.mem_singleton.1 hw
    exact ZFSet.mem_union.2 (Or.inl (eq ▸ hx))
  · apply (specU _ (M.unorderedPair_mem pairing hxM hyM)).2
    intro w hw
    rcases ZFSet.mem_pair.1 hw with rfl | rfl
    · exact ZFSet.mem_union.2 (Or.inl hx)
    · exact ZFSet.mem_union.2 (Or.inr hy)

end PartitionPilot.Forcing.TransitiveGround


section

namespace PartitionPilot.Forcing.SetFormula

def unionEntryFormula : SetFormula 4 :=
  ex <| ex <| ex <| ex <| ex <|
    .conj (orderedPairFormula 5 4 3) <|
    .conj (.mem 3 7) <|
    .conj (.mem 1 7) <|
    .conj (.mem 0 7) <|
    .conj (pairMembershipFormula 2 1 6) <|
    .conj (pairMembershipFormula 4 0 2) <|
    .conj (pairMembershipFormula 3 1 8) (pairMembershipFormula 3 0 8)

end PartitionPilot.Forcing.SetFormula

namespace PartitionPilot.Forcing.TransitiveGround

open SetFormula
universe u
variable (M : TransitiveGround.{u})

theorem realize_unionEntryFormula
    (pairing : Realize M.sets SetFormula.pairing Fin.elim0)
    (env : Fin 4 → ZFSet.{u}) (members : ∀ i, env i ∈ M.sets) :
    Realize M.sets unionEntryFormula env ↔
      ∃ x ∈ M.sets, ∃ p ∈ M.sets, ∃ ν ∈ M.sets, ∃ r ∈ M.sets, ∃ q ∈ M.sets,
        env 0 = ZFSet.pair x p ∧ p ∈ env 2 ∧ r ∈ env 2 ∧ q ∈ env 2 ∧
        ZFSet.pair ν r ∈ env 1 ∧ ZFSet.pair x q ∈ ν ∧
        ZFSet.pair p r ∈ env 3 ∧ ZFSet.pair p q ∈ env 3 := by
  simp only [unionEntryFormula, realize_ex]
  apply exists_congr
  intro x
  apply and_congr_right
  intro hx
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  apply exists_congr
  intro ν
  apply and_congr_right
  intro hν
  apply exists_congr
  intro r
  apply and_congr_right
  intro hr
  apply exists_congr
  intro q
  apply and_congr_right
  intro hq
  let e := extend q (extend r (extend ν (extend p (extend x env))))
  change (Realize M.sets (orderedPairFormula 5 4 3) e ∧ p ∈ env 2 ∧ r ∈ env 2 ∧ q ∈ env 2 ∧
    Realize M.sets (pairMembershipFormula 2 1 6) e ∧
    Realize M.sets (pairMembershipFormula 4 0 2) e ∧
    Realize M.sets (pairMembershipFormula 3 1 8) e ∧
    Realize M.sets (pairMembershipFormula 3 0 8) e) ↔ _
  rw [M.realize_orderedPairFormula pairing 5 4 3 e (members 0) hx hp,
    M.realize_pairMembershipFormula pairing 2 1 6 e hν hr (members 1),
    M.realize_pairMembershipFormula pairing 4 0 2 e hx hq hν,
    M.realize_pairMembershipFormula pairing 3 1 8 e hp hr (members 3),
    M.realize_pairMembershipFormula pairing 3 0 8 e hp hq (members 3)]
  rfl

end PartitionPilot.Forcing.TransitiveGround

end


namespace PartitionPilot.Forcing.Name

open SetRealization SetFormula
universe u
variable {P : Type u} [Preorder P] [OrderTop P] {s : Presentation P}

theorem mem_eval_codedPower_iff (D : NameDomain s) (H : ConditionFilter P)
    (generic : H.GenericFor (formulaFamily D))
    (separated : ∀ {n} (φ : SetFormula (n + 1)) (env : Assignment D n) τ,
      τ ∈ D.names → separationName D φ env τ ∈ D.names)
    (τ : D.names) (W : ZFSet.{u})
    (bounded : ∀ σ ∈ D.names, σ.val ∈ W ↔ σ.val ⊆ (envelope τ.val).val)
    (z : ZFSet.{u}) (hz : z ∈ D.values {p | H.mem p}) :
    z ∈ eval {p | H.mem p} (codedPower D W) ↔ z ⊆ eval {p | H.mem p} τ.val := by
  rw [mem_eval_codedPower]
  constructor
  · rintro ⟨σ, hσ, hW, rfl⟩
    have sub := eval_mono {p | H.mem p} ((bounded σ hσ).1 hW)
    rwa [eval_envelope] at sub
  · intro sub
    obtain ⟨ν, hν, value⟩ := (NameDomain.mem_values D _ z).1 hz
    let env : Assignment D 1 := extend ⟨ν, hν⟩ Fin.elim0
    let σ := separationName D (.mem 0 1) env τ.val
    have hσ : σ ∈ D.names := separated (.mem 0 1) env τ.val τ.property
    refine ⟨σ, hσ, (bounded σ hσ).2 (selectName_subset_envelope _ _), ?_⟩
    change eval {p | H.mem p} (separationName D (.mem 0 1) env τ.val) = z
    rw [eval_separationName D H generic (.mem 0 1) env τ.property]
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    change (x ∈ eval {p | H.mem p} τ.val ∧ x ∈ eval {p | H.mem p} ν) ↔ x ∈ z
    rw [value]
    exact ⟨And.right, fun hx => ⟨sub hx, hx⟩⟩

end PartitionPilot.Forcing.Name

namespace PartitionPilot.Forcing.SetFormula

universe u

theorem realize_powerSet_of_witnesses (U : Set ZFSet.{u})
    (transitive : ∀ x ∈ U, ∀ z ∈ x, z ∈ U)
    (witnesses : ∀ x ∈ U, ∃ y ∈ U, ∀ z ∈ U, z ∈ y ↔ z ⊆ x) :
    Realize U powerSet Fin.elim0 := by
  simp only [powerSet, realize_ex, realize_imp, Realize]
  intro x hx
  obtain ⟨y, hy, spec⟩ := witnesses x hx
  refine ⟨y, hy, ?_⟩
  intro z hz
  constructor
  · intro zy w _ wz
    exact (spec z hz).1 zy wz
  · intro sub
    exact (spec z hz).2 (fun w hw => sub w (transitive z hz w hw) hw)

end PartitionPilot.Forcing.SetFormula

end OAI
