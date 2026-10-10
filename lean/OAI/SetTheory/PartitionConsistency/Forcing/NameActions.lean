import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingNames
import OAI.SetTheory.PartitionConsistency.Logic.GroundModels

namespace OAI

namespace PartitionConsistency.SetForcingNames.ConditionAction
universe u v
variable {Γ : Type v} [Group Γ] [Small.{u} Γ] (S : ConditionAction.{u} Γ)

/-- The index set for the mixture in the support-descent argument. Both the
trigger and the original member condition are respected. -/
def MixtureEdges (R : ZFSet.{u} → ZFSet.{u} → Prop) (H : Subgroup Γ)
    (δ σ : ZFSet.{u}) :=
  {e : H × Edges σ × S.conditions //
    R e.2.2.val (S.actCode e.1.val δ) ∧
    R e.2.2.val (S.actCode e.1.val e.2.1.val.2)}

instance (R : ZFSet.{u} → ZFSet.{u} → Prop) (H : Subgroup Γ) (δ σ : ZFSet.{u}) :
    Small.{u} (S.MixtureEdges R H δ σ) := by
  unfold MixtureEdges
  infer_instance

/-- A set name formed from all translates with active triggers. Using *all*
common strengthenings is essential: a selected meet need not exist. -/
noncomputable def mixtureName (R : ZFSet.{u} → ZFSet.{u} → Prop) (H : Subgroup Γ)
    (δ σ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range fun e : S.MixtureEdges R H δ σ =>
    ZFSet.pair (mapConditions (S.actCode e.val.1.val) e.val.2.1.val.1) e.val.2.2.val

theorem mem_mixtureName_iff {R : ZFSet.{u} → ZFSet.{u} → Prop} {H : Subgroup Γ}
    {δ σ z : ZFSet.{u}} : z ∈ S.mixtureName R H δ σ ↔
    ∃ g ∈ H, ∃ τ p q, ZFSet.pair τ p ∈ σ ∧ q ∈ S.conditions ∧
      R q (S.actCode g δ) ∧ R q (S.actCode g p) ∧
      ZFSet.pair (mapConditions (S.actCode g) τ) q = z := by
  rw [mixtureName, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨g, hg⟩, ⟨⟨τ, p⟩, he⟩, ⟨q, hq⟩⟩, hδ, hp⟩, hz⟩
    exact ⟨g, hg, τ, p, q, he, hq, hδ, hp, hz⟩
  · rintro ⟨g, hg, τ, p, q, he, hq, hδ, hp, hz⟩
    exact ⟨⟨⟨⟨g, hg⟩, ⟨(τ, p), he⟩, ⟨q, hq⟩⟩, hδ, hp⟩, hz⟩

theorem edge_mixtureName_iff {R : ZFSet.{u} → ZFSet.{u} → Prop} {H : Subgroup Γ}
    {δ σ τ q : ZFSet.{u}} : ZFSet.pair τ q ∈ S.mixtureName R H δ σ ↔
    ∃ g ∈ H, ∃ ν p, ZFSet.pair ν p ∈ σ ∧ q ∈ S.conditions ∧
      R q (S.actCode g δ) ∧ R q (S.actCode g p) ∧
      mapConditions (S.actCode g) ν = τ := by
  rw [S.mem_mixtureName_iff]
  simp only [ZFSet.pair_inj]
  constructor
  · rintro ⟨g, hg, ν, p, q', he, hq, hδ, hp, hν, rfl⟩
    exact ⟨g, hg, ν, p, he, hq, hδ, hp, hν⟩
  · rintro ⟨g, hg, ν, p, he, hq, hδ, hp, hν⟩
    exact ⟨g, hg, ν, p, q, he, hq, hδ, hp, hν, rfl⟩

theorem mixtureName_isName (R : ZFSet.{u} → ZFSet.{u} → Prop) (H : Subgroup Γ)
    (δ : ZFSet.{u}) {σ : ZFSet.{u}} (hσ : IsName S.conditions σ) :
    IsName S.conditions (S.mixtureName R H δ σ) := by
  apply IsName.intro
  intro z hz
  obtain ⟨g, _, τ, p, q, he, hq, _, _, rfl⟩ := S.mem_mixtureName_iff.mp hz
  exact ⟨_, q, rfl, hq, (hσ.child he).mapConditions (fun _ => S.actCode_mem g)⟩

/-- The value is exactly the union of the values of the triggered copies.
The statement does not presume that moved conditions stay in the same filter. -/
theorem evaluate_mixtureName {R : ZFSet.{u} → ZFSet.{u} → Prop} {H : Subgroup Γ}
    {G : Set ZFSet.{u}} (hGP : G ⊆ S.conditions)
    (hup : ∀ p ∈ S.conditions, ∀ q ∈ G, R q p → p ∈ G)
    (hdir : ∀ p ∈ G, ∀ r ∈ G, ∃ q ∈ G, R q p ∧ R q r)
    {δ σ : ZFSet.{u}} (hδ : δ ∈ S.conditions) (hσ : IsName S.conditions σ) :
    evaluate G (S.mixtureName R H δ σ) = ZFSet.sUnion
      (ZFSet.range fun g : {g : H // S.actCode g.val δ ∈ G} =>
        evaluate G (mapConditions (S.actCode g.val.val) σ)) := by
  apply ZFSet.ext
  intro x
  rw [mem_evaluate_iff, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨τ, q, he0, hqG, rfl⟩
    obtain ⟨g, hg, ν, p, he, _, hqδ, hqp, rfl⟩ := S.edge_mixtureName_iff.mp he0
    have hδG := hup _ (S.actCode_mem g hδ) q hqG hqδ
    have hpG := hup _ (S.actCode_mem g (hσ.condition he)) q hqG hqp
    exact ⟨_, ZFSet.mem_range.mpr ⟨⟨⟨g, hg⟩, hδG⟩, rfl⟩,
      mem_evaluate_iff.mpr ⟨_, _, edge_mapConditions_iff.mpr ⟨ν, p, he, rfl, rfl⟩,
        hpG, rfl⟩⟩
  · rintro ⟨y, hy, hx⟩
    obtain ⟨⟨⟨g, hg⟩, hδG⟩, rfl⟩ := ZFSet.mem_range.mp hy
    obtain ⟨τ, p, he0, hpG, hτ⟩ := mem_evaluate_iff.mp hx
    obtain ⟨ν, r, he, rfl, rfl⟩ := edge_mapConditions_iff.mp he0
    obtain ⟨q, hqG, hqδ, hqp⟩ := hdir _ hδG _ hpG
    exact ⟨_, q, S.edge_mixtureName_iff.mpr ⟨g, hg, ν, r, he, hGP hqG,
      hqδ, hqp, rfl⟩, hqG, hτ⟩

omit [Small.{u} Γ] in
theorem mapConditions_actCode_mul (g h : Γ) (σ : ZFSet.{u}) :
    mapConditions (S.actCode g) (mapConditions (S.actCode h) σ) =
      mapConditions (S.actCode (g * h)) σ := by
  rw [mapConditions_comp]
  congr 1
  exact funext fun p => (S.actCode_mul g h p).symm

/-- Left multiplication by any element of the mixing subgroup permutes the
entries of the mixture literally. No equality of interpreted values is used. -/
theorem mapConditions_mixtureName (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    (H : Subgroup Γ) {g : Γ} (hg : g ∈ H) (δ σ : ZFSet.{u}) :
    mapConditions (S.actCode g) (S.mixtureName R H δ σ) = S.mixtureName R H δ σ := by
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, S.mem_mixtureName_iff]
  constructor
  · rintro ⟨τ, q, he0, hz⟩
    obtain ⟨h, hh, ν, p, he, hq, hqδ, hqp, rfl⟩ := S.edge_mixtureName_iff.mp he0
    refine ⟨g * h, H.mul_mem hg hh, ν, p, S.actCode g q, he, S.actCode_mem g hq,
      ?_, ?_, ?_⟩
    · rw [S.actCode_mul]
      exact (hR g _ _).mpr hqδ
    · rw [S.actCode_mul]
      exact (hR g _ _).mpr hqp
    · simpa only [S.mapConditions_actCode_mul] using hz
  · rintro ⟨h, hh, ν, p, q, he, hq, hqδ, hqp, hz⟩
    refine ⟨mapConditions (S.actCode (g⁻¹ * h)) ν, S.actCode g⁻¹ q, ?_, ?_⟩
    · apply S.edge_mixtureName_iff.mpr
      refine ⟨g⁻¹ * h, H.mul_mem (H.inv_mem hg) hh, ν, p, he, S.actCode_mem _ hq,
        ?_, ?_, rfl⟩
      · rw [S.actCode_mul]
        exact (hR g⁻¹ _ _).mpr hqδ
      · rw [S.actCode_mul]
        exact (hR g⁻¹ _ _).mpr hqp
    · simpa only [S.mapConditions_actCode_mul, mul_inv_cancel_left,
        S.actCode_actCode_inv] using hz

namespace Name
variable {S}

/-- Literal mixture of names, with no fixed name-rank cutoff. -/
noncomputable def mixture (R : ZFSet.{u} → ZFSet.{u} → Prop) (H : Subgroup Γ)
    (δ : ZFSet.{u}) (σ : S.Name) : S.Name :=
  ⟨S.mixtureName R H δ σ.val, S.mixtureName_isName R H δ σ.property⟩

theorem smul_mixture (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    (H : Subgroup Γ) {g : Γ} (hg : g ∈ H) (δ : ZFSet.{u}) (σ : S.Name) :
    g • mixture R H δ σ = mixture R H δ σ := by
  apply ext
  exact S.mapConditions_mixtureName R hR H hg δ σ.val

/-- The descent constructor is HS when the mixing subgroup is in the normal
filter. Its subnames are actual translates of subnames of the original. -/
theorem mixture_HS {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    (H : Subgroup Γ) (hH : H ∈ F) (δ : ZFSet.{u}) {σ : S.Name} (hσ : HS F σ) :
    HS F (mixture R H δ σ) := by
  apply hs_iff.mpr
  constructor
  · apply hF.2.1 H _ hH
    intro g hg
    exact smul_mixture R hR H hg δ σ
  · rintro τ ⟨q, hq⟩
    obtain ⟨g, _, ν, p, he, _, _, _, hν⟩ := S.edge_mixtureName_iff.mp hq
    have heq : g • σ.child he = τ := ext hν
    rw [← heq]
    exact (hσ.child he).smul hF g

/-- Once coherence of active copies has been established, the mixture is a
name for their common value. Coherence itself is a separate forcing argument. -/
theorem evaluate_mixture_eq {R : ZFSet.{u} → ZFSet.{u} → Prop} {H : Subgroup Γ}
    {G : Set ZFSet.{u}} (hGP : G ⊆ S.conditions)
    (hup : ∀ p ∈ S.conditions, ∀ q ∈ G, R q p → p ∈ G)
    (hdir : ∀ p ∈ G, ∀ r ∈ G, ∃ q ∈ G, R q p ∧ R q r)
    {δ : ZFSet.{u}} (hδ : δ ∈ G) (σ : S.Name)
    (hcoh : ∀ g ∈ H, S.actCode g δ ∈ G → evaluate G (g • σ).val = evaluate G σ.val) :
    evaluate G (mixture R H δ σ).val = evaluate G σ.val := by
  rw [mixture, S.evaluate_mixtureName hGP hup hdir (hGP hδ) σ.property]
  apply ZFSet.ext
  intro x
  rw [ZFSet.mem_sUnion]
  constructor
  · rintro ⟨y, hy, hx⟩
    obtain ⟨⟨⟨g, hg⟩, hδg⟩, rfl⟩ := ZFSet.mem_range.mp hy
    exact hcoh g hg hδg ▸ hx
  · intro hx
    refine ⟨evaluate G σ.val, ?_, hx⟩
    apply ZFSet.mem_range.mpr
    refine ⟨⟨⟨1, H.one_mem⟩, ?_⟩, ?_⟩
    · simpa only [S.actCode_one] using hδ
    · exact hcoh 1 H.one_mem (by simpa only [S.actCode_one] using hδ)

end Name
end PartitionConsistency.SetForcingNames.ConditionAction

namespace PartitionConsistency.TransitiveSets
universe u
open Formula SetLanguage

/-- Usual external transitivity of an actual collection of pure sets. -/
def IsTransitive (M : Set ZFSet.{u}) : Prop := ∀ a ∈ M, ∀ b ∈ a, b ∈ M

/-- Internal membership is literal membership, restricted to the collection. -/
def E (M : Set ZFSet.{u}) (a b : M) : Prop := a.val ∈ b.val

variable {M : Set ZFSet.{u}}

theorem IsTransitive.pair_left (hM : IsTransitive M) {a b : ZFSet.{u}}
    (hp : ZFSet.pair a b ∈ M) : a ∈ M :=
  hM _ (hM _ hp {a} (by simp [ZFSet.pair])) a (by simp)

theorem IsTransitive.pair_right (hM : IsTransitive M) {a b : ZFSet.{u}}
    (hp : ZFSet.pair a b ∈ M) : b ∈ M :=
  hM _ (hM _ hp {a, b} (by simp [ZFSet.pair])) b (by simp)

/-- An active subname of a name in a transitive ground is itself in the ground. -/
theorem IsTransitive.child (hM : IsTransitive M) {σ τ : ZFSet.{u}}
    (hσ : σ ∈ M) (he : SetForcingNames.Child τ σ) : τ ∈ M := by
  obtain ⟨p, hp⟩ := he
  exact hM.pair_left (hM σ hσ _ hp)

theorem realize_subset (hM : IsTransitive M) {n} (v : Fin n → M) (a b : Fin n) :
    Realize (E M) v (subset a b) ↔ (v a).val ⊆ (v b).val := by
  have h : Realize (E M) v (subset a b) ↔
      ∀ x : M, x.val ∈ (v a).val → x.val ∈ (v b).val := by
    simp [subset, Realize, Fin.snoc, Fin.castLT, E]
  rw [h]
  constructor
  · intro h x hx
    exact h ⟨x, hM _ (v a).property x hx⟩ hx
  · exact fun h x hx => h hx

theorem realize_empty (hM : IsTransitive M) {n} (v : Fin n → M) (a : Fin n) :
    Realize (E M) v (empty a) ↔ (v a).val = ∅ := by
  have h : Realize (E M) v (empty a) ↔ ∀ x : M, x.val ∉ (v a).val := by
    simp [empty, Realize, Fin.snoc, Fin.castLT, E]
  rw [h, ZFSet.eq_empty]
  constructor
  · exact fun h x hx => h ⟨x, hM _ (v a).property x hx⟩ hx
  · exact fun h x => h x.val

theorem realize_nonempty (hM : IsTransitive M) {n} (v : Fin n → M) (a : Fin n) :
    Realize (E M) v (nonempty a) ↔ ∃ x, x ∈ (v a).val := by
  have h : Realize (E M) v (nonempty a) ↔ ∃ x : M, x.val ∈ (v a).val := by
    simp [nonempty, Realize, Fin.snoc, Fin.castLT, E]
  rw [h]
  exact ⟨fun ⟨x, hx⟩ => ⟨x.val, hx⟩,
    fun ⟨x, hx⟩ => ⟨⟨x, hM _ (v a).property x hx⟩, hx⟩⟩

theorem realize_pair (hM : IsTransitive M) {n} (v : Fin n → M) (p x y : Fin n) :
    Realize (E M) v (unorderedPair p x y) ↔
      (v p).val = ({(v x).val, (v y).val} : ZFSet.{u}) := by
  have h : Realize (E M) v (unorderedPair p x y) ↔
      ∀ z : M, z.val ∈ (v p).val ↔ z = v x ∨ z = v y := by
    simp [unorderedPair, Realize, Fin.snoc, Fin.castLT, E, ← iff_def]
  rw [h, ZFSet.ext_iff]
  constructor
  · intro h z
    rw [ZFSet.mem_pair]
    constructor
    · intro hz
      rcases (h ⟨z, hM _ (v p).property z hz⟩).mp hz with hz | hz
      · exact Or.inl (congrArg Subtype.val hz)
      · exact Or.inr (congrArg Subtype.val hz)
    · rintro (rfl | rfl)
      · exact (h (v x)).mpr (Or.inl rfl)
      · exact (h (v y)).mpr (Or.inr rfl)
  · intro h z
    rw [h, ZFSet.mem_pair]
    exact or_congr Subtype.ext_iff.symm Subtype.ext_iff.symm

theorem realize_orderedPair (hM : IsTransitive M) {n} (v : Fin n → M) (p x y : Fin n) :
    Realize (E M) v (orderedPair p x y) ↔
      (v p).val = ZFSet.pair (v x).val (v y).val := by
  have h : Realize (E M) v (orderedPair p x y) ↔
      ∃ a b : M, a.val = ({(v x).val, (v x).val} : ZFSet.{u}) ∧
        b.val = ({(v x).val, (v y).val} : ZFSet.{u}) ∧
        (v p).val = ({a.val, b.val} : ZFSet.{u}) := by
    simp [orderedPair, Realize, realize_pair hM, Fin.snoc, Fin.castLT]
  rw [h]
  constructor
  · rintro ⟨a, b, ha, hb, hp⟩
    rw [hp, ha, hb, ZFSet.pair, ZFSet.pair_eq_singleton]
  · intro hp
    have h₁ : ({(v x).val} : ZFSet.{u}) ∈ M :=
      hM _ (v p).property _ (by simp [hp, ZFSet.pair])
    have h₂ : ({(v x).val, (v y).val} : ZFSet.{u}) ∈ M :=
      hM _ (v p).property _ (by simp [hp, ZFSet.pair])
    exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩, (ZFSet.pair_eq_singleton _).symm, rfl, hp⟩

theorem realize_edge (hM : IsTransitive M) {n} (v : Fin n → M) (f x y : Fin n) :
    Realize (E M) v (edge f x y) ↔ ZFSet.pair (v x).val (v y).val ∈ (v f).val := by
  have h : Realize (E M) v (edge f x y) ↔
      ∃ p : M, p.val ∈ (v f).val ∧ p.val = ZFSet.pair (v x).val (v y).val := by
    simp [edge, Realize, realize_orderedPair hM, Fin.snoc, Fin.castLT, E]
  rw [h]
  constructor
  · rintro ⟨p, hp, he⟩
    exact he ▸ hp
  · intro hp
    exact ⟨⟨_, hM _ (v f).property _ hp⟩, hp, rfl⟩

/-- Extensionality is inherited by every transitive collection of actual sets. -/
theorem extensionality_true (hM : IsTransitive M) :
    Realize (E M) Fin.elim0 extensionality := by
  change ∀ a b : M, (∀ x : M, (E M x a → E M x b) ∧ (E M x b → E M x a)) → a = b
  intro a b h
  apply Subtype.ext
  apply ZFSet.ext
  intro x
  constructor
  · intro hx
    exact (h ⟨x, hM _ a.property x hx⟩).1 hx
  · intro hx
    exact (h ⟨x, hM _ b.property x hx⟩).2 hx

/-- Foundation is inherited, including when the collection is not closed under
arbitrary subsets. This uses actual membership, not a purported action on values. -/
theorem foundation_true (hM : IsTransitive M) :
    Realize (E M) Fin.elim0 foundation := by
  simp only [foundation, Realize, realize_nonempty hM]
  intro a ha
  change ∃ x, x ∈ a.val at ha
  change ∃ b : M, b.val ∈ a.val ∧ ∀ x : M, x.val ∈ b.val → x.val ∉ a.val
  have hne : a.val ≠ ∅ := by
    rintro he
    have := ha
    rw [he] at this
    simp at this
  obtain ⟨b, hb, hi⟩ := ZFSet.regularity a.val hne
  refine ⟨⟨b, hM _ a.property b hb⟩, hb, ?_⟩
  intro x hx hxa
  exact ZFSet.notMem_empty x.val (hi ▸ ZFSet.mem_inter.mpr ⟨hxa, hx⟩)

variable (hM : IsTransitive M) (hZF : Models (E M) SetLanguage.ZF)
include hM hZF

/-- Closure under the empty set follows from the actual first-order ground axiom. -/
theorem empty_mem : (∅ : ZFSet.{u}) ∈ M := by
  obtain ⟨a, ha⟩ := hZF _ IsZFAxiom.emptySet
  have he : a.val = ∅ := (realize_empty hM _ _).mp ha
  exact he ▸ a.property

/-- Literal unordered pairing is absolute for a transitive ZF ground. -/
theorem pair_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ({a, b} : ZFSet.{u}) ∈ M := by
  obtain ⟨p, hp⟩ := hZF _ IsZFAxiom.pairing ⟨a, ha⟩ ⟨b, hb⟩
  have he : p.val = ({a, b} : ZFSet.{u}) := (realize_pair hM _ _ _ _).mp hp
  exact he ▸ p.property

theorem singleton_mem {a : ZFSet.{u}} (ha : a ∈ M) : ({a} : ZFSet.{u}) ∈ M := by
  simpa only [ZFSet.pair_eq_singleton] using pair_mem hM hZF ha ha

theorem orderedPair_mem {a b : ZFSet.{u}} (ha : a ∈ M) (hb : b ∈ M) :
    ZFSet.pair a b ∈ M :=
  pair_mem hM hZF (singleton_mem hM hZF ha) (pair_mem hM hZF ha hb)

/-- Union is also absolute; no closure under all external subsets is asserted. -/
theorem sUnion_mem {a : ZFSet.{u}} (ha : a ∈ M) : ZFSet.sUnion a ∈ M := by
  obtain ⟨b, hb⟩ := hZF _ IsZFAxiom.union ⟨a, ha⟩
  have he : b.val = ZFSet.sUnion a := by
    apply ZFSet.ext
    intro x
    constructor
    · intro hx
      let xm : M := ⟨x, hM _ b.property x hx⟩
      obtain ⟨y, hy, hxy⟩ := (hb xm).1 hx
      exact ZFSet.mem_sUnion.mpr ⟨y.val, hy, hxy⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := ZFSet.mem_sUnion.mp hx
      let ym : M := ⟨y, hM a ha y hy⟩
      let xm : M := ⟨x, hM _ ym.property x hxy⟩
      exact (hb xm).2 ⟨ym, hy, hxy⟩
  exact he ▸ b.property

/-- The Separation schema yields every formula-defined relative subset, with
parameters in the ground. The subset predicate is internal satisfaction. -/
theorem separation_mem {n} (φ : Formula (n + 1)) (v : Fin n → M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ZFSet.sep (fun x => ∃ hx : x ∈ M, Realize (E M) (Fin.snoc v ⟨x, hx⟩) φ) a ∈ M := by
  obtain ⟨b, hb⟩ := (SetLanguage.realize_separation (E M) φ).mp
    (hZF _ (IsZFAxiom.separation φ)) v ⟨a, ha⟩
  have he : b.val = ZFSet.sep
      (fun x => ∃ hx : x ∈ M, Realize (E M) (Fin.snoc v ⟨x, hx⟩) φ) a := by
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_sep]
    constructor
    · intro hx
      let xm : M := ⟨x, hM _ b.property x hx⟩
      obtain ⟨hxa, hφ⟩ := (hb xm).mp hx
      exact ⟨hxa, xm.property, hφ⟩
    · rintro ⟨hxa, hxM, hφ⟩
      exact (hb ⟨x, hxM⟩).mpr ⟨hxa, hφ⟩
  exact he ▸ b.property

end PartitionConsistency.TransitiveSets

namespace PartitionConsistency.SetForcingNames.ConditionAction
universe u v
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

/-- The actual symmetric interpretation of ground set-name codes. Membership
in this domain is witnessed by a ground HS name, not by a required target axiom. -/
def symmetricValues (M : Set ZFSet.{u}) (F : Set (Subgroup Γ))
    (G : Set ZFSet.{u}) : Set ZFSet.{u} :=
  {x | ∃ σ : S.Name, σ.val ∈ M ∧ Name.HS F σ ∧ evaluate G σ.val = x}

/-- Hereditary symmetry and transitivity of the ground make the interpretation
transitive. No filter genericity or rank restriction is needed for this fact. -/
theorem symmetricValues_transitive {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (F : Set (Subgroup Γ)) (G : Set ZFSet.{u}) :
    TransitiveSets.IsTransitive (S.symmetricValues M F G) := by
  rintro x ⟨σ, hσM, hσ, rfl⟩ y hy
  obtain ⟨τ, p, he, _, hτ⟩ := mem_evaluate_iff.mp hy
  exact ⟨σ.child he, hM.child hσM ⟨p, he⟩, hσ.child he, hτ⟩

/-- A countable ground gives a countable actual symmetric interpretation. -/
theorem symmetricValues_countable {M : Set ZFSet.{u}} (hc : M.Countable)
    (F : Set (Subgroup Γ)) (G : Set ZFSet.{u}) : (S.symmetricValues M F G).Countable := by
  apply (hc.image (evaluate G)).mono
  rintro x ⟨σ, hM, _, hx⟩
  exact ⟨σ.val, hM, hx⟩

theorem symmetricValues_extensionality {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (F : Set (Subgroup Γ)) (G : Set ZFSet.{u}) :
    Formula.Realize (TransitiveSets.E (S.symmetricValues M F G)) Fin.elim0
      SetLanguage.extensionality :=
  TransitiveSets.extensionality_true (S.symmetricValues_transitive hM F G)

theorem symmetricValues_foundation {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (F : Set (Subgroup Γ)) (G : Set ZFSet.{u}) :
    Formula.Realize (TransitiveSets.E (S.symmetricValues M F G)) Fin.elim0
      SetLanguage.foundation :=
  TransitiveSets.foundation_true (S.symmetricValues_transitive hM F G)

theorem empty_mem_symmetricValues {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (hZF : Models (TransitiveSets.E M) SetLanguage.ZF)
    {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F) (G : Set ZFSet.{u}) :
    (∅ : ZFSet.{u}) ∈ S.symmetricValues M F G :=
  ⟨Name.empty, TransitiveSets.empty_mem hM hZF, Name.empty_HS htop, evaluate_empty G⟩

theorem pair_mem_symmetricValues {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (hZF : Models (TransitiveSets.E M) SetLanguage.ZF)
    {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F) {G : Set ZFSet.{u}}
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (htM : t ∈ M) (htG : t ∈ G)
    (hfixed : ∀ g : Γ, S.actCode g t = t)
    {x y : ZFSet.{u}} (hx : x ∈ S.symmetricValues M F G) (hy : y ∈ S.symmetricValues M F G) :
    ({x, y} : ZFSet.{u}) ∈ S.symmetricValues M F G := by
  obtain ⟨σ, hσM, hσ, rfl⟩ := hx
  obtain ⟨τ, hτM, hτ, rfl⟩ := hy
  refine ⟨Name.pair ht σ τ, ?_, Name.pair_HS hF ht hfixed hσ hτ,
    evaluate_pairName htG σ.val τ.val⟩
  exact TransitiveSets.pair_mem hM hZF
    (TransitiveSets.orderedPair_mem hM hZF hσM htM)
    (TransitiveSets.orderedPair_mem hM hZF hτM htM)

/-- This is only the empty-set axiom, not an assertion of the full symmetric
model theorem or of its Separation and Replacement schemas. -/
theorem symmetricValues_emptySet {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (hZF : Models (TransitiveSets.E M) SetLanguage.ZF)
    {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F) (G : Set ZFSet.{u}) :
    Formula.Realize (TransitiveSets.E (S.symmetricValues M F G)) Fin.elim0
      SetLanguage.emptySet := by
  refine ⟨⟨∅, S.empty_mem_symmetricValues hM hZF htop G⟩, ?_⟩
  exact (TransitiveSets.realize_empty (S.symmetricValues_transitive hM F G) _ _).mpr rfl

/-- Pairing holds with the actual ground pairing-name code as witness. -/
theorem symmetricValues_pairing {M : Set ZFSet.{u}}
    (hM : TransitiveSets.IsTransitive M) (hZF : Models (TransitiveSets.E M) SetLanguage.ZF)
    {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F) {G : Set ZFSet.{u}}
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (htM : t ∈ M) (htG : t ∈ G)
    (hfixed : ∀ g : Γ, S.actCode g t = t) :
    Formula.Realize (TransitiveSets.E (S.symmetricValues M F G)) Fin.elim0
      SetLanguage.pairing := by
  intro x y
  refine ⟨⟨{x.val, y.val}, S.pair_mem_symmetricValues hM hZF hF ht htM htG hfixed
    x.property y.property⟩, ?_⟩
  exact (TransitiveSets.realize_pair (S.symmetricValues_transitive hM F G) _ _ _ _).mpr rfl

end PartitionConsistency.SetForcingNames.ConditionAction

end OAI
