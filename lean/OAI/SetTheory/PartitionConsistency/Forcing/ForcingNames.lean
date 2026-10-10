import Mathlib
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingQuotient
import OAI.SetTheory.PartitionConsistency.Logic.GroundModels
import OAI.SetTheory.PartitionConsistency.Forcing.SupportFilter

namespace OAI

namespace PartitionConsistency.SetForcingNames
universe u v

/-- The subname relation on literal set codes. The second component of an edge
is a forcing condition; the first component is a name for a potential member. -/
def Child (τ σ : ZFSet.{u}) : Prop := ∃ p, ZFSet.pair τ p ∈ σ

theorem child_wf : WellFounded Child.{u} := by
  apply (ZFSet.mem_wf.transGen).mono
  rintro τ σ ⟨p, hp⟩
  have h₁ : Relation.TransGen (fun x y : ZFSet.{u} => x ∈ y) τ {τ} :=
    .single (by simp)
  have h₂ : Relation.TransGen (fun x y : ZFSet.{u} => x ∈ y) τ (ZFSet.pair τ p) :=
    h₁.tail (by simp [ZFSet.pair])
  exact h₂.tail hp

/-- Edges of a set name, with no choice of a presentation of that set. -/
def Edges (σ : ZFSet.{u}) := {e : ZFSet.{u} × ZFSet.{u} // ZFSet.pair e.1 e.2 ∈ σ}

instance (σ : ZFSet.{u}) : Small.{u} (Edges σ) := by
  apply small_of_injective (f := fun e : Edges σ =>
    (⟨ZFSet.pair e.val.1 e.val.2, e.property⟩ : σ))
  intro a b hab
  apply Subtype.ext
  exact Prod.ext ((ZFSet.pair_inj.mp (Subtype.ext_iff.mp hab)).1)
    ((ZFSet.pair_inj.mp (Subtype.ext_iff.mp hab)).2)

/-- Well-formed set-forcing names. This is the usual hereditary recursive
condition on sets of pairs, not a predicate on their interpreted values. -/
def IsName (P : Set ZFSet.{u}) : ZFSet.{u} → Prop :=
  child_wf.fix fun σ rec =>
    (∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p) ∧
    ∀ τ p (he : ZFSet.pair τ p ∈ σ), p ∈ P ∧ rec τ ⟨p, he⟩

theorem isName_iff {P : Set ZFSet.{u}} {σ : ZFSet.{u}} : IsName P σ ↔
    (∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p) ∧
    ∀ τ p, ZFSet.pair τ p ∈ σ → p ∈ P ∧ IsName P τ := by
  unfold IsName
  rw [WellFounded.fix_eq]

theorem IsName.intro {P : Set ZFSet.{u}} (σ : ZFSet.{u})
    (h : ∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p ∧ p ∈ P ∧ IsName P τ) : IsName P σ := by
  apply isName_iff.mpr
  refine ⟨fun z hz => ?_, fun τ p he => ?_⟩
  · obtain ⟨τ, p, hpair, _, _⟩ := h z hz
    exact ⟨τ, p, hpair⟩
  · obtain ⟨τ', p', hpair, hp', hn⟩ := h _ he
    obtain ⟨rfl, rfl⟩ := ZFSet.pair_inj.mp hpair
    exact ⟨hp', hn⟩

theorem IsName.edges {P : Set ZFSet.{u}} {σ : ZFSet.{u}} (h : IsName P σ) :
    ∀ z ∈ σ, ∃ τ p, z = ZFSet.pair τ p ∧ p ∈ P ∧ IsName P τ := by
  intro z hz
  obtain ⟨τ, p, rfl⟩ := (isName_iff.mp h).1 z hz
  exact ⟨τ, p, rfl, (isName_iff.mp h).2 τ p hz⟩

theorem IsName.child {P : Set ZFSet.{u}} {σ τ p : ZFSet.{u}}
    (h : IsName P σ) (he : ZFSet.pair τ p ∈ σ) : IsName P τ :=
  ((isName_iff.mp h).2 τ p he).2

theorem IsName.condition {P : Set ZFSet.{u}} {σ τ p : ZFSet.{u}}
    (h : IsName P σ) (he : ZFSet.pair τ p ∈ σ) : p ∈ P :=
  ((isName_iff.mp h).2 τ p he).1

theorem isName_empty (P : Set ZFSet.{u}) : IsName P ∅ :=
  .intro _ (by simp)

/-- Interpretation of actual set-name codes. At no point is the forcing order
or a maximum principle used in this recursion. -/
noncomputable def evaluate (G : Set ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  child_wf.fix fun σ rec => ZFSet.range fun e : {e : Edges σ // e.val.2 ∈ G} =>
    rec e.val.val.1 ⟨e.val.val.2, e.val.property⟩

theorem evaluate_eq (G : Set ZFSet.{u}) (σ : ZFSet.{u}) : evaluate G σ =
    ZFSet.range (fun e : {e : Edges σ // e.val.2 ∈ G} => evaluate G e.val.val.1) := by
  unfold evaluate
  rw [WellFounded.fix_eq]

theorem mem_evaluate_iff {G : Set ZFSet.{u}} {σ x : ZFSet.{u}} :
    x ∈ evaluate G σ ↔ ∃ τ p, ZFSet.pair τ p ∈ σ ∧ p ∈ G ∧ evaluate G τ = x := by
  rw [evaluate_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨τ, p⟩, he⟩, hp⟩, hx⟩
    exact ⟨τ, p, he, hp, hx⟩
  · rintro ⟨τ, p, he, hp, hx⟩
    exact ⟨⟨⟨(τ, p), he⟩, hp⟩, hx⟩

/-- Recursive transport of names by a map on condition codes. -/
noncomputable def mapConditions (f : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  child_wf.fix fun σ rec => ZFSet.range fun e : Edges σ =>
    ZFSet.pair (rec e.val.1 ⟨e.val.2, e.property⟩) (f e.val.2)

theorem mapConditions_eq (f : ZFSet.{u} → ZFSet.{u}) (σ : ZFSet.{u}) :
    mapConditions f σ = ZFSet.range (fun e : Edges σ =>
      ZFSet.pair (mapConditions f e.val.1) (f e.val.2)) := by
  unfold mapConditions
  rw [WellFounded.fix_eq]

theorem mem_mapConditions_iff {f : ZFSet.{u} → ZFSet.{u}} {σ z : ZFSet.{u}} :
    z ∈ mapConditions f σ ↔ ∃ τ p, ZFSet.pair τ p ∈ σ ∧
      ZFSet.pair (mapConditions f τ) (f p) = z := by
  rw [mapConditions_eq, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨τ, p⟩, he⟩, hz⟩
    exact ⟨τ, p, he, hz⟩
  · rintro ⟨τ, p, he, hz⟩
    exact ⟨⟨(τ, p), he⟩, hz⟩

theorem edge_mapConditions_iff {f : ZFSet.{u} → ZFSet.{u}} {σ τ p : ZFSet.{u}} :
    ZFSet.pair τ p ∈ mapConditions f σ ↔ ∃ τ' p',
      ZFSet.pair τ' p' ∈ σ ∧ mapConditions f τ' = τ ∧ f p' = p := by
  simp only [mem_mapConditions_iff, ZFSet.pair_inj]

@[simp] theorem evaluate_empty (G : Set ZFSet.{u}) : evaluate G ∅ = ∅ := by
  apply ZFSet.ext
  simp [mem_evaluate_iff]

@[simp] theorem mapConditions_empty (f : ZFSet.{u} → ZFSet.{u}) :
    mapConditions f ∅ = ∅ := by
  apply ZFSet.ext
  simp [mem_mapConditions_iff]

theorem mapConditions_id {P : Set ZFSet.{u}} {σ : ZFSet.{u}} (h : IsName P σ) :
    mapConditions id σ = σ := by
  induction σ using child_wf.induction with | h σ ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff]
  constructor
  · rintro ⟨τ, p, he, rfl⟩
    simpa only [ih τ ⟨p, he⟩ (h.child he), id_eq] using he
  · intro hz
    obtain ⟨τ, p, rfl, _, _⟩ := h.edges z hz
    exact ⟨τ, p, hz, by rw [ih τ ⟨p, hz⟩ (h.child hz)]; rfl⟩

theorem mapConditions_comp (f g : ZFSet.{u} → ZFSet.{u}) (σ : ZFSet.{u}) :
    mapConditions f (mapConditions g σ) = mapConditions (f ∘ g) σ := by
  induction σ using child_wf.induction with | h σ ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_mapConditions_iff]
  constructor
  · rintro ⟨τ, p, he, hz⟩
    obtain ⟨τ', p', he', rfl, rfl⟩ := edge_mapConditions_iff.mp he
    refine ⟨τ', p', he', ?_⟩
    simpa only [ih τ' ⟨p', he'⟩, Function.comp_apply] using hz
  · rintro ⟨τ, p, he, hz⟩
    refine ⟨mapConditions g τ, g p, edge_mapConditions_iff.mpr ⟨τ, p, he, rfl, rfl⟩, ?_⟩
    simpa only [ih τ ⟨p, he⟩, Function.comp_apply] using hz

theorem IsName.mapConditions {P Q : Set ZFSet.{u}} {f : ZFSet.{u} → ZFSet.{u}}
    (hf : ∀ p ∈ P, f p ∈ Q) {σ : ZFSet.{u}} (h : IsName P σ) :
    IsName Q (mapConditions f σ) := by
  induction σ using child_wf.induction with | h σ ih =>
  apply IsName.intro
  intro z hz
  obtain ⟨τ, p, he, rfl⟩ := mem_mapConditions_iff.mp hz
  exact ⟨_, _, rfl, hf p (h.condition he), ih τ ⟨p, he⟩ (h.child he)⟩

/-- Covariance holds with the filter transformed as well; this is not a claim
that moving a name gives an automorphism of one fixed transitive extension. -/
theorem evaluate_mapConditions (f : ZFSet.{u} → ZFSet.{u}) (G : Set ZFSet.{u})
    (σ : ZFSet.{u}) : evaluate G (mapConditions f σ) = evaluate (f ⁻¹' G) σ := by
  induction σ using child_wf.induction with | h σ ih =>
  apply ZFSet.ext
  intro x
  rw [mem_evaluate_iff, mem_evaluate_iff]
  constructor
  · rintro ⟨τ, p, he, hp, hx⟩
    obtain ⟨τ', p', he', rfl, rfl⟩ := edge_mapConditions_iff.mp he
    exact ⟨τ', p', he', hp, by simpa only [ih τ' ⟨p', he'⟩] using hx⟩
  · rintro ⟨τ, p, he, hp, hx⟩
    exact ⟨mapConditions f τ, f p, edge_mapConditions_iff.mpr ⟨τ, p, he, rfl, rfl⟩,
      hp, by simpa only [ih τ ⟨p, he⟩] using hx⟩


/-- The canonical name for a ground set, using the condition `t`. In applications
`t` is the largest condition. -/
noncomputable def checkName (t : ZFSet.{u}) : ZFSet.{u} → ZFSet.{u} :=
  ZFSet.mem_wf.fix fun x rec => ZFSet.range fun y : x => ZFSet.pair (rec y.val y.property) t

theorem checkName_eq (t x : ZFSet.{u}) :
    checkName t x = ZFSet.range (fun y : x => ZFSet.pair (checkName t y.val) t) := by
  unfold checkName
  rw [WellFounded.fix_eq]

theorem mem_checkName_iff {t x z : ZFSet.{u}} :
    z ∈ checkName t x ↔ ∃ y ∈ x, ZFSet.pair (checkName t y) t = z := by
  rw [checkName_eq, ZFSet.mem_range]
  exact ⟨fun ⟨y, hy⟩ => ⟨y.val, y.property, hy⟩, fun ⟨y, hy, hz⟩ => ⟨⟨y, hy⟩, hz⟩⟩

theorem edge_checkName_iff {t x τ p : ZFSet.{u}} :
    ZFSet.pair τ p ∈ checkName t x ↔ ∃ y ∈ x, checkName t y = τ ∧ t = p := by
  simp only [mem_checkName_iff, ZFSet.pair_inj]

theorem checkName_isName {P : Set ZFSet.{u}} {t : ZFSet.{u}} (ht : t ∈ P) (x : ZFSet.{u}) :
    IsName P (checkName t x) := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply IsName.intro
  intro z hz
  obtain ⟨y, hy, rfl⟩ := mem_checkName_iff.mp hz
  exact ⟨_, _, rfl, ht, ih y hy⟩

theorem evaluate_checkName {G : Set ZFSet.{u}} {t : ZFSet.{u}} (ht : t ∈ G)
    (x : ZFSet.{u}) : evaluate G (checkName t x) = x := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply ZFSet.ext
  intro z
  rw [mem_evaluate_iff]
  constructor
  · rintro ⟨τ, p, he, _, hz⟩
    obtain ⟨y, hy, rfl, rfl⟩ := edge_checkName_iff.mp he
    rw [ih y hy] at hz
    exact hz ▸ hy
  · intro hz
    exact ⟨checkName t z, t, edge_checkName_iff.mpr ⟨z, hz, rfl, rfl⟩, ht, ih z hz⟩

theorem mapConditions_checkName (f : ZFSet.{u} → ZFSet.{u}) (t x : ZFSet.{u}) :
    mapConditions f (checkName t x) = checkName (f t) x := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_checkName_iff]
  constructor
  · rintro ⟨τ, p, he, hz⟩
    obtain ⟨y, hy, rfl, rfl⟩ := edge_checkName_iff.mp he
    exact ⟨y, hy, by simpa only [ih y hy] using hz⟩
  · rintro ⟨y, hy, hz⟩
    exact ⟨checkName t y, t, edge_checkName_iff.mpr ⟨y, hy, rfl, rfl⟩,
      by simpa only [ih y hy] using hz⟩

/-- A literal pairing name. -/
def pairName (t σ τ : ZFSet.{u}) : ZFSet.{u} := {ZFSet.pair σ t, ZFSet.pair τ t}

theorem pairName_isName {P : Set ZFSet.{u}} {t σ τ : ZFSet.{u}}
    (ht : t ∈ P) (hσ : IsName P σ) (hτ : IsName P τ) : IsName P (pairName t σ τ) := by
  apply IsName.intro
  intro z hz
  rcases ZFSet.mem_pair.mp hz with rfl | rfl
  · exact ⟨σ, t, rfl, ht, hσ⟩
  · exact ⟨τ, t, rfl, ht, hτ⟩

theorem edge_pairName_iff {t σ τ ν p : ZFSet.{u}} :
    ZFSet.pair ν p ∈ pairName t σ τ ↔ (ν = σ ∨ ν = τ) ∧ p = t := by
  simp only [pairName, ZFSet.mem_pair, ZFSet.pair_inj, or_and_right]

theorem evaluate_pairName {G : Set ZFSet.{u}} {t : ZFSet.{u}} (ht : t ∈ G)
    (σ τ : ZFSet.{u}) : evaluate G (pairName t σ τ) = {evaluate G σ, evaluate G τ} := by
  apply ZFSet.ext
  intro x
  simp only [mem_evaluate_iff, edge_pairName_iff, ZFSet.mem_pair]
  constructor
  · rintro ⟨ν, p, ⟨(rfl | rfl), rfl⟩, _, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨σ, t, ⟨Or.inl rfl, rfl⟩, ht, rfl⟩
    · exact ⟨τ, t, ⟨Or.inr rfl, rfl⟩, ht, rfl⟩

theorem mapConditions_pairName (f : ZFSet.{u} → ZFSet.{u}) (t σ τ : ZFSet.{u}) :
    mapConditions f (pairName t σ τ) = pairName (f t) (mapConditions f σ) (mapConditions f τ) := by
  apply ZFSet.ext
  intro z
  simp only [mem_mapConditions_iff, edge_pairName_iff]
  rw [pairName, ZFSet.mem_pair]
  constructor
  · rintro ⟨ν, p, ⟨(rfl | rfl), rfl⟩, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨σ, t, ⟨Or.inl rfl, rfl⟩, rfl⟩
    · exact ⟨τ, t, ⟨Or.inr rfl, rfl⟩, rfl⟩

/-- A small type indexing the three conditions used by the union-name
construction: the two existing edge conditions and their common strengthening. -/
def UnionEdges (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : ZFSet.{u}) :=
  {e : (Σ a : Edges σ, Edges a.val.1 × P) //
    R e.2.2.val e.1.val.2 ∧ R e.2.2.val e.2.1.val.2}

instance (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : ZFSet.{u}) :
    Small.{u} (UnionEdges P R σ) := by
  unfold UnionEdges
  infer_instance

/-- The union name for an arbitrary set forcing, not necessarily one with binary
meets. Every common strengthening is included. -/
noncomputable def unionName (P : ZFSet.{u}) (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (σ : ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun e : UnionEdges P R σ => ZFSet.pair e.val.2.1.val.1 e.val.2.2.val)

theorem mem_unionName_iff {P : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {σ z : ZFSet.{u}} : z ∈ unionName P R σ ↔ ∃ χ p τ r q,
      ZFSet.pair χ p ∈ σ ∧ ZFSet.pair τ r ∈ χ ∧ q ∈ P ∧
      R q p ∧ R q r ∧ ZFSet.pair τ q = z := by
  rw [unionName, ZFSet.mem_range]
  constructor
  · rintro ⟨⟨⟨⟨⟨χ, p⟩, hp⟩, ⟨⟨⟨τ, r⟩, hr⟩, ⟨q, hq⟩⟩⟩, hqp, hqr⟩, hz⟩
    exact ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
  · rintro ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
    exact ⟨⟨⟨⟨(χ, p), hp⟩, ⟨⟨(τ, r), hr⟩, ⟨q, hq⟩⟩⟩, hqp, hqr⟩, hz⟩

theorem edge_unionName_iff {P : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {σ τ q : ZFSet.{u}} : ZFSet.pair τ q ∈ unionName P R σ ↔
      ∃ χ p r, ZFSet.pair χ p ∈ σ ∧ ZFSet.pair τ r ∈ χ ∧ q ∈ P ∧ R q p ∧ R q r := by
  simp only [mem_unionName_iff, ZFSet.pair_inj]
  constructor
  · rintro ⟨χ, p, τ', r, q', hp, hr, hq, hqp, hqr, rfl, rfl⟩
    exact ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩
  · rintro ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩
    exact ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, rfl, rfl⟩

theorem unionName_isName {P : ZFSet.{u}} (R : ZFSet.{u} → ZFSet.{u} → Prop)
    {σ : ZFSet.{u}} (hσ : IsName P σ) : IsName P (unionName P R σ) := by
  apply IsName.intro
  intro z hz
  obtain ⟨χ, p, τ, r, q, hp, hr, hq, _, _, rfl⟩ := mem_unionName_iff.mp hz
  exact ⟨τ, q, rfl, hq, (hσ.child hp).child hr⟩

/-- Interpretation of the union constructor needs precisely upward closure and
directedness of the filter. No continuity or closure of the poset is assumed. -/
theorem evaluate_unionName {P : ZFSet.{u}} {R : ZFSet.{u} → ZFSet.{u} → Prop}
    {G : Set ZFSet.{u}} (hGP : G ⊆ P)
    (hup : ∀ p ∈ P, ∀ q ∈ G, R q p → p ∈ G)
    (hdir : ∀ p ∈ G, ∀ r ∈ G, ∃ q ∈ G, R q p ∧ R q r)
    {σ : ZFSet.{u}} (hσ : IsName P σ) :
    evaluate G (unionName P R σ) = ZFSet.sUnion (evaluate G σ) := by
  apply ZFSet.ext
  intro z
  rw [mem_evaluate_iff, ZFSet.mem_sUnion]
  constructor
  · rintro ⟨τ, q, he, hq, rfl⟩
    obtain ⟨χ, p, r, hp, hr, _, hqp, hqr⟩ := edge_unionName_iff.mp he
    have hpG := hup p (hσ.condition hp) q hq hqp
    have hrG := hup r ((hσ.child hp).condition hr) q hq hqr
    exact ⟨evaluate G χ, mem_evaluate_iff.mpr ⟨χ, p, hp, hpG, rfl⟩,
      mem_evaluate_iff.mpr ⟨τ, r, hr, hrG, rfl⟩⟩
  · rintro ⟨x, hx, hz⟩
    obtain ⟨χ, p, hp, hpG, rfl⟩ := mem_evaluate_iff.mp hx
    obtain ⟨τ, r, hr, hrG, rfl⟩ := mem_evaluate_iff.mp hz
    obtain ⟨q, hq, hqp, hqr⟩ := hdir p hpG r hrG
    exact ⟨τ, q, edge_unionName_iff.mpr ⟨χ, p, r, hp, hr, hGP hq, hqp, hqr⟩, hq, rfl⟩


/-- The condition part of a symmetric system. A homomorphism into permutations
of the actual set of conditions is enough to lift the action to set names.
Preservation of the forcing order is used separately for the union constructor. -/
structure ConditionAction (Γ : Type v) [Group Γ] where
  conditions : ZFSet.{u}
  perm : Γ →* Equiv.Perm conditions

namespace ConditionAction
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

/-- Extend a permutation of the conditions by the identity on all other codes. -/
noncomputable def actCode (g : Γ) (p : ZFSet.{u}) : ZFSet.{u} := by
  classical
  exact if h : p ∈ S.conditions then (S.perm g ⟨p, h⟩).val else p

@[simp] theorem actCode_of_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∈ S.conditions) :
    S.actCode g p = (S.perm g ⟨p, hp⟩).val := by
  classical
  simp only [actCode, dite_eq_left hp]

@[simp] theorem actCode_of_not_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∉ S.conditions) :
    S.actCode g p = p := by
  classical
  simp only [actCode, dite_eq_right hp]

theorem actCode_mem (g : Γ) {p : ZFSet.{u}} (hp : p ∈ S.conditions) :
    S.actCode g p ∈ S.conditions := by
  rw [S.actCode_of_mem g hp]
  exact (S.perm g ⟨p, hp⟩).property

@[simp] theorem actCode_one (p : ZFSet.{u}) : S.actCode 1 p = p := by
  classical
  by_cases hp : p ∈ S.conditions
  · simp [actCode, hp]
  · exact S.actCode_of_not_mem 1 hp

@[simp] theorem actCode_mul (g h : Γ) (p : ZFSet.{u}) :
    S.actCode (g * h) p = S.actCode g (S.actCode h p) := by
  classical
  by_cases hp : p ∈ S.conditions
  · rw [S.actCode_of_mem (g * h) hp, S.actCode_of_mem g (S.actCode_mem h hp)]
    simp only [S.actCode_of_mem h hp, map_mul, Equiv.Perm.coe_mul, Function.comp_apply]
  · rw [S.actCode_of_not_mem _ hp, S.actCode_of_not_mem _ hp, S.actCode_of_not_mem _ hp]

@[simp] theorem actCode_inv_actCode (g : Γ) (p : ZFSet.{u}) :
    S.actCode g⁻¹ (S.actCode g p) = p := by
  rw [← S.actCode_mul, inv_mul_cancel, S.actCode_one]

@[simp] theorem actCode_actCode_inv (g : Γ) (p : ZFSet.{u}) :
    S.actCode g (S.actCode g⁻¹ p) = p := by
  rw [← S.actCode_mul, mul_inv_cancel, S.actCode_one]

theorem actCode_injective (g : Γ) : Function.Injective (S.actCode g) :=
  Function.LeftInverse.injective (S.actCode_inv_actCode g)

/-- Literal names for this condition set. Equality is equality of the underlying
ZF sets, not equality of tree presentations. -/
structure Name where
  val : ZFSet.{u}
  property : IsName S.conditions val

namespace Name
variable {S}

@[ext] theorem ext {σ τ : S.Name} (h : σ.val = τ.val) : σ = τ := by
  cases σ
  cases τ
  cases h
  rfl

noncomputable def act (g : Γ) (σ : S.Name) : S.Name :=
  ⟨mapConditions (S.actCode g) σ.val,
    σ.property.mapConditions (fun _ => S.actCode_mem g)⟩

noncomputable instance : MulAction Γ S.Name where
  smul := act
  one_smul σ := by
    apply ext
    change mapConditions (S.actCode 1) σ.val = σ.val
    have he : S.actCode 1 = id := funext S.actCode_one
    rw [he]
    exact mapConditions_id σ.property
  mul_smul g h σ := by
    apply ext
    change mapConditions (S.actCode (g * h)) σ.val =
      mapConditions (S.actCode g) (mapConditions (S.actCode h) σ.val)
    rw [mapConditions_comp]
    congr 1
    exact funext (S.actCode_mul g h)

@[simp] theorem smul_val (g : Γ) (σ : S.Name) :
    (g • σ).val = mapConditions (S.actCode g) σ.val := rfl

/-- The syntax action and evaluation transform together. -/
theorem evaluate_smul (g : Γ) (G : Set ZFSet.{u}) (σ : S.Name) :
    evaluate G (g • σ).val = evaluate (S.actCode g ⁻¹' G) σ.val :=
  evaluate_mapConditions _ _ _

/-- An edge recovers a name, with hereditary well-formedness proved from its
parent rather than imposed as an additional hypothesis. -/
def child (σ : S.Name) {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) : S.Name :=
  ⟨τ, σ.property.child he⟩

@[simp] theorem child_val (σ : S.Name) {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) :
    (σ.child he).val = τ := rfl

theorem child_wellFounded : WellFounded (fun τ σ : S.Name => Child τ.val σ.val) :=
  child_wf.onFun

/-- Canonical names in the actual condition system. -/
noncomputable def check {t : ZFSet.{u}} (ht : t ∈ S.conditions) (x : ZFSet.{u}) : S.Name :=
  ⟨checkName t x, checkName_isName ht x⟩

/-- Pairing of names in the actual condition system. -/
def pair {t : ZFSet.{u}} (ht : t ∈ S.conditions) (σ τ : S.Name) : S.Name :=
  ⟨pairName t σ.val τ.val, pairName_isName ht σ.property τ.property⟩

/-- Union of names for the chosen forcing order. -/
noncomputable def union (R : ZFSet.{u} → ZFSet.{u} → Prop) (σ : S.Name) : S.Name :=
  ⟨unionName S.conditions R σ.val, unionName_isName R σ.property⟩

@[simp] theorem smul_check {t : ZFSet.{u}} (ht : t ∈ S.conditions) (g : Γ)
    (hx : S.actCode g t = t) (x : ZFSet.{u}) :
    g • check ht x = check ht x := by
  apply ext
  change mapConditions (S.actCode g) (checkName t x) = checkName t x
  rw [mapConditions_checkName, hx]

@[simp] theorem smul_pair {t : ZFSet.{u}} (ht : t ∈ S.conditions) (g : Γ)
    (hx : S.actCode g t = t) (σ τ : S.Name) :
    g • pair ht σ τ = pair ht (g • σ) (g • τ) := by
  apply ext
  change mapConditions (S.actCode g) (pairName t σ.val τ.val) =
    pairName t (mapConditions (S.actCode g) σ.val) (mapConditions (S.actCode g) τ.val)
  rw [mapConditions_pairName, hx]

end Name
end ConditionAction


namespace ConditionAction
variable {Γ : Type v} [Group Γ] (S : ConditionAction.{u} Γ)

/-- If condition permutations preserve the order, they commute exactly with
the set-valued union-name constructor. -/
theorem mapConditions_unionName (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    (g : Γ) (σ : ZFSet.{u}) :
    mapConditions (S.actCode g) (unionName S.conditions R σ) =
      unionName S.conditions R (mapConditions (S.actCode g) σ) := by
  apply ZFSet.ext
  intro z
  rw [mem_mapConditions_iff, mem_unionName_iff]
  constructor
  · rintro ⟨τ, q, he, hz⟩
    obtain ⟨χ, p, r, hp, hr, hq, hqp, hqr⟩ := edge_unionName_iff.mp he
    exact ⟨mapConditions (S.actCode g) χ, S.actCode g p,
      mapConditions (S.actCode g) τ, S.actCode g r, S.actCode g q,
      edge_mapConditions_iff.mpr ⟨χ, p, hp, rfl, rfl⟩,
      edge_mapConditions_iff.mpr ⟨τ, r, hr, rfl, rfl⟩,
      S.actCode_mem g hq, (hR g q p).mpr hqp, (hR g q r).mpr hqr, hz⟩
  · rintro ⟨χ, p, τ, r, q, hp, hr, hq, hqp, hqr, hz⟩
    obtain ⟨χ', p', hp', rfl, rfl⟩ := edge_mapConditions_iff.mp hp
    obtain ⟨τ', r', hr', rfl, rfl⟩ := edge_mapConditions_iff.mp hr
    have hqp' : R (S.actCode g⁻¹ q) p' := by
      apply (hR g _ _).mp
      simpa only [S.actCode_actCode_inv] using hqp
    have hqr' : R (S.actCode g⁻¹ q) r' := by
      apply (hR g _ _).mp
      simpa only [S.actCode_actCode_inv] using hqr
    refine ⟨τ', S.actCode g⁻¹ q, ?_, ?_⟩
    · exact edge_unionName_iff.mpr ⟨χ', p', r', hp', hr', S.actCode_mem _ hq, hqp', hqr'⟩
    · simpa only [S.actCode_actCode_inv] using hz

namespace Name
variable {S}

@[simp] theorem smul_union (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q) (g : Γ) (σ : S.Name) :
    g • union R σ = union R (g • σ) := by
  apply ext
  exact S.mapConditions_unionName R hR g σ.val

/-- A name is symmetric when its literal set-name stabilizer belongs to the
specified subgroup filter. This does not mention its interpretation. -/
def Symmetric (F : Set (Subgroup Γ)) (σ : S.Name) : Prop :=
  MulAction.stabilizer Γ σ ∈ F

/-- Hereditary symmetry follows the subname relation, not membership of the
interpreted sets. -/
def HS (F : Set (Subgroup Γ)) : S.Name → Prop :=
  child_wellFounded.fix fun σ rec => Symmetric F σ ∧
    ∀ τ (he : Child τ.val σ.val), rec τ he

theorem hs_iff {F : Set (Subgroup Γ)} {σ : S.Name} : HS F σ ↔
    Symmetric F σ ∧ ∀ τ : S.Name, Child τ.val σ.val → HS F τ := by
  unfold HS
  rw [WellFounded.fix_eq]

theorem HS.symmetric {F : Set (Subgroup Γ)} {σ : S.Name} (h : HS F σ) :
    Symmetric F σ := (hs_iff.mp h).1

theorem HS.subname {F : Set (Subgroup Γ)} {σ τ : S.Name} (h : HS F σ)
    (he : Child τ.val σ.val) : HS F τ := (hs_iff.mp h).2 τ he

theorem HS.child {F : Set (Subgroup Γ)} {σ : S.Name} (h : HS F σ)
    {τ p : ZFSet.{u}} (he : ZFSet.pair τ p ∈ σ.val) : HS F (σ.child he) :=
  h.subname ⟨p, he⟩

/-- Normality of the subgroup filter is exactly what is needed to transport
hereditarily symmetric names. -/
theorem HS.smul {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F) (g : Γ)
    {σ : S.Name} (hσ : HS F σ) : HS F (g • σ) := by
  induction σ using child_wellFounded.induction with | h σ ih =>
  apply hs_iff.mpr
  constructor
  · change MulAction.stabilizer Γ (g • σ) ∈ F
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    exact hF.2.2.2 g _ hσ.symmetric
  · rintro τ ⟨p, hp⟩
    obtain ⟨τ', p', he, hτ', _⟩ := edge_mapConditions_iff.mp hp
    let ν : S.Name := σ.child he
    have hν : Child ν.val σ.val := ⟨p', he⟩
    have heq : g • ν = τ := ext hτ'
    rw [← heq]
    exact ih ν hν (hσ.subname hν)

def empty : S.Name := ⟨∅, isName_empty _⟩

@[simp] theorem smul_empty (g : Γ) : g • (empty : S.Name) = empty := by
  apply ext
  exact mapConditions_empty _

theorem empty_HS {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F) :
    HS F (empty : S.Name) := by
  apply hs_iff.mpr
  constructor
  · have hs : MulAction.stabilizer Γ (empty : S.Name) = ⊤ := by
      apply top_unique
      intro g _
      exact smul_empty g
    simpa only [Symmetric, hs] using htop
  · rintro τ ⟨p, hp⟩
    exact False.elim (ZFSet.notMem_empty _ hp)

theorem check_HS {F : Set (Subgroup Γ)} (htop : (⊤ : Subgroup Γ) ∈ F)
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (hfixed : ∀ g : Γ, S.actCode g t = t)
    (x : ZFSet.{u}) : HS F (check ht x) := by
  induction x using ZFSet.inductionOn with | h x ih =>
  apply hs_iff.mpr
  constructor
  · have hs : MulAction.stabilizer Γ (check ht x) = ⊤ := by
      apply top_unique
      intro g _
      exact smul_check ht g (hfixed g) x
    simpa only [Symmetric, hs] using htop
  · rintro τ ⟨p, hp⟩
    obtain ⟨y, hy, hτ, _⟩ := edge_checkName_iff.mp hp
    have heq : check ht y = τ := ext hτ
    rw [← heq]
    exact ih y hy

theorem pair_HS {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F)
    {t : ZFSet.{u}} (ht : t ∈ S.conditions) (hfixed : ∀ g : Γ, S.actCode g t = t)
    {σ τ : S.Name} (hσ : HS F σ) (hτ : HS F τ) : HS F (pair ht σ τ) := by
  apply hs_iff.mpr
  constructor
  · apply hF.2.1 (MulAction.stabilizer Γ σ ⊓ MulAction.stabilizer Γ τ)
      _ (hF.2.2.1 _ _ hσ.symmetric hτ.symmetric)
    intro g hg
    change g • pair ht σ τ = pair ht σ τ
    rw [smul_pair ht g (hfixed g), hg.1, hg.2]
  · rintro ν ⟨p, hp⟩
    obtain ⟨heq | heq, _⟩ := edge_pairName_iff.mp hp
    · exact (ext heq).symm ▸ hσ
    · exact (ext heq).symm ▸ hτ

theorem union_HS {F : Set (Subgroup Γ)} (hF : SupportFilter.IsNormalFilter F)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (hR : ∀ g p q, R (S.actCode g p) (S.actCode g q) ↔ R p q)
    {σ : S.Name} (hσ : HS F σ) : HS F (union R σ) := by
  apply hs_iff.mpr
  constructor
  · apply hF.2.1 (MulAction.stabilizer Γ σ) _ hσ.symmetric
    intro g hg
    change g • union R σ = union R σ
    rw [smul_union R hR, hg]
  · rintro τ ⟨q, hq⟩
    obtain ⟨χ, p, r, hp, hr, _, _, _⟩ := edge_unionName_iff.mp hq
    exact (hσ.child hp).subname ⟨r, hr⟩

end Name
end ConditionAction

end PartitionConsistency.SetForcingNames

end OAI
