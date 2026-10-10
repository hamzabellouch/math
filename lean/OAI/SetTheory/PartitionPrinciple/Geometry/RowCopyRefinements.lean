import OAI.SetTheory.PartitionPrinciple.Forcing.NameMixingRanks
import OAI.SetTheory.PartitionPrinciple.Forcing.RowNames

namespace OAI

section

namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun CountableCondition

def Bounds (p : RowForcing) (D : FinalPoint Column) : Prop :=
  ∀ i : Position, ∀ α : Column, p.value (i, α) ≠ none → (finalOrder Column).le i.val D

theorem bounds_mono {p : RowForcing} {D E : FinalPoint Column}
    (bounded : Bounds p D) (lower : (finalOrder Column).le D E) : Bounds p E :=
  fun i α hi => (finalOrder Column).trans (bounded i α hi) lower

theorem bounds_action {p : RowForcing} {D : FinalPoint Column}
    (bounded : Bounds p D) (g : FinalActor Column) :
    Bounds (rowAction g p) (((finalAction Column).iso g).toFun D) := by
  intro i α hi
  let j := (positionPermutation g).symm i
  have gj : positionAction g j = i := (positionPermutation g).apply_symm_apply i
  have val := rowAction_value g p j α
  rw [gj] at val
  have lower := (((finalAction Column).iso g).le_iff _ _).2
    (bounded j α (val ▸ hi))
  change (finalOrder Column).le (positionAction g j).val _ at lower
  simpa only [gj] using lower

theorem bounds_with (p : RowForcing) (extra : Set (FinalPoint Column))
    (small : extra.Countable) :
    ∃ D, Bounds p D ∧ ∀ x ∈ extra, (finalOrder Column).le x D := by
  let positions : Set (FinalPoint Column) := (fun c : Position × Column => c.1.val) '' p.domain
  have countable : positions.Countable := p.countable_domain.image (fun c => c.1.val)
  obtain ⟨D, bound⟩ := final_countable_upper_bound Column (positions ∪ extra) (countable.union small)
  exact ⟨D, fun i α hi => bound i.val (Or.inl ⟨(i, α), hi, rfl⟩),
    fun x hx => bound x (Or.inr hx)⟩

theorem aligned_agrees {p r : RowForcing} {D X V₀ : FinalPoint Column}
    {g h : FinalActor Column} (bp : Bounds p D) (br : Bounds r X)
    (reference : r ≤ rowAction g p)
    (overlap : (finalOrder Column).meet (((finalAction Column).iso h).toFun D) X =
      ((finalAction Column).iso h).toFun V₀)
    (agree : ∀ z, (finalOrder Column).le z V₀ →
      ((finalAction Column).iso h).toFun z = ((finalAction Column).iso g).toFun z) :
    Agrees r (rowAction h p) := by
  rintro ⟨i, α⟩ a b ra hb
  have ri := br i α (by rw [ra]; exact Option.some_ne_none a)
  have hi := bounds_action bp h i α (by rw [hb]; exact Option.some_ne_none b)
  have below := (finalOrder Column).le_meet hi ri
  rw [overlap] at below
  let j := (positionPermutation h).symm i
  have hj : positionAction h j = i := (positionPermutation h).apply_symm_apply i
  have old : (finalOrder Column).le j.val V₀ := by
    apply (((finalAction Column).iso h).le_iff _ _).1
    change (finalOrder Column).le (positionAction h j).val _
    simpa only [hj] using below
  have gj : positionAction g j = i := by
    apply Subtype.ext
    exact (agree j.val old).symm.trans (congrArg Subtype.val hj)
  have pv := rowAction_value h p j α
  rw [hj, hb] at pv
  have gv := rowAction_value g p j α
  rw [gj, ← pv] at gv
  have rb := reference (i, α) b gv
  exact Option.some.inj (ra.symm.trans rb)

theorem one_copy_union {p r : RowForcing} {D X V₀ : FinalPoint Column}
    {g h : FinalActor Column} (bp : Bounds p D) (br : Bounds r X)
    (reference : r ≤ rowAction g p)
    (overlap : (finalOrder Column).meet (((finalAction Column).iso h).toFun D) X =
      ((finalAction Column).iso h).toFun V₀)
    (agree : ∀ z, (finalOrder Column).le z V₀ →
      ((finalAction Column).iso h).toFun z = ((finalAction Column).iso g).toFun z) :
    ∃ t, t ≤ r ∧ t ≤ rowAction h p :=
  ⟨merge r (rowAction h p), merge_le_left _ _,
    merge_le_right (aligned_agrees bp br reference overlap agree)⟩

theorem rectangle_union {p r : RowForcing} {D X C B : FinalPoint Column}
    {g₁ g₂ h₁ h₂ : FinalActor Column} (bp : Bounds p D) (br : Bounds r X)
    (ref₁ : r ≤ rowAction g₁ p) (ref₂ : r ≤ rowAction g₂ p)
    (agree₁ : ∀ z, (finalOrder Column).le z C →
      ((finalAction Column).iso h₁).toFun z = ((finalAction Column).iso g₁).toFun z)
    (agree₂ : ∀ z, (finalOrder Column).le z C →
      ((finalAction Column).iso h₂).toFun z = ((finalAction Column).iso g₂).toFun z)
    (agreeB : ∀ z, (finalOrder Column).le z B →
      ((finalAction Column).iso h₁).toFun z = ((finalAction Column).iso h₂).toFun z)
    (overlap₁ : (finalOrder Column).meet (((finalAction Column).iso h₁).toFun D) X =
      ((finalAction Column).iso h₁).toFun C)
    (overlap₂ : (finalOrder Column).meet (((finalAction Column).iso h₂).toFun D) X =
      ((finalAction Column).iso h₂).toFun C)
    (pairOverlap : (finalOrder Column).meet (((finalAction Column).iso h₁).toFun D)
      (((finalAction Column).iso h₂).toFun D) = ((finalAction Column).iso h₁).toFun B) :
    ∃ t, t ≤ r ∧ t ≤ rowAction h₁ p ∧ t ≤ rowAction h₂ p := by
  have one := aligned_agrees bp br ref₁ overlap₁ agree₁
  have two := aligned_agrees bp br ref₂ overlap₂ agree₂
  have pair := aligned_agrees bp (bounds_action bp h₂) le_rfl pairOverlap agreeB
  exact three_agree_common one two (agrees_symm pair)

end PartitionPilot.Forcing.Rows



namespace PartitionPilot.Forcing.PosetAction

open SetRealization Compression.RecursiveMaps
universe u v
variable {G : Type v} [Group G] {P : Type u} [PartialOrder P]
variable (a : PosetAction G P) (s : Presentation P)

def RectangleWitness (p : P) (x y : Name s) (g₁ g₂ : G) : Set P :=
  {q | ∃ h₁ h₂, q ≤ a.iso h₁ p ∧ q ≤ a.iso h₂ p ∧
    a.act s h₁ x = a.act s g₁ x ∧ a.act s h₂ x = a.act s g₂ x ∧
    a.act s h₁ y = a.act s h₂ y}

def SeparationWitness (K : Subgroup G) (Sep : G → G → Prop) (p : P) (g₁ g₂ : G) : Set P :=
  {q | ∃ h ∈ K, q ≤ a.iso h p ∧ Sep h g₁ ∧ Sep h g₂}

def copyWitnessFamily (K : Subgroup G) (Sep : G → G → Prop) (p : P) (x y : Name s) :
    Set (Set P) :=
  {D | (∃ r g₁ g₂, D = Localized r (a.RectangleWitness s p x y g₁ g₂)) ∨
    ∃ r g₁ g₂, D = Localized r (a.SeparationWitness K Sep p g₁ g₂)}

theorem separated_copies_agree (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y))
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    {g₁ g₂ : G} (hg₁ : g₁ ∈ K) (hg₂ : g₂ ∈ K) (sep : Sep g₁ g₂)
    (active₁ : H.mem (a.iso g₁ p)) (active₂ : H.mem (a.iso g₂ p)) :
    Name.eval {q | H.mem q} (a.act s g₁ x) = Name.eval {q | H.mem q} (a.act s g₂ x) := by
  obtain ⟨r, hr, r₁, r₂⟩ := H.directed active₁ active₂
  obtain ⟨q, hq, h₁, h₂, q₁, q₂, hx₁, hx₂, hy⟩ :=
    H.meets_below generic hr (Or.inl ⟨r, g₁, g₂, rfl⟩)
      (rectangles g₁ hg₁ g₂ hg₂ sep r r₁ r₂)
  have eq₁ := xy h₁ (H.upward hq q₁)
  have eq₂ := xy h₂ (H.upward hq q₂)
  rw [hx₁] at eq₁
  rw [hx₂] at eq₂
  exact eq₁.trans ((congrArg (Name.eval {q | H.mem q}) hy).trans eq₂.symm)

theorem active_copies_agree (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y))
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separation : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.SeparationWitness K Sep p g₁ g₂))
    {g₁ g₂ : G} (hg₁ : g₁ ∈ K) (hg₂ : g₂ ∈ K)
    (active₁ : H.mem (a.iso g₁ p)) (active₂ : H.mem (a.iso g₂ p)) :
    Name.eval {q | H.mem q} (a.act s g₁ x) = Name.eval {q | H.mem q} (a.act s g₂ x) := by
  obtain ⟨r, hr, r₁, r₂⟩ := H.directed active₁ active₂
  obtain ⟨q, hq, h, hh, qh, sep₁, sep₂⟩ :=
    H.meets_below generic hr (Or.inr ⟨r, g₁, g₂, rfl⟩)
      (separation g₁ hg₁ g₂ hg₂ r r₁ r₂)
  have active := H.upward hq qh
  have eq₁ := a.separated_copies_agree s K Sep p x y H generic xy rectangles hh hg₁ sep₁ active active₁
  have eq₂ := a.separated_copies_agree s K Sep p x y H generic xy rectangles hh hg₂ sep₂ active active₂
  exact eq₁.symm.trans eq₂

theorem mix_capture_from_refinements [Small.{u} G] (K : Subgroup G) (Sep : G → G → Prop)
    (p : P) (x y : Name s) (H : ConditionFilter P)
    (generic : H.GenericFor (a.copyWitnessFamily s K Sep p x y)) (hp : H.mem p)
    (xy : ∀ g, H.mem (a.iso g p) →
      Name.eval {q | H.mem q} (a.act s g x) = Name.eval {q | H.mem q} (a.act s g y))
    (rectangles : ∀ g₁ ∈ K, ∀ g₂ ∈ K, Sep g₁ g₂ → ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.RectangleWitness s p x y g₁ g₂))
    (separation : ∀ g₁ ∈ K, ∀ g₂ ∈ K, ∀ r,
      r ≤ a.iso g₁ p → r ≤ a.iso g₂ p → DenseBelow r (a.SeparationWitness K Sep p g₁ g₂)) :
    Name.eval {q | H.mem q} (a.mix s K p x) = Name.eval {q | H.mem q} x := by
  apply a.eval_mix_of_active_equal s K p x H hp
  intro g hg active
  have eq := a.active_copies_agree s K Sep p x y H generic xy rectangles separation
    hg K.one_mem active (by simpa only [a.one] using hp)
  simpa only [a.act_one] using eq

end PartitionPilot.Forcing.PosetAction



namespace PartitionPilot.Forcing.Rows

open Compression.RecursiveMaps Compression.RecursiveMaps.CountableColumns
open Compression.RecursiveMaps.MainStage.OrdinalRun

local notation "L" => finalOrder Column
local notation "geom" => finalAction Column

def Separated (D W : FinalPoint Column) (g h : FinalActor Column) : Prop :=
  (L).meet (((geom).iso g).toFun D) (((geom).iso h).toFun D) = W

theorem fixed_lower_image {W D : FinalPoint Column} {g : FinalActor Column}
    (wd : (L).le W D) (hg : g ∈ (geom).fixSubgroup W) : (L).le W (((geom).iso g).toFun D) := by
  have lower := (((geom).iso g).le_iff _ _).2 wd
  rw [hg W ((L).refl W)] at lower
  exact lower

theorem rectangle_refinement (p : RowForcing) (C B D : FinalPoint Column)
    (x y : Name namePresentation) (bp : Bounds p D) (cd : (L).le C D) (bd : (L).le B D)
    (sx : (geom).fixSubgroup C ≤ posetAction.stabilizer namePresentation x)
    (sy : (geom).fixSubgroup B ≤ posetAction.stabilizer namePresentation y)
    (g₁ : FinalActor Column) (hg₁ : g₁ ∈ (geom).fixSubgroup ((L).meet C B))
    (g₂ : FinalActor Column) (hg₂ : g₂ ∈ (geom).fixSubgroup ((L).meet C B))
    (sep : Separated D ((L).meet C B) g₁ g₂) (r : RowForcing)
    (ref₁ : r ≤ rowAction g₁ p) (ref₂ : r ≤ rowAction g₂ p) :
    DenseBelow r (posetAction.RectangleWitness namePresentation p x y g₁ g₂) := by
  intro q qr
  obtain ⟨X, bq, upper⟩ := bounds_with q
    {(((geom).iso g₁).toFun D), (((geom).iso g₂).toFun D)} ((Set.countable_singleton _).insert _)
  let rect : ActionRectangle L (geom).iso := {
    C := C, B := B, D := D, first := g₁, second := g₂,
    C_le_D := cd, B_le_D := bd,
    agree := fun z hz => (hg₁ z hz).trans (hg₂ z hz).symm,
    separated := sep.trans (hg₁ ((L).meet C B) ((L).refl _)).symm }
  obtain ⟨h₁, h₂, agree₁, agree₂, agreeB, meet₁, meet₂, pairMeet⟩ :=
    final_rectangles Column rect X (upper _ (by simp [rect])) (upper _ (by simp [rect]))
  have overlap₁ : (L).meet (((geom).iso h₁).toFun D) X = ((geom).iso h₁).toFun C :=
    meet₁.trans (agree₁ C ((L).refl C)).symm
  have overlap₂ : (L).meet (((geom).iso h₂).toFun D) X = ((geom).iso h₂).toFun C :=
    meet₂.trans (agree₂ C ((L).refl C)).symm
  obtain ⟨t, tq, th₁, th₂⟩ := rectangle_union bp bq (le_trans qr ref₁) (le_trans qr ref₂)
    agree₁ agree₂ agreeB overlap₁ overlap₂ pairMeet
  exact ⟨t, tq, h₁, h₂, th₁, th₂,
    posetAction.act_eq_of_support_agreement geom namePresentation sx agree₁,
    posetAction.act_eq_of_support_agreement geom namePresentation sx agree₂,
    posetAction.act_eq_of_support_agreement geom namePresentation sy agreeB⟩

theorem separation_refinement (p : RowForcing) (W D : FinalPoint Column)
    (bp : Bounds p D) (wd : (L).le W D)
    (g₁ : FinalActor Column) (hg₁ : g₁ ∈ (geom).fixSubgroup W)
    (g₂ : FinalActor Column) (hg₂ : g₂ ∈ (geom).fixSubgroup W)
    (r : RowForcing) (ref₁ : r ≤ rowAction g₁ p) :
    DenseBelow r (posetAction.SeparationWitness ((geom).fixSubgroup W) (Separated D W) p g₁ g₂) := by
  intro q qr
  obtain ⟨X, bq, upper⟩ := bounds_with q
    {(((geom).iso g₁).toFun D), (((geom).iso g₂).toFun D)} ((Set.countable_singleton _).insert _)
  have lower₁ := fixed_lower_image wd hg₁
  have lower₂ := fixed_lower_image wd hg₂
  have upper₁ := upper (((geom).iso g₁).toFun D) (by simp)
  have upper₂ := upper (((geom).iso g₂).toFun D) (by simp)
  obtain ⟨h, fixed, overlap⟩ := final_separation Column W D X wd ((L).trans lower₁ upper₁)
  have overlap' : (L).meet (((geom).iso h).toFun D) X = ((geom).iso h).toFun W :=
    overlap.trans (fixed W ((L).refl W)).symm
  obtain ⟨t, tq, th⟩ := one_copy_union bp bq (le_trans qr ref₁) overlap'
    (fun z hz => (fixed z hz).trans (hg₁ z hz).symm)
  have sep (Y : FinalPoint Column) (wy : (L).le W Y) (yx : (L).le Y X) :
      (L).meet (((geom).iso h).toFun D) Y = W := by
    apply (L).antisymm
    · rw [← overlap]
      exact (L).le_meet ((L).meet_le_left _ _) ((L).trans ((L).meet_le_right _ _) yx)
    · exact (L).le_meet (fixed_lower_image wd fixed) wy
  exact ⟨t, tq, h, fixed, th, sep _ lower₁ upper₁, sep _ lower₂ upper₂⟩

end PartitionPilot.Forcing.Rows

end

end OAI
