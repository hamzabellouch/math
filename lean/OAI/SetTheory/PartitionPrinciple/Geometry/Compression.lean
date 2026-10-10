import Init

namespace OAI


namespace PartitionPilot

section

universe u v

structure MeetOrder (α : Type u) where
  le : α → α → Prop
  meet : α → α → α
  refl : ∀ a, le a a
  trans : ∀ {a b c}, le a b → le b c → le a c
  antisymm : ∀ {a b}, le a b → le b a → a = b
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ {a b c}, le a b → le a c → le a (meet b c)

theorem meet_comm {α : Type u} (P : MeetOrder α) (a b : α) :
    P.meet a b = P.meet b a := by
  apply P.antisymm
  · exact P.le_meet (P.meet_le_right a b) (P.meet_le_left a b)
  · exact P.le_meet (P.meet_le_right b a) (P.meet_le_left b a)

structure MeetEmbedding {α : Type u} {β : Type v}
    (P : MeetOrder α) (Q : MeetOrder β) where
  toFun : α → β
  le_iff : ∀ a b, Q.le (toFun a) (toFun b) ↔ P.le a b
  map_meet : ∀ a b, toFun (P.meet a b) = Q.meet (toFun a) (toFun b)

def Positive {α : Type u} (P : MeetOrder α) (F : α → Prop) (x : α) : Prop :=
  ∃ f, F f ∧ P.le f x

def Profile {α : Type u} (P : MeetOrder α) (c e K : α) (F : α → Prop) : Prop :=
  ∀ x, P.le e x →
    (Positive P F x → P.le K x) ∧
    (¬ Positive P F x → P.meet K x = c)

def PositiveOver {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (F : α → Prop) (x : β) : Prop :=
  ∃ f, F f ∧ Q.le (i.toFun f) x

def ProfileOver {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop) : Prop :=
  ∀ x, Q.le (i.toFun e) x →
    (PositiveOver i F x → Q.le (i.toFun K) x) ∧
    (¬ PositiveOver i F x → Q.meet (i.toFun K) x = i.toFun c)

def HasOldShadow {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (x : β) : Prop :=
  ∃ l,
    (∀ a, Q.le (i.toFun a) x ↔ P.le a l) ∧
    (∀ a, ¬ Q.le x (i.toFun a) →
      Q.meet x (i.toFun a) = i.toFun (P.meet l a))

def IsGreatest {β : Type v} (Q : MeetOrder β) (x : β) : Prop :=
  ∀ y, Q.le y x

def PermittedExtension {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) : Prop :=
  ∀ x, (∃ a, i.toFun a = x) ∨ HasOldShadow i x ∨ IsGreatest Q x

theorem profile_at_shadow {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop)
    (old_profile : Profile P c e K F)
    (e_not_le_K : ¬ P.le e K)
    (x : β) (above_e : Q.le (i.toFun e) x)
    (shadow : HasOldShadow i x) :
    (PositiveOver i F x → Q.le (i.toFun K) x) ∧
    (¬ PositiveOver i F x → Q.meet (i.toFun K) x = i.toFun c) := by
  cases shadow with
  | intro l hl =>
    have part := hl.left
    have shadow_meet := hl.right
    have e_le_l : P.le e l := (part e).mp above_e
    have x_not_le_K : ¬ Q.le x (i.toFun K) := by
      intro hx
      exact e_not_le_K ((i.le_iff e K).mp (Q.trans above_e hx))
    have positives : PositiveOver i F x ↔ Positive P F l := by
      constructor
      · intro hp
        cases hp with
        | intro f hf => exact ⟨f, hf.left, (part f).mp hf.right⟩
      · intro hp
        cases hp with
        | intro f hf => exact ⟨f, hf.left, (part f).mpr hf.right⟩
    have inherited := old_profile l e_le_l
    constructor
    · intro hp
      exact (part K).mpr (inherited.left (positives.mp hp))
    · intro hn
      have hn_old : ¬ Positive P F l := fun hp => hn (positives.mpr hp)
      calc
        Q.meet (i.toFun K) x = Q.meet x (i.toFun K) := meet_comm Q _ _
        _ = i.toFun (P.meet l K) := shadow_meet K x_not_le_K
        _ = i.toFun (P.meet K l) := congrArg i.toFun (meet_comm P l K)
        _ = i.toFun c := congrArg i.toFun (inherited.right hn_old)

theorem profile_persists_one_step {α : Type u} {β : Type v}
    {P : MeetOrder α} {Q : MeetOrder β}
    (i : MeetEmbedding P Q) (c e K : α) (F : α → Prop)
    (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F)
    (e_not_le_K : ¬ P.le e K)
    (extension : PermittedExtension i) :
    ProfileOver i c e K F := by
  intro x above_e
  cases extension x with
  | inl old =>
    cases old with
    | intro a ha =>
      cases ha
      have e_le_a : P.le e a := (i.le_iff e a).mp above_e
      have positives : PositiveOver i F (i.toFun a) ↔ Positive P F a := by
        constructor
        · intro hp
          cases hp with
          | intro f hf => exact ⟨f, hf.left, (i.le_iff f a).mp hf.right⟩
        · intro hp
          cases hp with
          | intro f hf => exact ⟨f, hf.left, (i.le_iff f a).mpr hf.right⟩
      have inherited := old_profile a e_le_a
      constructor
      · intro hp
        exact (i.le_iff K a).mpr (inherited.left (positives.mp hp))
      · intro hn
        have hn_old : ¬ Positive P F a := fun hp => hn (positives.mpr hp)
        calc
          Q.meet (i.toFun K) (i.toFun a) = i.toFun (P.meet K a) :=
            (i.map_meet K a).symm
          _ = i.toFun c := congrArg i.toFun (inherited.right hn_old)
  | inr fresh =>
    cases fresh with
    | inl shadow =>
      exact profile_at_shadow i c e K F old_profile e_not_le_K x above_e shadow
    | inr top =>
      constructor
      · intro _
        exact top (i.toFun K)
      · intro hn
        cases nonempty_F with
        | intro f hf => exact False.elim (hn ⟨f, hf, top (i.toFun f)⟩)

def NodeProfile {α : Type u} (P : MeetOrder α) (c K : α)
    (F : α → Prop) (x : α) : Prop :=
  (Positive P F x → P.le K x) ∧
  (¬ Positive P F x → P.meet K x = c)

def ProfileOn {α : Type u} (P : MeetOrder α) (c e K : α)
    (F S : α → Prop) : Prop :=
  ∀ x, S x → P.le e x → NodeProfile P c K F x

def ShadowIn {α : Type u} (P : MeetOrder α) (Old : α → Prop)
    (x l : α) : Prop :=
  Old l ∧
  (∀ a, Old a → (P.le a x ↔ P.le a l)) ∧
  (∀ a, Old a → ¬ P.le x a → P.meet x a = P.meet l a)

def GreatestIn {α : Type u} (P : MeetOrder α) (S : α → Prop) (x : α) : Prop :=
  ∀ y, S y → P.le y x

def ContainsAnchors {α : Type u} (S : α → Prop) (e K : α) (F : α → Prop) : Prop :=
  S e ∧ S K ∧ ∀ f, F f → S f

theorem profile_on_shadow {α : Type u} (P : MeetOrder α)
    (c e K : α) (F Old : α → Prop)
    (anchors : ContainsAnchors Old e K F)
    (old_profile : ProfileOn P c e K F Old)
    (e_not_le_K : ¬ P.le e K)
    (x l : α) (above_e : P.le e x)
    (shadow : ShadowIn P Old x l) : NodeProfile P c K F x := by
  have part := shadow.right.left
  have shadow_meet := shadow.right.right
  have e_le_l : P.le e l := (part e anchors.left).mp above_e
  have x_not_le_K : ¬ P.le x K := fun hx => e_not_le_K (P.trans above_e hx)
  have positives : Positive P F x ↔ Positive P F l := by
    constructor
    · intro hp
      cases hp with
      | intro f hf =>
        exact ⟨f, hf.left, (part f (anchors.right.right f hf.left)).mp hf.right⟩
    · intro hp
      cases hp with
      | intro f hf =>
        exact ⟨f, hf.left, (part f (anchors.right.right f hf.left)).mpr hf.right⟩
  have inherited := old_profile l shadow.left e_le_l
  constructor
  · intro hp
    exact (part K anchors.right.left).mpr (inherited.left (positives.mp hp))
  · intro hn
    have hn_old : ¬ Positive P F l := fun hp => hn (positives.mpr hp)
    calc
      P.meet K x = P.meet x K := meet_comm P _ _
      _ = P.meet l K := shadow_meet K anchors.right.left x_not_le_K
      _ = P.meet K l := meet_comm P _ _
      _ = c := inherited.right hn_old

def SuccessorNodes {α : Type u} (P : MeetOrder α) (Old Current : α → Prop) : Prop :=
  ∀ x, Current x →
    Old x ∨ (∃ l, ShadowIn P Old x l) ∨ GreatestIn P Current x

def StageCases {α : Type u} {I : Type v} (P : MeetOrder α)
    (earlier : I → I → Prop) (Initial : α → Prop) (stage : I → α → Prop)
    (i : I) : Prop :=
  (∀ x, stage i x → Initial x) ∨
  (∃ j, earlier j i ∧ SuccessorNodes P (stage j) (stage i)) ∨
  (∀ x, stage i x → ∃ j, earlier j i ∧ stage j x)

theorem profile_at_every_stage {α : Type u} {I : Type v}
    (P : MeetOrder α) (c e K : α) (F Initial : α → Prop)
    (earlier : I → I → Prop) (wf : WellFounded earlier)
    (stage : I → α → Prop)
    (nonempty_F : ∃ f, F f)
    (e_not_le_K : ¬ P.le e K)
    (initial_profile : ProfileOn P c e K F Initial)
    (anchors : ∀ i, ContainsAnchors (stage i) e K F)
    (cases_at : ∀ i, StageCases P earlier Initial stage i) :
    ∀ i, ProfileOn P c e K F (stage i) := by
  intro i
  apply wf.induction i
  intro current ih
  intro x hx above_e
  cases cases_at current with
  | inl initial =>
    exact initial_profile x (initial x hx) above_e
  | inr growth =>
    cases growth with
    | inl successor =>
      cases successor with
      | intro old h =>
        have old_profile := ih old h.left
        cases h.right x hx with
        | inl old_node => exact old_profile x old_node above_e
        | inr new_node =>
          cases new_node with
          | inl has_shadow =>
            cases has_shadow with
            | intro l shadow =>
              exact profile_on_shadow P c e K F (stage old) (anchors old)
                old_profile e_not_le_K x l above_e shadow
          | inr top =>
            constructor
            · intro _
              exact top K (anchors current).right.left
            · intro hn
              cases nonempty_F with
              | intro f hf =>
                exact False.elim (hn ⟨f, hf, top f ((anchors current).right.right f hf)⟩)
    | inr limit =>
      cases limit x hx with
      | intro old h => exact ih old h.left x h.right above_e

theorem profile_persists_through_growth {α : Type u} {I : Type v}
    (P : MeetOrder α) (c e K : α) (F Initial : α → Prop)
    (earlier : I → I → Prop) (wf : WellFounded earlier)
    (stage : I → α → Prop)
    (nonempty_F : ∃ f, F f)
    (e_not_le_K : ¬ P.le e K)
    (initial_profile : ProfileOn P c e K F Initial)
    (anchors : ∀ i, ContainsAnchors (stage i) e K F)
    (cases_at : ∀ i, StageCases P earlier Initial stage i)
    (covers : ∀ x, ∃ i, stage i x) :
    Profile P c e K F := by
  have at_stage := profile_at_every_stage P c e K F Initial earlier wf stage
    nonempty_F e_not_le_K initial_profile anchors cases_at
  intro x above_e
  cases covers x with
  | intro i hi => exact at_stage i x hi above_e

end



namespace Attachment

universe u v w

structure Data {O : Type u} (P : MeetOrder O) (N : Type v) (I : Type w) where
  component : N → I
  base : I → O
  upper : I → O → Prop
  upper_up : ∀ i {a b}, upper i a → P.le a b → upper i b
  upper_meet : ∀ i {a b}, upper i a → upper i b → upper i (P.meet a b)
  base_le_upper : ∀ i a, upper i a → P.le (base i) a
  base_not_upper : ∀ i, ¬ upper i (base i)
  shadow : N → O
  shadow_le_base : ∀ x, P.le (shadow x) (base (component x))
  inside : N → N → Prop
  inside_refl : ∀ x, inside x x
  inside_trans : ∀ {x y z}, inside x y → inside y z → inside x z
  inside_antisymm : ∀ {x y}, inside x y → inside y x → x = y
  inside_component : ∀ {x y}, inside x y → component x = component y
  inside_shadow : ∀ {x y}, inside x y → P.le (shadow x) (shadow y)

variable {O : Type u} {N : Type v} {I : Type w} {P : MeetOrder O}

def FreshLe (d : Data P N I) (x y : N) : Prop :=
  d.inside x y ∨ d.upper (d.component x) (d.shadow y)

def Le (d : Data P N I) : O ⊕ N → O ⊕ N → Prop
  | .inl a, .inl b => P.le a b
  | .inl a, .inr y => P.le a (d.shadow y)
  | .inr x, .inl b => d.upper (d.component x) b
  | .inr x, .inr y => FreshLe d x y

theorem not_upper_shadow (d : Data P N I) (x : N) :
    ¬ d.upper (d.component x) (d.shadow x) := by
  intro h
  exact d.base_not_upper _ (d.upper_up _ h (d.shadow_le_base x))

theorem fresh_shadow_mono (d : Data P N I) {x y : N}
    (h : FreshLe d x y) : P.le (d.shadow x) (d.shadow y) := by
  cases h with
  | inl h => exact d.inside_shadow h
  | inr h => exact P.trans (d.shadow_le_base x) (d.base_le_upper _ _ h)

theorem fresh_trans (d : Data P N I) {x y z : N}
    (hxy : FreshLe d x y) (hyz : FreshLe d y z) : FreshLe d x z := by
  cases hxy with
  | inl hxy =>
    cases hyz with
    | inl hyz => exact Or.inl (d.inside_trans hxy hyz)
    | inr hyz =>
      exact Or.inr ((d.inside_component hxy).symm ▸ hyz)
  | inr hxy => exact Or.inr (d.upper_up _ hxy (fresh_shadow_mono d hyz))

theorem fresh_antisymm (d : Data P N I) {x y : N}
    (hxy : FreshLe d x y) (hyx : FreshLe d y x) : x = y := by
  cases hxy with
  | inl hxy =>
    cases hyx with
    | inl hyx => exact d.inside_antisymm hxy hyx
    | inr hyx =>
      exact False.elim (not_upper_shadow d x ((d.inside_component hxy).symm ▸ hyx))
  | inr hxy =>
    exact False.elim (not_upper_shadow d x (d.upper_up _ hxy (fresh_shadow_mono d hyx)))

theorem le_refl (d : Data P N I) (x : O ⊕ N) : Le d x x := by
  cases x with
  | inl a => exact P.refl a
  | inr x => exact Or.inl (d.inside_refl x)

theorem le_trans (d : Data P N I) {x y z : O ⊕ N}
    (hxy : Le d x y) (hyz : Le d y z) : Le d x z := by
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      cases z with
      | inl c => exact P.trans hxy hyz
      | inr z => exact P.trans hxy hyz
    | inr y =>
      cases z with
      | inl c => exact P.trans hxy (P.trans (d.shadow_le_base y) (d.base_le_upper _ _ hyz))
      | inr z => exact P.trans hxy (fresh_shadow_mono d hyz)
  | inr x =>
    cases y with
    | inl b =>
      cases z with
      | inl c => exact d.upper_up _ hxy hyz
      | inr z => exact Or.inr (d.upper_up _ hxy hyz)
    | inr y =>
      cases z with
      | inl c =>
        cases hxy with
        | inl hxy =>
          change d.upper (d.component x) c
          exact (d.inside_component hxy).symm ▸ hyz
        | inr hxy =>
          exact d.upper_up _ hxy (P.trans (d.shadow_le_base y) (d.base_le_upper _ _ hyz))
      | inr z => exact fresh_trans d hxy hyz

theorem le_antisymm (d : Data P N I) {x y : O ⊕ N}
    (hxy : Le d x y) (hyx : Le d y x) : x = y := by
  cases x with
  | inl a =>
    cases y with
    | inl b => exact congrArg Sum.inl (P.antisymm hxy hyx)
    | inr y => exact False.elim (not_upper_shadow d y (d.upper_up _ hyx hxy))
  | inr x =>
    cases y with
    | inl b => exact False.elim (not_upper_shadow d x (d.upper_up _ hxy hyx))
    | inr y => exact congrArg Sum.inr (fresh_antisymm d hxy hyx)

theorem fresh_same_component (d : Data P N I) {x y : N}
    (same : d.component x = d.component y) :
    FreshLe d x y ↔ d.inside x y := by
  constructor
  · intro h
    cases h with
    | inl h => exact h
    | inr h => exact False.elim (not_upper_shadow d y (same ▸ h))
  · exact Or.inl

theorem fresh_different_components (d : Data P N I) {x y : N}
    (different : d.component x ≠ d.component y) :
    FreshLe d x y ↔ d.upper (d.component x) (d.shadow y) := by
  constructor
  · intro h
    cases h with
    | inl h => exact False.elim (different (d.inside_component h))
    | inr h => exact h
  · exact Or.inr

def IsMeet (d : Data P N I) (a b m : O ⊕ N) : Prop :=
  Le d m a ∧ Le d m b ∧ ∀ t, Le d t a → Le d t b → Le d t m

theorem old_meet (d : Data P N I) (a b : O) :
    IsMeet d (.inl a) (.inl b) (.inl (P.meet a b)) := by
  refine ⟨P.meet_le_left a b, P.meet_le_right a b, ?_⟩
  intro t hta htb
  cases t with
  | inl c => exact P.le_meet hta htb
  | inr x => exact d.upper_meet _ hta htb

theorem shadow_meet (d : Data P N I) (x : N) (a : O)
    (not_above : ¬ d.upper (d.component x) a) :
    IsMeet d (.inr x) (.inl a) (.inl (P.meet (d.shadow x) a)) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx hta
  cases t with
  | inl b => exact P.le_meet htx hta
  | inr y =>
    cases htx with
    | inl inside => exact False.elim (not_above (d.inside_component inside ▸ hta))
    | inr mediated => exact d.upper_meet _ mediated hta

theorem cross_meet (d : Data P N I) (x z : N)
    (different : d.component x ≠ d.component z)
    (not_xz : ¬ FreshLe d x z) (not_zx : ¬ FreshLe d z x) :
    IsMeet d (.inr x) (.inr z) (.inl (P.meet (d.shadow x) (d.shadow z))) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx htz
  cases t with
  | inl b => exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz =>
        exact False.elim (different ((d.inside_component hyx).symm.trans (d.inside_component hyz)))
      | inr hyz => exact False.elim (not_xz (Or.inr (d.inside_component hyx ▸ hyz)))
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (not_zx (Or.inr (d.inside_component hyz ▸ hyx)))
      | inr hyz => exact d.upper_meet _ hyx hyz

def ComponentMeets (d : Data P N I) : Prop :=
  ∀ x z, d.component x = d.component z →
    (∃ m, d.inside m x ∧ d.inside m z ∧
      (∀ y, d.inside y x → d.inside y z → d.inside y m) ∧
      d.shadow m = P.meet (d.shadow x) (d.shadow z)) ∨
    (∀ y, d.inside y x → d.inside y z → False)

theorem inside_mediated_impossible (d : Data P N I) {y x z : N}
    (inside : d.inside y x) (same : d.component x = d.component z)
    (mediated : d.upper (d.component y) (d.shadow z)) : False := by
  exact not_upper_shadow d z ((d.inside_component inside).trans same ▸ mediated)

theorem component_fresh_meet (d : Data P N I) (x z m : N)
    (same : d.component x = d.component z)
    (hmx : d.inside m x) (hmz : d.inside m z)
    (greatest : ∀ y, d.inside y x → d.inside y z → d.inside y m)
    (shadows : d.shadow m = P.meet (d.shadow x) (d.shadow z)) :
    IsMeet d (.inr x) (.inr z) (.inr m) := by
  refine ⟨Or.inl hmx, Or.inl hmz, ?_⟩
  intro t htx htz
  cases t with
  | inl a =>
    change P.le a (d.shadow m)
    rw [shadows]
    exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz => exact Or.inl (greatest y hyx hyz)
      | inr hyz => exact False.elim (inside_mediated_impossible d hyx same hyz)
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (inside_mediated_impossible d hyz same.symm hyx)
      | inr hyz =>
        apply Or.inr
        rw [shadows]
        exact d.upper_meet _ hyx hyz

theorem component_old_meet (d : Data P N I) (x z : N)
    (same : d.component x = d.component z)
    (no_new_lower : ∀ y, d.inside y x → d.inside y z → False) :
    IsMeet d (.inr x) (.inr z) (.inl (P.meet (d.shadow x) (d.shadow z))) := by
  refine ⟨P.meet_le_left _ _, P.meet_le_right _ _, ?_⟩
  intro t htx htz
  cases t with
  | inl a => exact P.le_meet htx htz
  | inr y =>
    cases htx with
    | inl hyx =>
      cases htz with
      | inl hyz => exact False.elim (no_new_lower y hyx hyz)
      | inr hyz => exact False.elim (inside_mediated_impossible d hyx same hyz)
    | inr hyx =>
      cases htz with
      | inl hyz => exact False.elim (inside_mediated_impossible d hyz same.symm hyx)
      | inr hyz => exact d.upper_meet _ hyx hyz

theorem meet_of_le (d : Data P N I) {a b : O ⊕ N} (h : Le d a b) :
    IsMeet d a b a := ⟨le_refl d a, h, fun _ hta _ => hta⟩

theorem meet_symm (d : Data P N I) {a b m : O ⊕ N}
    (h : IsMeet d a b m) : IsMeet d b a m :=
  ⟨h.right.left, h.left, fun t htb hta => h.right.right t hta htb⟩

theorem all_meets (d : Data P N I) (local_meets : ComponentMeets d)
    (a b : O ⊕ N) : ∃ m, IsMeet d a b m := by
  classical
  cases a with
  | inl a =>
    cases b with
    | inl b => exact ⟨_, old_meet d a b⟩
    | inr y =>
      by_cases h : d.upper (d.component y) a
      · exact ⟨_, meet_symm d (meet_of_le d h)⟩
      · exact ⟨_, meet_symm d (shadow_meet d y a h)⟩
  | inr x =>
    cases b with
    | inl b =>
      by_cases h : d.upper (d.component x) b
      · exact ⟨_, meet_of_le d h⟩
      · exact ⟨_, shadow_meet d x b h⟩
    | inr z =>
      by_cases same : d.component x = d.component z
      · cases local_meets x z same with
        | inl fresh =>
          rcases fresh with ⟨m, hmx, hmz, greatest, shadows⟩
          exact ⟨_, component_fresh_meet d x z m same hmx hmz greatest shadows⟩
        | inr old => exact ⟨_, component_old_meet d x z same old⟩
      · by_cases h : FreshLe d x z
        · exact ⟨_, meet_of_le d h⟩
        · by_cases h' : FreshLe d z x
          · exact ⟨_, meet_symm d (meet_of_le d h')⟩
          · exact ⟨_, cross_meet d x z same h h'⟩

noncomputable def meetOrder (d : Data P N I) (local_meets : ComponentMeets d) :
    MeetOrder (O ⊕ N) where
  le := Le d
  meet a b := Classical.choose (all_meets d local_meets a b)
  refl := le_refl d
  trans := le_trans d
  antisymm := le_antisymm d
  meet_le_left a b := (Classical.choose_spec (all_meets d local_meets a b)).left
  meet_le_right a b := (Classical.choose_spec (all_meets d local_meets a b)).right.left
  le_meet hab hac := (Classical.choose_spec (all_meets d local_meets _ _)).right.right _ hab hac

theorem meet_eq (d : Data P N I) (local_meets : ComponentMeets d)
    {a b m : O ⊕ N} (h : IsMeet d a b m) :
    (meetOrder d local_meets).meet a b = m := by
  let Q := meetOrder d local_meets
  apply le_antisymm d
  · exact h.right.right _ (Q.meet_le_left a b) (Q.meet_le_right a b)
  · exact Q.le_meet h.left h.right.left

noncomputable def oldEmbedding (d : Data P N I) (local_meets : ComponentMeets d) :
    MeetEmbedding P (meetOrder d local_meets) where
  toFun := Sum.inl
  le_iff _ _ := Iff.rfl
  map_meet a b := (meet_eq d local_meets (old_meet d a b)).symm

theorem has_old_shadow (d : Data P N I) (local_meets : ComponentMeets d) (x : N) :
    HasOldShadow (oldEmbedding d local_meets) (.inr x) := by
  refine ⟨d.shadow x, fun _ => Iff.rfl, ?_⟩
  intro a h
  exact meet_eq d local_meets (shadow_meet d x a h)

theorem permitted_extension (d : Data P N I) (local_meets : ComponentMeets d) :
    PermittedExtension (oldEmbedding d local_meets) := by
  intro x
  cases x with
  | inl a => exact Or.inl ⟨a, rfl⟩
  | inr x => exact Or.inr (Or.inl (has_old_shadow d local_meets x))

theorem attachment_preserves_profile (d : Data P N I) (local_meets : ComponentMeets d)
    (c e K : O) (F : O → Prop) (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F) (e_not_le_K : ¬ P.le e K) :
    ProfileOver (oldEmbedding d local_meets) c e K F :=
  profile_persists_one_step (oldEmbedding d local_meets) c e K F
    nonempty_F old_profile e_not_le_K (permitted_extension d local_meets)

end Attachment



namespace Attachment

universe u v w

def idealOrder {A : Type v} (Q : MeetOrder A) (a : A) :
    MeetOrder {x : A // Q.le x a} where
  le x y := Q.le x.val y.val
  meet x y := ⟨Q.meet x.val y.val, Q.trans (Q.meet_le_left _ _) x.property⟩
  refl x := Q.refl x.val
  trans hxy hyz := Q.trans hxy hyz
  antisymm hxy hyx := Subtype.ext (Q.antisymm hxy hyx)
  meet_le_left x y := Q.meet_le_left x.val y.val
  meet_le_right x y := Q.meet_le_right x.val y.val
  le_meet hxy hxz := Q.le_meet hxy hxz

def cut {A : Type v} (Q : MeetOrder A) (a x : A) : {y : A // Q.le y a} :=
  ⟨Q.meet x a, Q.meet_le_right x a⟩

theorem cut_mono {A : Type v} (Q : MeetOrder A) (a : A) {x y : A}
    (h : Q.le x y) : (idealOrder Q a).le (cut Q a x) (cut Q a y) :=
  Q.le_meet (Q.trans (Q.meet_le_left x a) h) (Q.meet_le_right x a)

theorem cut_meet {A : Type v} (Q : MeetOrder A) (a x y : A) :
    cut Q a (Q.meet x y) = (idealOrder Q a).meet (cut Q a x) (cut Q a y) := by
  apply Subtype.ext
  change Q.meet (Q.meet x y) a = Q.meet (Q.meet x a) (Q.meet y a)
  apply Q.antisymm
  · apply Q.le_meet
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left x y)) (Q.meet_le_right _ _)
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_right x y)) (Q.meet_le_right _ _)
  · apply Q.le_meet
    · exact Q.le_meet (Q.trans (Q.meet_le_left _ _) (Q.meet_le_left x a))
        (Q.trans (Q.meet_le_right _ _) (Q.meet_le_left y a))
    · exact Q.trans (Q.meet_le_left _ _) (Q.meet_le_right x a)

theorem cut_of_le {A : Type v} (Q : MeetOrder A) (a x : A) (h : Q.le x a) :
    cut Q a x = ⟨x, h⟩ := by
  apply Subtype.ext
  exact Q.antisymm (Q.meet_le_left x a) (Q.le_meet (Q.refl x) h)

structure Templates {O : Type u} (P : MeetOrder O) (I : Type w) where
  Space : I → Type v
  order : ∀ i, MeetOrder (Space i)
  anchor : ∀ i, Space i
  embed : ∀ i, MeetEmbedding (idealOrder (order i) (anchor i)) P
  upper : I → O → Prop
  upper_nonempty : ∀ i, ∃ a, upper i a
  upper_up : ∀ i {a b}, upper i a → P.le a b → upper i b
  upper_meet : ∀ i {a b}, upper i a → upper i b → upper i (P.meet a b)
  separator : I → O
  base_le_separator : ∀ i,
    P.le ((embed i).toFun ⟨anchor i, (order i).refl _⟩) (separator i)
  separator_not_le_base : ∀ i,
    ¬ P.le (separator i) ((embed i).toFun ⟨anchor i, (order i).refl _⟩)
  separator_le_upper : ∀ i a, upper i a → P.le (separator i) a

namespace Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

def Fresh := (i : I) × {y : b.Space i // ¬ (b.order i).le y (b.anchor i)}

def base (i : I) : O := (b.embed i).toFun ⟨b.anchor i, (b.order i).refl _⟩

def shadow (x : b.Fresh) : O := (b.embed x.1).toFun (cut (b.order x.1) (b.anchor x.1) x.2.val)

def Inside (x y : b.Fresh) : Prop :=
  ∃ h : x.1 = y.1, (b.order x.1).le x.2.val (h.symm ▸ y.2.val)

theorem inside_refl (x : b.Fresh) : b.Inside x x := ⟨rfl, (b.order x.1).refl x.2.val⟩

theorem inside_trans {x y z : b.Fresh} (hxy : b.Inside x y) (hyz : b.Inside y z) :
    b.Inside x z := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases z with ⟨k, z⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  rcases hyz with ⟨hjk, hyz⟩
  cases hjk
  exact ⟨rfl, (b.order i).trans hxy hyz⟩

theorem inside_antisymm {x y : b.Fresh} (hxy : b.Inside x y) (hyx : b.Inside y x) :
    x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  rcases hyx with ⟨hii, hyx⟩
  cases hii
  exact congrArg (Sigma.mk i) (Subtype.ext ((b.order i).antisymm hxy hyx))

theorem inside_shadow {x y : b.Fresh} (hxy : b.Inside x y) :
    P.le (b.shadow x) (b.shadow y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  rcases hxy with ⟨hij, hxy⟩
  cases hij
  exact ((b.embed i).le_iff _ _).mpr (cut_mono (b.order i) (b.anchor i) hxy)

def data : Data P b.Fresh I where
  component := Sigma.fst
  base := b.base
  upper := b.upper
  upper_up := b.upper_up
  upper_meet := b.upper_meet
  base_le_upper i a h := P.trans (b.base_le_separator i) (b.separator_le_upper i a h)
  base_not_upper i h := b.separator_not_le_base i (b.separator_le_upper i (b.base i) h)
  shadow := b.shadow
  shadow_le_base x := ((b.embed x.1).le_iff _ _).mpr ((b.order x.1).meet_le_right _ _)
  inside := b.Inside
  inside_refl := b.inside_refl
  inside_trans := b.inside_trans
  inside_antisymm := b.inside_antisymm
  inside_component h := h.choose
  inside_shadow := b.inside_shadow

theorem mapped_cut_meet (i : I) (x y : b.Space i) :
    (b.embed i).toFun (cut (b.order i) (b.anchor i) ((b.order i).meet x y)) =
    P.meet ((b.embed i).toFun (cut (b.order i) (b.anchor i) x))
      ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  rw [cut_meet]
  exact (b.embed i).map_meet _ _

theorem component_meets : ComponentMeets b.data := by
  classical
  intro x z same
  rcases x with ⟨i, x⟩
  rcases z with ⟨j, z⟩
  change i = j at same
  cases same
  by_cases old : (b.order i).le ((b.order i).meet x.val z.val) (b.anchor i)
  · apply Or.inr
    intro y hyx hyz
    rcases y with ⟨k, y⟩
    rcases hyx with ⟨hki, hyx⟩
    cases hki
    rcases hyz with ⟨hkk, hyz⟩
    cases hkk
    exact y.property ((b.order i).trans ((b.order i).le_meet hyx hyz) old)
  · apply Or.inl
    let m : b.Fresh := ⟨i, ⟨(b.order i).meet x.val z.val, old⟩⟩
    refine ⟨m, ⟨rfl, (b.order i).meet_le_left _ _⟩, ⟨rfl, (b.order i).meet_le_right _ _⟩, ?_, ?_⟩
    · intro y hyx hyz
      rcases y with ⟨k, y⟩
      rcases hyx with ⟨hki, hyx⟩
      cases hki
      rcases hyz with ⟨hkk, hyz⟩
      cases hkk
      exact ⟨rfl, (b.order i).le_meet hyx hyz⟩
    · exact b.mapped_cut_meet i x.val z.val

noncomputable def extension : MeetOrder (O ⊕ b.Fresh) := meetOrder b.data b.component_meets

noncomputable def oldEmbedding : MeetEmbedding P b.extension :=
  Attachment.oldEmbedding b.data b.component_meets

theorem shadow_verified (x : b.Fresh) : HasOldShadow b.oldEmbedding (.inr x) :=
  has_old_shadow b.data b.component_meets x

theorem persistence (c e K : O) (F : O → Prop) (nonempty_F : ∃ f, F f)
    (old_profile : Profile P c e K F) (e_not_le_K : ¬ P.le e K) :
    ProfileOver b.oldEmbedding c e K F :=
  attachment_preserves_profile b.data b.component_meets c e K F nonempty_F old_profile e_not_le_K

noncomputable def represent (i : I) (y : b.Space i) : O ⊕ b.Fresh := by
  classical
  exact if h : (b.order i).le y (b.anchor i) then
    .inl ((b.embed i).toFun ⟨y, h⟩)
  else .inr ⟨i, ⟨y, h⟩⟩

theorem represent_old (i : I) (y : b.Space i) (h : (b.order i).le y (b.anchor i)) :
    b.represent i y = .inl ((b.embed i).toFun ⟨y, h⟩) := by
  simp only [represent, dite_eq_left h]

theorem represent_new (i : I) (y : b.Space i) (h : ¬ (b.order i).le y (b.anchor i)) :
    b.represent i y = .inr ⟨i, ⟨y, h⟩⟩ := by
  simp only [represent, dite_eq_right h]

theorem represent_le_iff (i : I) (x y : b.Space i) :
    Le b.data (b.represent i x) (b.represent i y) ↔ (b.order i).le x y := by
  classical
  by_cases hx : (b.order i).le x (b.anchor i)
  · rw [b.represent_old i x hx]
    by_cases hy : (b.order i).le y (b.anchor i)
    · rw [b.represent_old i y hy]
      exact (b.embed i).le_iff _ _
    · rw [b.represent_new i y hy]
      change P.le ((b.embed i).toFun ⟨x, hx⟩)
        ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) ↔ _
      rw [(b.embed i).le_iff]
      constructor
      · intro h
        exact (b.order i).trans h ((b.order i).meet_le_left y (b.anchor i))
      · intro h
        exact (b.order i).le_meet h hx
  · rw [b.represent_new i x hx]
    by_cases hy : (b.order i).le y (b.anchor i)
    · rw [b.represent_old i y hy]
      constructor
      · intro h
        have hbase : P.le ((b.embed i).toFun ⟨y, hy⟩) (b.base i) :=
          ((b.embed i).le_iff _ _).mpr hy
        exact False.elim (b.data.base_not_upper i (b.upper_up i h hbase))
      · intro h
        exact False.elim (hx ((b.order i).trans h hy))
    · rw [b.represent_new i y hy]
      change FreshLe b.data ⟨i, ⟨x, hx⟩⟩ ⟨i, ⟨y, hy⟩⟩ ↔ _
      rw [fresh_same_component b.data (x := ⟨i, ⟨x, hx⟩⟩) (y := ⟨i, ⟨y, hy⟩⟩) rfl]
      constructor
      · rintro ⟨h, hxy⟩
        cases h
        exact hxy
      · intro hxy
        exact ⟨rfl, hxy⟩

theorem old_below_represent (i : I) (y : b.Space i) (a : O) :
    Le b.data (.inl a) (b.represent i y) ↔
    P.le a ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy, cut_of_le _ _ _ hy]
    exact Iff.rfl
  · rw [b.represent_new i y hy]
    exact Iff.rfl

theorem upper_shadow_below_represent (i : I) (y : b.Space i) (x : b.Fresh)
    (h : b.upper x.1 ((b.embed i).toFun (cut (b.order i) (b.anchor i) y))) :
    Le b.data (.inr x) (b.represent i y) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy]
    rw [cut_of_le _ _ _ hy] at h
    exact h
  · rw [b.represent_new i y hy]
    exact Or.inr h

theorem foreign_below_represent (i : I) (y : b.Space i) (x : b.Fresh)
    (different : x.1 ≠ i)
    (h : Le b.data (.inr x) (b.represent i y)) :
    b.upper x.1 ((b.embed i).toFun (cut (b.order i) (b.anchor i) y)) := by
  classical
  by_cases hy : (b.order i).le y (b.anchor i)
  · rw [b.represent_old i y hy] at h
    rw [cut_of_le _ _ _ hy]
    exact h
  · rw [b.represent_new i y hy] at h
    exact (fresh_different_components b.data (x := x) (y := ⟨i, ⟨y, hy⟩⟩) different).mp h

theorem represented_meet (i : I) (x z : b.Space i) :
    IsMeet b.data (b.represent i x) (b.represent i z)
      (b.represent i ((b.order i).meet x z)) := by
  classical
  refine ⟨(b.represent_le_iff i _ _).mpr ((b.order i).meet_le_left x z),
    (b.represent_le_iff i _ _).mpr ((b.order i).meet_le_right x z), ?_⟩
  intro t htx htz
  cases t with
  | inl a =>
    apply (b.old_below_represent i _ a).mpr
    rw [b.mapped_cut_meet]
    exact P.le_meet ((b.old_below_represent i x a).mp htx)
      ((b.old_below_represent i z a).mp htz)
  | inr y =>
    rcases y with ⟨j, y⟩
    by_cases same : j = i
    · cases same
      have repr_y := b.represent_new i y.val y.property
      rw [← repr_y] at htx htz ⊢
      apply (b.represent_le_iff i _ _).mpr
      exact (b.order i).le_meet ((b.represent_le_iff i _ _).mp htx)
        ((b.represent_le_iff i _ _).mp htz)
    · apply b.upper_shadow_below_represent
      rw [b.mapped_cut_meet]
      exact b.upper_meet j (b.foreign_below_represent i x ⟨j, y⟩ same htx)
        (b.foreign_below_represent i z ⟨j, y⟩ same htz)

noncomputable def templateEmbedding (i : I) : MeetEmbedding (b.order i) b.extension where
  toFun := b.represent i
  le_iff := b.represent_le_iff i
  map_meet x z := (meet_eq b.data b.component_meets (b.represented_meet i x z)).symm

theorem template_agrees_on_base (i : I) (y : b.Space i)
    (hy : (b.order i).le y (b.anchor i)) :
    (b.templateEmbedding i).toFun y = .inl ((b.embed i).toFun ⟨y, hy⟩) :=
  b.represent_old i y hy

theorem greatest_preserved (T : O) (top : ∀ a, P.le a T) :
    ∀ x, b.extension.le x (.inl T) := by
  intro x
  cases x with
  | inl a => exact top a
  | inr x =>
    rcases b.upper_nonempty x.1 with ⟨a, ha⟩
    exact b.upper_up x.1 ha (top a)

theorem least_preserved (zero : O) (bottom : ∀ a, P.le zero a) :
    ∀ x, b.extension.le (.inl zero) x := by
  intro x
  cases x with
  | inl a => exact bottom a
  | inr x => exact bottom (b.shadow x)

theorem cross_meet_eq (x z : b.Fresh) (different : x.1 ≠ z.1)
    (not_xz : ¬ b.extension.le (.inr x) (.inr z))
    (not_zx : ¬ b.extension.le (.inr z) (.inr x)) :
    b.extension.meet (.inr x) (.inr z) = .inl (P.meet (b.shadow x) (b.shadow z)) :=
  meet_eq b.data b.component_meets (cross_meet b.data x z different not_xz not_zx)

theorem old_lower_iff (a : O) (x : b.Fresh) :
    b.extension.le (.inl a) (.inr x) ↔ P.le a (b.shadow x) := Iff.rfl

theorem old_upper_iff (a : O) (x : b.Fresh) :
    b.extension.le (.inr x) (.inl a) ↔ b.upper x.1 a := Iff.rfl

theorem cross_le_iff (x z : b.Fresh) (different : x.1 ≠ z.1) :
    b.extension.le (.inr x) (.inr z) ↔ b.upper x.1 (b.shadow z) :=
  fresh_different_components b.data (x := x) (y := z) different

theorem shadow_meet_eq (x : b.Fresh) (a : O)
    (not_above : ¬ b.extension.le (.inr x) (.inl a)) :
    b.extension.meet (.inr x) (.inl a) = .inl (P.meet (b.shadow x) a) :=
  meet_eq b.data b.component_meets (shadow_meet b.data x a not_above)

theorem template_preserves_zero (i : I) (qzero : b.Space i) (zero : O)
    (qbottom : ∀ y, (b.order i).le qzero y)
    (base_zero : (b.embed i).toFun ⟨qzero, qbottom (b.anchor i)⟩ = zero) :
    (b.templateEmbedding i).toFun qzero = .inl zero := by
  rw [b.template_agrees_on_base i qzero (qbottom (b.anchor i)), base_zero]

end Templates
end Attachment




universe u v w

theorem meet_eq_left_of_le {A : Type u} (P : MeetOrder A) {x y : A}
    (h : P.le x y) : P.meet x y = x :=
  P.antisymm (P.meet_le_left x y) (P.le_meet (P.refl x) h)

namespace Attachment.Templates

variable {O : Type u} {I : Type w} {P : MeetOrder O} (b : Templates.{u,v,w} P I)

def originalFamily (i : I) : O ⊕ b.Fresh → Prop
  | .inl a => b.upper i a
  | .inr _ => False

theorem positive_old_iff (i : I) (a : O) :
    Positive b.extension (b.originalFamily i) (.inl a) ↔ b.upper i a := by
  constructor
  · rintro ⟨f, hf, hfa⟩
    cases f with
    | inl f => exact b.upper_up i hf hfa
    | inr f => exact False.elim hf
  · intro ha
    exact ⟨.inl a, ha, P.refl a⟩

theorem positive_new_iff (i : I) (x : b.Fresh) :
    Positive b.extension (b.originalFamily i) (.inr x) ↔ b.upper i (b.shadow x) := by
  constructor
  · rintro ⟨f, hf, hfx⟩
    cases f with
    | inl f => exact b.upper_up i hf hfx
    | inr f => exact False.elim hf
  · intro hx
    exact ⟨.inl (b.shadow x), hx, P.refl _⟩

def cap (i : I) (t : b.Space i) (outside : ¬ (b.order i).le t (b.anchor i)) : b.Fresh :=
  ⟨i, ⟨t, outside⟩⟩

theorem cap_shadow (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    b.shadow (b.cap i t outside) = b.base i := by
  change (b.embed i).toFun (cut (b.order i) (b.anchor i) t) = _
  have hcut : cut (b.order i) (b.anchor i) t =
      ⟨b.anchor i, (b.order i).refl _⟩ := by
    apply Subtype.ext
    exact (b.order i).antisymm ((b.order i).meet_le_right _ _)
      ((b.order i).le_meet (top _) ((b.order i).refl _))
  exact congrArg (b.embed i).toFun hcut

theorem cap_strict_above_base (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    b.extension.le (.inl (b.base i)) (.inr (b.cap i t outside)) ∧
    ¬ b.extension.le (.inr (b.cap i t outside)) (.inl (b.base i)) := by
  constructor
  · change P.le (b.base i) (b.shadow (b.cap i t outside))
    rw [b.cap_shadow i t top outside]
    exact P.refl _
  · exact b.data.base_not_upper i

theorem separator_not_below_cap (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    ¬ b.extension.le (.inl (b.separator i)) (.inr (b.cap i t outside)) := by
  intro h
  change P.le (b.separator i) (b.shadow (b.cap i t outside)) at h
  rw [b.cap_shadow i t top outside] at h
  exact b.separator_not_le_base i h

theorem initial_profile (i : I) (t : b.Space i)
    (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    Profile b.extension (.inl (b.base i)) (.inl (b.separator i))
      (.inr (b.cap i t outside)) (b.originalFamily i) := by
  intro x above_e
  cases x with
  | inl a =>
    constructor
    · intro hp
      exact (b.positive_old_iff i a).mp hp
    · intro hn
      have not_upper : ¬ b.upper i a := fun ha => hn ((b.positive_old_iff i a).mpr ha)
      calc
        b.extension.meet (.inr (b.cap i t outside)) (.inl a) =
            .inl (P.meet (b.shadow (b.cap i t outside)) a) :=
          b.shadow_meet_eq _ a not_upper
        _ = .inl (P.meet (b.base i) a) := by rw [b.cap_shadow i t top outside]
        _ = .inl (b.base i) := congrArg Sum.inl
          (meet_eq_left_of_le P (P.trans (b.base_le_separator i) above_e))
  | inr x =>
    have different : i ≠ x.1 := by
      intro same
      have hs := b.data.shadow_le_base x
      change P.le (b.shadow x) (b.base x.1) at hs
      rw [← same] at hs
      exact b.separator_not_le_base i (P.trans above_e hs)
    have not_xk : ¬ b.extension.le (.inr x) (.inr (b.cap i t outside)) := by
      intro h
      exact b.separator_not_below_cap i t top outside (b.extension.trans above_e h)
    constructor
    · intro hp
      exact (b.cross_le_iff _ x different).mpr ((b.positive_new_iff i x).mp hp)
    · intro hn
      have not_kx : ¬ b.extension.le (.inr (b.cap i t outside)) (.inr x) := by
        intro h
        exact hn ((b.positive_new_iff i x).mpr ((b.cross_le_iff _ x different).mp h))
      calc
        b.extension.meet (.inr (b.cap i t outside)) (.inr x) =
            .inl (P.meet (b.shadow (b.cap i t outside)) (b.shadow x)) :=
          b.cross_meet_eq _ x different not_kx not_xk
        _ = .inl (P.meet (b.base i) (b.shadow x)) := by rw [b.cap_shadow i t top outside]
        _ = .inl (b.base i) := congrArg Sum.inl
          (meet_eq_left_of_le P (P.trans (b.base_le_separator i) above_e))

theorem cap_alternatives (i j : I) (different : i ≠ j)
    (ti : b.Space i) (tj : b.Space j)
    (top_i : ∀ y, (b.order i).le y ti) (top_j : ∀ y, (b.order j).le y tj)
    (outside_i : ¬ (b.order i).le ti (b.anchor i))
    (outside_j : ¬ (b.order j).le tj (b.anchor j)) :
    b.extension.le (.inr (b.cap i ti outside_i)) (.inl (b.base j)) ∨
    b.extension.le (.inr (b.cap j tj outside_j)) (.inl (b.base i)) ∨
    b.extension.meet (.inr (b.cap i ti outside_i)) (.inr (b.cap j tj outside_j)) =
      b.extension.meet (.inl (b.base i)) (.inl (b.base j)) := by
  classical
  by_cases hij : b.extension.le (.inr (b.cap i ti outside_i)) (.inr (b.cap j tj outside_j))
  · apply Or.inl
    have h := (b.cross_le_iff _ _ different).mp hij
    rw [b.cap_shadow j tj top_j outside_j] at h
    exact h
  · apply Or.inr
    by_cases hji : b.extension.le (.inr (b.cap j tj outside_j)) (.inr (b.cap i ti outside_i))
    · apply Or.inl
      have h := (b.cross_le_iff _ _ (Ne.symm different)).mp hji
      rw [b.cap_shadow i ti top_i outside_i] at h
      exact h
    · apply Or.inr
      rw [b.cross_meet_eq _ _ different hij hji,
        b.cap_shadow i ti top_i outside_i, b.cap_shadow j tj top_j outside_j]
      exact b.oldEmbedding.map_meet _ _

theorem equal_base_caps_meet (i j : I) (different : i ≠ j)
    (same_base : b.base i = b.base j)
    (ti : b.Space i) (tj : b.Space j)
    (top_i : ∀ y, (b.order i).le y ti) (top_j : ∀ y, (b.order j).le y tj)
    (outside_i : ¬ (b.order i).le ti (b.anchor i))
    (outside_j : ¬ (b.order j).le tj (b.anchor j)) :
    b.extension.meet (.inr (b.cap i ti outside_i)) (.inr (b.cap j tj outside_j)) =
      .inl (b.base i) := by
  have h := b.cap_alternatives i j different ti tj top_i top_j outside_i outside_j
  cases h with
  | inl h =>
    have h' : b.upper i (b.base j) := h
    rw [← same_base] at h'
    exact False.elim (b.data.base_not_upper i h')
  | inr h =>
    cases h with
    | inl h =>
      have h' : b.upper j (b.base i) := h
      rw [same_base] at h'
      exact False.elim (b.data.base_not_upper j h')
    | inr h =>
      rw [← same_base] at h
      exact h.trans (meet_eq_left_of_le b.extension (b.extension.refl _))

theorem initial_profile_persists {A : Type v} {Q : MeetOrder A}
    (next : MeetEmbedding b.extension Q) (allowed : PermittedExtension next)
    (i : I) (t : b.Space i) (top : ∀ y, (b.order i).le y t)
    (outside : ¬ (b.order i).le t (b.anchor i)) :
    ProfileOver next (.inl (b.base i)) (.inl (b.separator i))
      (.inr (b.cap i t outside)) (b.originalFamily i) := by
  have family_nonempty : ∃ f, b.originalFamily i f := by
    rcases b.upper_nonempty i with ⟨f, hf⟩
    exact ⟨.inl f, hf⟩
  exact profile_persists_one_step next _ _ _ _ family_nonempty
    (b.initial_profile i t top outside) (b.separator_not_below_cap i t top outside) allowed

end Attachment.Templates

namespace Compression

structure MeetFilter {A : Type u} (P : MeetOrder A) where
  mem : A → Prop
  nonempty : ∃ x, mem x
  upward : ∀ {x y}, mem x → P.le x y → mem y
  closed_meet : ∀ {x y}, mem x → mem y → mem (P.meet x y)

def pushFilter {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) : MeetFilter Q where
  mem y := ∃ x, F.mem x ∧ Q.le (s.toFun x) y
  nonempty := by
    rcases F.nonempty with ⟨x, hx⟩
    exact ⟨s.toFun x, x, hx, Q.refl _⟩
  upward := by
    rintro a b ⟨x, hx, hxa⟩ hab
    exact ⟨x, hx, Q.trans hxa hab⟩
  closed_meet := by
    rintro a b ⟨x, hx, hxa⟩ ⟨y, hy, hyb⟩
    refine ⟨P.meet x y, F.closed_meet hx hy, ?_⟩
    rw [s.map_meet]
    exact Q.le_meet (Q.trans (Q.meet_le_left _ _) hxa)
      (Q.trans (Q.meet_le_right _ _) hyb)

theorem pushFilter_trace {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) (x : A) :
    (pushFilter s F).mem (s.toFun x) ↔ F.mem x := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact F.upward hy ((s.le_iff y x).mp hyx)
  · intro hx
    exact ⟨x, hx, Q.refl _⟩

theorem pushFilter_lower_bound {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) (F : MeetFilter P) (e : A)
    (lower : ∀ f, F.mem f → P.le e f) :
    ∀ y, (pushFilter s F).mem y → Q.le (s.toFun e) y := by
  rintro y ⟨f, hf, hfy⟩
  exact Q.trans ((s.le_iff e f).mpr (lower f hf)) hfy

structure MeetIso {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    extends MeetEmbedding P Q where
  inverse : B → A
  left_inverse : ∀ x, inverse (toFun x) = x
  right_inverse : ∀ y, toFun (inverse y) = y

theorem filter_image_from_slice {A : Type u} (P : MeetOrder A) (F : MeetFilter P)
    (g : MeetIso P P) (v : A) (hv : F.mem v) (y : A) :
    (∃ f, F.mem f ∧ g.toFun f = y) ↔
    (∃ x, F.mem x ∧ P.le x v ∧ P.le (g.toFun x) y) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨P.meet f v, F.closed_meet hf hv, P.meet_le_right f v,
      (g.le_iff _ _).mpr (P.meet_le_left f v)⟩
  · rintro ⟨x, hx, _, hxy⟩
    have hxinv : P.le x (g.inverse y) := by
      apply (g.le_iff _ _).mp
      rw [g.right_inverse]
      exact hxy
    exact ⟨g.inverse y, F.upward hx hxinv, g.right_inverse y⟩

theorem filter_images_agree {A : Type u} (P : MeetOrder A) (F : MeetFilter P)
    (g h : MeetIso P P) (v : A) (hv : F.mem v)
    (agree : ∀ x, P.le x v → g.toFun x = h.toFun x) :
    ∀ y, (∃ f, F.mem f ∧ g.toFun f = y) ↔ (∃ f, F.mem f ∧ h.toFun f = y) := by
  intro y
  rw [filter_image_from_slice P F g v hv, filter_image_from_slice P F h v hv]
  constructor
  · rintro ⟨x, hx, hxv, hxy⟩
    exact ⟨x, hx, hxv, agree x hxv ▸ hxy⟩
  · rintro ⟨x, hx, hxv, hxy⟩
    exact ⟨x, hx, hxv, (agree x hxv).symm ▸ hxy⟩

theorem meet_insert_upper {A : Type u} (P : MeetOrder A) (x y a : A)
    (hya : P.le y a) : P.meet x y = P.meet (P.meet x a) y := by
  apply P.antisymm
  · exact P.le_meet (P.le_meet (P.meet_le_left x y) (P.trans (P.meet_le_right x y) hya))
      (P.meet_le_right x y)
  · exact P.le_meet (P.trans (P.meet_le_left _ _) (P.meet_le_left x a))
      (P.meet_le_right _ _)

theorem base_meet_patch {A : Type u} {B : Type v} (P : MeetOrder A) (Q : MeetOrder B)
    (s : A → B) (g : MeetEmbedding P Q) (a : A) (c : B)
    (ga : g.toFun a = c)
    (agree : ∀ y, P.le y a → s y = g.toFun y)
    (cut_law : ∀ x, Q.meet (s x) c = s (P.meet x a))
    (x y : A) (hya : P.le y a) : Q.meet (s x) (s y) = s (P.meet x y) := by
  have syc : Q.le (s y) c := by
    rw [agree y hya, ← ga]
    exact (g.le_iff y a).mpr hya
  calc
    Q.meet (s x) (s y) = Q.meet (Q.meet (s x) c) (s y) := meet_insert_upper Q _ _ _ syc
    _ = Q.meet (s (P.meet x a)) (s y) := by rw [cut_law]
    _ = Q.meet (g.toFun (P.meet x a)) (g.toFun y) := by
      rw [agree _ (P.meet_le_right x a), agree y hya]
    _ = g.toFun (P.meet (P.meet x a) y) := (g.map_meet _ _).symm
    _ = g.toFun (P.meet x y) := congrArg g.toFun (meet_insert_upper P x y a hya).symm
    _ = s (P.meet x y) := (agree _ (P.trans (P.meet_le_right x y) hya)).symm

theorem base_ideal_filled {A : Type u} (P : MeetOrder A) (s : A → A)
    (g : MeetIso P P) (a : A)
    (agree : ∀ y, P.le y a → s y = g.toFun y) :
    ∀ x, P.le x (g.toFun a) → ∃ y, s y = x := by
  intro x hx
  have hy : P.le (g.inverse x) a := by
    apply (g.le_iff _ _).mp
    rw [g.right_inverse]
    exact hx
  exact ⟨g.inverse x, (agree _ hy).trans (g.right_inverse x)⟩

theorem range_completion_from_accounting {A : Type u} {J : Type v}
    (P : MeetOrder A) (Original : A → Prop) (base cap : J → A) (s : J → A → A)
    (base_filled : ∀ i x, P.le x (base i) → ∃ y, s i y = x)
    (old_shadow : ∀ i x, Original x → P.le x (cap i) → P.le x (base i))
    (separation : ∀ i j, i ≠ j →
      P.le (cap i) (base j) ∨ P.le (cap j) (base i) ∨
      P.meet (cap i) (cap j) = P.meet (base i) (base j))
    (accounting : ∀ x, Original x ∨
      ∃ j y, s j y = x ∧ P.le x (cap j) ∧ ¬ P.le x (base j)) :
    ∀ i x, P.le x (cap i) → ∃ y, s i y = x := by
  classical
  intro i x hxi
  cases accounting x with
  | inl old => exact base_filled i x (old_shadow i x old hxi)
  | inr new =>
    rcases new with ⟨j, y, hy, hxj, not_base⟩
    by_cases same : j = i
    · cases same
      exact ⟨y, hy⟩
    · cases separation j i same with
      | inl hjci => exact base_filled i x (P.trans hxj hjci)
      | inr h =>
        cases h with
        | inl hicj => exact False.elim (not_base (P.trans hxi hicj))
        | inr hmeet =>
          have hxmeet : P.le x (P.meet (base j) (base i)) := hmeet ▸ P.le_meet hxj hxi
          exact base_filled i x (P.trans hxmeet (P.meet_le_right _ _))

theorem embedding_injective {A : Type u} {B : Type v} {P : MeetOrder A} {Q : MeetOrder B}
    (s : MeetEmbedding P Q) {x y : A} (h : s.toFun x = s.toFun y) : x = y := by
  apply P.antisymm
  · apply (s.le_iff x y).mp
    rw [h]
    exact Q.refl _
  · apply (s.le_iff y x).mp
    rw [h]
    exact Q.refl _

noncomputable def isoOntoIdeal {A : Type u} (P : MeetOrder A)
    (s : MeetEmbedding P P) (k : A)
    (below : ∀ x, P.le (s.toFun x) k)
    (onto : ∀ z, P.le z k → ∃ x, s.toFun x = z) :
    MeetIso P (Attachment.idealOrder P k) where
  toFun x := ⟨s.toFun x, below x⟩
  le_iff x y := s.le_iff x y
  map_meet x y := Subtype.ext (s.map_meet x y)
  inverse z := Classical.choose (onto z.val z.property)
  left_inverse x := embedding_injective s (Classical.choose_spec (onto (s.toFun x) (below x)))
  right_inverse z := Subtype.ext (Classical.choose_spec (onto z.val z.property))

structure InitialTasks {A : Type u} (P : MeetOrder A) (J : Type v) where
  source : J → A
  representative : J → MeetIso P P
  filter : J → MeetFilter P
  separator : J → A
  base_le_separator : ∀ i, P.le ((representative i).toFun (source i)) (separator i)
  separator_not_le_base : ∀ i, ¬ P.le (separator i) ((representative i).toFun (source i))
  separator_le_filter : ∀ i f, (filter i).mem f → P.le (separator i) f

namespace InitialTasks

variable {A : Type u} {J : Type v} {P : MeetOrder A} (d : InitialTasks P J)

def batch : Attachment.Templates P J where
  Space _ := A
  order _ := P
  anchor := d.source
  embed i := {
    toFun y := (d.representative i).toFun y.val
    le_iff x y := (d.representative i).le_iff x.val y.val
    map_meet x y := (d.representative i).map_meet x.val y.val }
  upper i := (d.filter i).mem
  upper_nonempty i := (d.filter i).nonempty
  upper_up i := (d.filter i).upward
  upper_meet i := (d.filter i).closed_meet
  separator := d.separator
  base_le_separator := d.base_le_separator
  separator_not_le_base := d.separator_not_le_base
  separator_le_upper := d.separator_le_filter

noncomputable def copy (i : J) : MeetEmbedding P d.batch.extension :=
  d.batch.templateEmbedding i

theorem copy_agrees_on_base (i : J) (y : A) (hy : P.le y (d.source i)) :
    (d.copy i).toFun y = .inl ((d.representative i).toFun y) :=
  d.batch.template_agrees_on_base i y hy

theorem copy_initial_profile (T : A) (top : ∀ y, P.le y T)
    (outside : ∀ i, ¬ P.le T (d.source i)) (i : J) :
    Profile d.batch.extension (.inl ((d.representative i).toFun (d.source i)))
      (.inl (d.separator i)) ((d.copy i).toFun T) (d.batch.originalFamily i) := by
  change Profile d.batch.extension (.inl (d.batch.base i)) (.inl (d.batch.separator i))
    (d.batch.represent i T) (d.batch.originalFamily i)
  rw [d.batch.represent_new i T (outside i)]
  exact d.batch.initial_profile i T top (outside i)

theorem copy_cap_separation (T : A) (top : ∀ y, P.le y T)
    (outside : ∀ i, ¬ P.le T (d.source i)) (i j : J) (different : i ≠ j) :
    d.batch.extension.le ((d.copy i).toFun T) (.inl (d.batch.base j)) ∨
    d.batch.extension.le ((d.copy j).toFun T) (.inl (d.batch.base i)) ∨
    d.batch.extension.meet ((d.copy i).toFun T) ((d.copy j).toFun T) =
      d.batch.extension.meet (.inl (d.batch.base i)) (.inl (d.batch.base j)) := by
  change d.batch.extension.le (d.batch.represent i T) (.inl (d.batch.base j)) ∨
    d.batch.extension.le (d.batch.represent j T) (.inl (d.batch.base i)) ∨
    d.batch.extension.meet (d.batch.represent i T) (d.batch.represent j T) = _
  rw [d.batch.represent_new i T (outside i), d.batch.represent_new j T (outside j)]
  exact d.batch.cap_alternatives i j different T T top top (outside i) (outside j)

end InitialTasks

end Compression

end PartitionPilot

end OAI
