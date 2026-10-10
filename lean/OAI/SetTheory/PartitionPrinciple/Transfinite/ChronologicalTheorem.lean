import OAI.SetTheory.PartitionPrinciple.Geometry.CompressionTheorem

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Chronological

universe u v w

variable {A : Type u} {P : MeetOrder A}

def CountableBelow (F : MeetFilter P) (target : A → Prop) : Prop :=
  ∃ B : Set A, B.Countable ∧ (∀ x ∈ B, F.mem x) ∧
    ∀ x, target x → ∃ y ∈ B, P.le y x

def CountableBasis (F : MeetFilter P) : Prop := CountableBelow F F.mem

def AllFiltersCountable (P : MeetOrder A) : Prop := ∀ F : MeetFilter P, CountableBasis F

theorem countableBelow_mono (F : MeetFilter P) {small large : A → Prop}
    (basis : CountableBelow F large) (subset : ∀ x, small x → large x) : CountableBelow F small := by
  rcases basis with ⟨B, countable, positive, coinitial⟩
  exact ⟨B, countable, positive, fun x hx => coinitial x (subset x hx)⟩

theorem countableBelow_empty (F : MeetFilter P) (target : A → Prop)
    (empty : ∀ x, ¬ target x) : CountableBelow F target :=
  ⟨∅, Set.countable_empty, by simp, fun x hx => False.elim (empty x hx)⟩

theorem countableBelow_of_countable (F : MeetFilter P) (target : A → Prop)
    (countable : Set.Countable {x | target x}) (positive : ∀ x, target x → F.mem x) :
    CountableBelow F target :=
  ⟨{x | target x}, countable, positive, fun x hx => ⟨x, hx, P.refl x⟩⟩

theorem countableBelow_union {I : Type v} [Countable I] (F : MeetFilter P)
    (target : A → Prop) (parts : I → A → Prop)
    (cover : ∀ x, target x → ∃ i, parts i x)
    (localBases : ∀ i, CountableBelow F (parts i)) : CountableBelow F target := by
  classical
  choose B countable positive coinitial using localBases
  refine ⟨⋃ i, B i, Set.countable_iUnion countable, ?_, ?_⟩
  · intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
    exact positive i x hi
  · intro x hx
    rcases cover x hx with ⟨i, hi⟩
    rcases coinitial i x hi with ⟨y, hy, below⟩
    exact ⟨y, Set.mem_iUnion.mpr ⟨i, hy⟩, below⟩

def pullFilter {B : Type v} {Q : MeetOrder B} (e : MeetEmbedding Q P) (F : MeetFilter P)
    (inhabited : ∃ x, F.mem (e.toFun x)) : MeetFilter Q where
  mem x := F.mem (e.toFun x)
  nonempty := inhabited
  upward hx lower := F.upward hx ((e.le_iff _ _).mpr lower)
  closed_meet hx hy := by
    rw [e.map_meet]
    exact F.closed_meet hx hy

theorem countableBelow_copy {B : Type v} {Q : MeetOrder B}
    (e : MeetEmbedding Q P) (F : MeetFilter P) (earlier : AllFiltersCountable Q) :
    CountableBelow F (fun x => F.mem x ∧ ∃ y, e.toFun y = x) := by
  classical
  by_cases inhabited : ∃ y, F.mem (e.toFun y)
  · rcases earlier (pullFilter e F inhabited) with ⟨B, countable, positive, coinitial⟩
    refine ⟨e.toFun '' B, countable.image e.toFun, ?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact positive y hy
    · rintro x ⟨hx, y, rfl⟩
      rcases coinitial y hx with ⟨z, hz, lower⟩
      exact ⟨e.toFun z, ⟨z, hz, rfl⟩, (e.le_iff _ _).mpr lower⟩
  · refine ⟨∅, Set.countable_empty, by simp, ?_⟩
    rintro x ⟨hx, y, rfl⟩
    exact False.elim (inhabited ⟨y, hx⟩)

section Birth

variable {Stage : Type v} [LinearOrder Stage] (birth : A → Stage)

def Essential (F : MeetFilter P) (x : A) : Prop :=
  F.mem x ∧ ∀ y, F.mem y → P.le y x → ¬ birth y < birth x

def EssentialStages (F : MeetFilter P) : Set Stage :=
  {s | ∃ x, Essential birth F x ∧ birth x = s}

theorem positive_above_essential [WellFoundedLT Stage] (F : MeetFilter P)
    (x : A) (positive : F.mem x) : ∃ y, Essential birth F y ∧ P.le y x := by
  let S : Set Stage := {s | ∃ y, F.mem y ∧ P.le y x ∧ birth y = s}
  have inhabited : S.Nonempty := ⟨birth x, x, positive, P.refl x, rfl⟩
  rcases wellFounded_lt.has_min S inhabited with ⟨s, ⟨y, hy, below, born⟩, minimal⟩
  refine ⟨y, ⟨hy, ?_⟩, below⟩
  intro z hz lower earlier
  apply minimal (birth z) ⟨z, hz, P.trans lower below, rfl⟩
  exact born ▸ earlier

def OldMeet : Prop := ∀ x y, birth y < birth x → ¬ P.le x y →
  birth (P.meet x y) < birth x

theorem essential_below_earlier (oldMeet : OldMeet (P := P) birth) (F : MeetFilter P)
    (x y : A) (essential : Essential birth F x) (positive : F.mem y)
    (earlier : birth y < birth x) : P.le x y ∧ x ≠ y := by
  classical
  have lower : P.le x y := by
    by_contra hn
    exact essential.2 (P.meet x y) (F.closed_meet essential.1 positive)
      (P.meet_le_left x y) (oldMeet x y earlier hn)
  refine ⟨lower, ?_⟩
  intro eq
  subst y
  exact lt_irrefl _ earlier

def DescendingCountable {H : Type w} (R : HeightOrder H) : Prop :=
  ∀ (S : Set Stage) (value : S → H),
    (∀ i j : S, i.val < j.val → R.lt (value j) (value i)) → S.Countable

theorem essential_stages_countable {H : Type w} {R : HeightOrder H}
    (height : StrictHeight P R) (descending : DescendingCountable (Stage := Stage) R)
    (oldMeet : OldMeet (P := P) birth) (F : MeetFilter P) :
    (EssentialStages birth F).Countable := by
  classical
  let point : EssentialStages birth F → A := fun s => Classical.choose s.property
  have essential : ∀ s, Essential birth F (point s) :=
    fun s => (Classical.choose_spec s.property).1
  have born : ∀ s, birth (point s) = s.val :=
    fun s => (Classical.choose_spec s.property).2
  apply descending (EssentialStages birth F) (fun s => height.value (point s))
  intro i j earlier
  have old : birth (point i) < birth (point j) := by rw [born, born]; exact earlier
  have lower := essential_below_earlier birth oldMeet F (point j) (point i)
    (essential j) (essential i).1 old
  exact height.strict _ _ lower.1 lower.2

theorem countable_basis_of_layers [WellFoundedLT Stage] (F : MeetFilter P)
    (stages : (EssentialStages birth F).Countable)
    (localBases : ∀ s, CountableBelow F (fun x => Essential birth F x ∧ birth x = s)) :
    CountableBasis F := by
  have := stages.to_subtype
  have essentials : CountableBelow F (Essential birth F) :=
    countableBelow_union F (Essential birth F)
      (fun s : EssentialStages birth F => fun x => Essential birth F x ∧ birth x = s.val)
      (fun x hx => ⟨⟨birth x, x, hx, rfl⟩, hx, rfl⟩)
      (fun s => localBases s.val)
  rcases essentials with ⟨B, countable, positive, coinitial⟩
  refine ⟨B, countable, positive, ?_⟩
  intro x hx
  rcases positive_above_essential birth F x hx with ⟨y, hy, lower⟩
  rcases coinitial y hy with ⟨z, hz, below⟩
  exact ⟨z, hz, P.trans below lower⟩

end Birth

end PartitionPilot.Compression.RecursiveMaps.Chronological



namespace PartitionPilot.Compression.RecursiveMaps.Chronological

universe u v

variable {A Stage : Type u} [LinearOrder Stage] {P : MeetOrder A}

def OldBridge (birth : A → Stage) (s : Stage) (x y : A) : Prop :=
  birth (P.meet x y) < s ∨
    (∃ z, birth z < s ∧ P.le x z ∧ P.le z y) ∨
    (∃ z, birth z < s ∧ P.le y z ∧ P.le z x)

theorem essentials_no_bridge (birth : A → Stage) (F : MeetFilter P) (s : Stage)
    (x y : A) (hx : Essential birth F x) (hy : Essential birth F y)
    (bx : birth x = s) (by_ : birth y = s) : ¬ OldBridge (P := P) birth s x y := by
  intro bridge
  rcases bridge with meet | between | between
  · exact hx.2 (P.meet x y) (F.closed_meet hx.1 hy.1) (P.meet_le_left x y) (bx ▸ meet)
  · rcases between with ⟨z, old, lower, upper⟩
    exact hy.2 z (F.upward hx.1 lower) upper (by_ ▸ old)
  · rcases between with ⟨z, old, lower, upper⟩
    exact hx.2 z (F.upward hy.1 lower) upper (bx ▸ old)

inductive GrowthLayer (Space : Stage → Type u) (order : ∀ s, MeetOrder (Space s))
    (P : MeetOrder A) (birth : A → Stage) (s : Stage) : Type (u + 1) where
  | countablePoints (small : Set.Countable {x | birth x = s})
  | copies (I : Type u) (small : Countable I) (index : I → Stage)
      (earlier : ∀ i, index i < s)
      (copy : ∀ i, MeetEmbedding (order (index i)) P)
      (cover : ∀ x, birth x = s → ∃ i y, (copy i).toFun y = x)
  | separated (I : Type u) (index : I → Stage) (earlier : ∀ i, index i < s)
      (copy : ∀ i, MeetEmbedding (order (index i)) P)
      (component : {x // birth x = s} → I)
      (cover : ∀ x : {x // birth x = s}, ∃ y, (copy (component x)).toFun y = x.val)
      (separated : ∀ x y : {x // birth x = s}, component x ≠ component y →
        OldBridge (P := P) birth s x.val y.val)

theorem GrowthLayer.countable_essentials {Space : Stage → Type u}
    {order : ∀ s, MeetOrder (Space s)} {birth : A → Stage} {s : Stage}
    (layer : GrowthLayer Space order P birth s) (F : MeetFilter P)
    (inductionHypothesis : ∀ t, t < s → AllFiltersCountable (order t)) :
    CountableBelow F (fun x => Essential birth F x ∧ birth x = s) := by
  classical
  cases layer with
  | countablePoints small =>
    exact countableBelow_of_countable F _ (small.mono (fun _ h => h.2)) (fun _ h => h.1.1)
  | copies I small index earlier copy cover =>
    let := small
    apply countableBelow_union F _ (fun i => fun x => F.mem x ∧ ∃ y, (copy i).toFun y = x)
    · intro x hx
      rcases cover x hx.2 with ⟨i, y, eq⟩
      exact ⟨i, hx.1.1, y, eq⟩
    · intro i
      exact countableBelow_copy (copy i) F (inductionHypothesis (index i) (earlier i))
  | separated I index earlier copy component cover separated =>
    by_cases existsEssential : ∃ x, Essential birth F x ∧ birth x = s
    · rcases existsEssential with ⟨x, hx, bx⟩
      let i := component ⟨x, bx⟩
      apply countableBelow_mono F
        (countableBelow_copy (copy i) F (inductionHypothesis (index i) (earlier i)))
      intro y hy
      have same : component ⟨y, hy.2⟩ = i := by
        by_contra different
        exact essentials_no_bridge birth F s y x hy.1 hx hy.2 bx
          (separated ⟨y, hy.2⟩ ⟨x, bx⟩ different)
      have hz := cover ⟨y, hy.2⟩
      rw [same] at hz
      exact ⟨hy.1.1, hz⟩
    · exact countableBelow_empty F _ (fun x hx => existsEssential ⟨x, hx⟩)

structure History (Stage : Type u) [LinearOrder Stage] {H : Type v} (R : HeightOrder H) where
  Space : Stage → Type u
  order : ∀ s, MeetOrder (Space s)
  birth : ∀ s, Space s → Stage
  birth_le : ∀ s x, birth s x ≤ s
  old_meet : ∀ s, OldMeet (P := order s) (birth s)
  height : ∀ s, StrictHeight (order s) R
  layer : ∀ cutoff s, s ≤ cutoff → GrowthLayer Space order (order cutoff) (birth cutoff) s

theorem History.all_filters_countable [WellFoundedLT Stage] {H : Type v} {R : HeightOrder H}
    (history : History Stage R) (descending : DescendingCountable (Stage := Stage) R) :
    ∀ cutoff, AllFiltersCountable (history.order cutoff) := by
  intro cutoff
  have wf : WellFounded ((· < ·) : Stage → Stage → Prop) := wellFounded_lt
  induction cutoff using wf.induction with
  | h cutoff ih =>
    intro F
    apply countable_basis_of_layers (history.birth cutoff) F
    · exact essential_stages_countable (history.birth cutoff) (history.height cutoff)
        descending (history.old_meet cutoff) F
    · intro s
      by_cases present : s ≤ cutoff
      · apply (history.layer cutoff s present).countable_essentials F
        intro t earlier
        exact ih t (lt_of_lt_of_le earlier present)
      · apply countableBelow_empty F _
        intro x hx
        apply present
        rw [← hx.2]
        exact history.birth_le cutoff x

end PartitionPilot.Compression.RecursiveMaps.Chronological

end

end OAI
