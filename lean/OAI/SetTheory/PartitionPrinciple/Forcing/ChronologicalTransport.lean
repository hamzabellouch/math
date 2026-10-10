import OAI.SetTheory.PartitionPrinciple.Geometry.BinaryTiles

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Chronological

universe u v

variable {A B Stage : Type u} [LinearOrder Stage]
    {P : MeetOrder A} {Q : MeetOrder B}

theorem OldBridge.map (e : MeetEmbedding P Q) (birthA : A → Stage) (birthB : B → Stage)
    (preserves : ∀ x, birthB (e.toFun x) = birthA x) (s : Stage) (x y : A)
    (bridge : OldBridge (P := P) birthA s x y) :
    OldBridge (P := Q) birthB s (e.toFun x) (e.toFun y) := by
  rcases bridge with meet | between | between
  · left
    rw [← e.map_meet, preserves]
    exact meet
  · rcases between with ⟨z, old, lower, upper⟩
    exact Or.inr (Or.inl ⟨e.toFun z, (preserves z).symm ▸ old,
      (e.le_iff _ _).mpr lower, (e.le_iff _ _).mpr upper⟩)
  · rcases between with ⟨z, old, lower, upper⟩
    exact Or.inr (Or.inr ⟨e.toFun z, (preserves z).symm ▸ old,
      (e.le_iff _ _).mpr lower, (e.le_iff _ _).mpr upper⟩)

noncomputable def GrowthLayer.transport {Space : Stage → Type u}
    {order : ∀ s, MeetOrder (Space s)} {birthA : A → Stage} {birthB : B → Stage} {s : Stage}
    (layer : GrowthLayer Space order P birthA s) (e : MeetEmbedding P Q)
    (preserves : ∀ x, birthB (e.toFun x) = birthA x)
    (noNew : ∀ x, birthB x = s → ∃ y, e.toFun y = x) :
    GrowthLayer Space order Q birthB s := by
  classical
  cases layer with
  | countablePoints small =>
    apply GrowthLayer.countablePoints
    apply (small.image e.toFun).mono
    intro x hx
    rcases noNew x hx with ⟨y, rfl⟩
    exact ⟨y, (preserves y).symm.trans hx, rfl⟩
  | copies I small index earlier copy cover =>
    apply GrowthLayer.copies I small index earlier (fun i => compose (copy i) e)
    intro x hx
    rcases noNew x hx with ⟨y, rfl⟩
    rcases cover y ((preserves y).symm.trans hx) with ⟨i, z, eq⟩
    exact ⟨i, z, congrArg e.toFun eq⟩
  | separated I index earlier copy component cover separated =>
    let pre : {x // birthB x = s} → {x // birthA x = s} := fun x =>
      let y := Classical.choose (noNew x.val x.property)
      have eq : e.toFun y = x.val := Classical.choose_spec (noNew x.val x.property)
      ⟨y, by rw [← preserves, eq]; exact x.property⟩
    have pre_eq : ∀ x, e.toFun (pre x).val = x.val :=
      fun x => Classical.choose_spec (noNew x.val x.property)
    apply GrowthLayer.separated I index earlier (fun i => compose (copy i) e)
      (fun x => component (pre x))
    · intro x
      rcases cover (pre x) with ⟨y, eq⟩
      exact ⟨y, (congrArg e.toFun eq).trans (pre_eq x)⟩
    · intro x y different
      have bridge := OldBridge.map e birthA birthB preserves s (pre x).val (pre y).val
        (separated (pre x) (pre y) different)
      rw [pre_eq, pre_eq] at bridge
      exact bridge

theorem oldMeet_of_covered_stages {I : Type v} {Space : I → Type u}
    (order : ∀ i, MeetOrder (Space i)) (birth : B → Stage)
    (stageBirth : ∀ i, Space i → Stage) (embed : ∀ i, MeetEmbedding (order i) Q)
    (preserves : ∀ i x, birth ((embed i).toFun x) = stageBirth i x)
    (pairCover : ∀ x y, ∃ i a b, (embed i).toFun a = x ∧ (embed i).toFun b = y)
    (oldMeet : ∀ i, OldMeet (P := order i) (stageBirth i)) : OldMeet (P := Q) birth := by
  intro x y earlier notLower
  rcases pairCover x y with ⟨i, a, b, rfl, rfl⟩
  rw [preserves, preserves] at earlier
  have old := oldMeet i a b earlier (fun h => notLower (((embed i).le_iff _ _).mpr h))
  rw [← (embed i).map_meet, preserves, preserves]
  exact old

end PartitionPilot.Compression.RecursiveMaps.Chronological

end

end OAI
