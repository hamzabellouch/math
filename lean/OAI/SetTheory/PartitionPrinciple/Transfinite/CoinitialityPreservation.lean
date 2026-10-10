import OAI.SetTheory.PartitionPrinciple.Geometry.FinalProfilePersistence

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.Chronological

universe u v w

theorem all_filters_of_countable {A : Type u} [Countable A] (P : MeetOrder A) :
    AllFiltersCountable P := fun F =>
  countableBelow_of_countable F F.mem (Set.to_countable _) (fun _ h => h)

theorem all_filters_of_countable_cover {A : Type u} {I : Type v} [Countable I]
    {P : MeetOrder A} (Space : I → Type w) (orders : ∀ i, MeetOrder (Space i))
    (copy : ∀ i, MeetEmbedding (orders i) P)
    (cover : ∀ x, ∃ i y, (copy i).toFun y = x)
    (small : ∀ i, AllFiltersCountable (orders i)) : AllFiltersCountable P := by
  intro F
  apply countableBelow_union F F.mem (fun i x => F.mem x ∧ ∃ y, (copy i).toFun y = x)
  · intro x positive
    rcases cover x with ⟨i, y, eq⟩
    exact ⟨i, positive, y, eq⟩
  · intro i
    exact countableBelow_copy (copy i) F (small i)

theorem all_filters_of_surjective {A : Type u} {B : Type v}
    {P : MeetOrder A} {Q : MeetOrder B} (e : MeetEmbedding P Q)
    (onto : Function.Surjective e.toFun) (small : AllFiltersCountable P) : AllFiltersCountable Q := by
  intro F
  exact countableBelow_mono F (countableBelow_copy e F small) (fun x hx => ⟨hx, onto x⟩)

def twoLayerBirth {O : Type u} {N : Type v} : O ⊕ N → ULift.{max u v} Nat
  | .inl _ => ⟨0⟩
  | .inr _ => ⟨1⟩

theorem all_filters_of_separated_sum {O N I : Type u} {P : MeetOrder O}
    (Q : MeetOrder (O ⊕ N)) (old : MeetEmbedding P Q)
    (old_eq : ∀ x, old.toFun x = .inl x)
    (Space : I → Type u) (orders : ∀ i, MeetOrder (Space i))
    (copy : ∀ i, MeetEmbedding (orders i) Q) (component : N → I)
    (cover : ∀ x, ∃ y, (copy (component x)).toFun y = .inr x)
    (separated : ∀ x y, component x ≠ component y →
      OldBridge (P := Q) twoLayerBirth ⟨1⟩ (.inr x) (.inr y))
    (oldSmall : AllFiltersCountable P) (copySmall : ∀ i, AllFiltersCountable (orders i)) :
    AllFiltersCountable Q := by
  classical
  let : WellFoundedLT (ULift.{u} Nat) := InvImage.wf ULift.down Nat.lt_wfRel.wf
  intro F
  have fresh : CountableBelow F
      (fun x => Essential twoLayerBirth F x ∧ ∃ y, Sum.inr y = x) := by
    by_cases inhabited : ∃ x : N, Essential twoLayerBirth F (.inr x)
    · rcases inhabited with ⟨x, hx⟩
      apply countableBelow_mono F (countableBelow_copy (copy (component x)) F (copySmall _))
      rintro y ⟨hy, z, rfl⟩
      have same : component z = component x := by
        by_contra different
        exact essentials_no_bridge twoLayerBirth F ⟨1⟩ (.inr z) (.inr x) hy hx rfl rfl
          (separated z x different)
      have covered := cover z
      rw [same] at covered
      exact ⟨hy.1, covered⟩
    · exact countableBelow_empty F _ (by
        rintro x ⟨hx, y, rfl⟩
        exact inhabited ⟨y, hx⟩)
  apply countable_basis_of_layers twoLayerBirth F (Set.to_countable _)
  rintro ⟨s⟩
  cases s with
  | zero =>
    apply countableBelow_mono F (countableBelow_copy old F oldSmall)
    rintro x ⟨hx, born⟩
    cases x with
    | inl x => exact ⟨hx.1, x, old_eq x⟩
    | inr x => exact False.elim (Nat.one_ne_zero (congrArg ULift.down born))
  | succ s =>
    apply countableBelow_mono F fresh
    rintro x ⟨hx, born⟩
    cases x with
    | inl x => exact False.elim (Nat.noConfusion (congrArg ULift.down born))
    | inr x => exact ⟨hx, x, rfl⟩

end PartitionPilot.Compression.RecursiveMaps.Chronological

end

end OAI
