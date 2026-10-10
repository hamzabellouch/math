import OAI.SetTheory.PartitionPrinciple.Geometry.PartialBatchStep

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family

universe u
variable {A I K : Type u} {P : MeetOrder A} (b : PrincipalBatch.Family P I)

theorem present_union [Nonempty K] (U : K → I → Prop) (x : b.Node) :
    b.Present (fun i => ∃ k, U k i) x ↔ ∃ k, b.Present (U k) x := by
  cases x with
  | inl x =>
    constructor
    · intro _
      exact ⟨Classical.choice inferInstance, True.intro⟩
    · intro _
      exact True.intro
  | inr x => exact Iff.rfl

theorem cutoff_union_cover [Nonempty K] (U : K → I → Prop)
    (x : b.Cutoff (fun i => ∃ k, U k i)) :
    ∃ k, ∃ y : b.Cutoff (U k),
      (b.cutoffInclusion (fun _ h => ⟨k, h⟩ : ∀ i, U k i → ∃ l, U l i)).toFun y = x := by
  rcases (b.present_union U x.val).mp x.property with ⟨k, hx⟩
  exact ⟨k, ⟨x.val, hx⟩, rfl⟩

theorem cutoff_union_pair [Nonempty K] (U : K → I → Prop)
    (directed : ∀ k l, ∃ m, (∀ i, U k i → U m i) ∧ ∀ i, U l i → U m i)
    (x y : b.Cutoff (fun i => ∃ k, U k i)) :
    ∃ k, b.Present (U k) x.val ∧ b.Present (U k) y.val := by
  rcases (b.present_union U x.val).mp x.property with ⟨k, hx⟩
  rcases (b.present_union U y.val).mp y.property with ⟨l, hy⟩
  rcases directed k l with ⟨m, hkm, hlm⟩
  exact ⟨m, b.present_mono hkm hx, b.present_mono hlm hy⟩

theorem cutoff_union_meet [Nonempty K] (U : K → I → Prop)
    (directed : ∀ k l, ∃ m, (∀ i, U k i → U m i) ∧ ∀ i, U l i → U m i)
    (x y : b.Cutoff (fun i => ∃ k, U k i)) :
    ∃ k, ∃ a c : b.Cutoff (U k), a.val = x.val ∧ c.val = y.val ∧
      ((b.cutoffOrder (U k)).meet a c).val =
        ((b.cutoffOrder (fun i => ∃ k, U k i)).meet x y).val := by
  rcases b.cutoff_union_pair U directed x y with ⟨k, hx, hy⟩
  exact ⟨k, ⟨x.val, hx⟩, ⟨y.val, hy⟩, rfl, rfl, rfl⟩

section Ordered
variable [LinearOrder I]

def before (t : I) (i : I) : Prop := i < t

theorem before_mono {s t : I} (h : s ≤ t) : ∀ i, before s i → before t i :=
  fun _ hi => lt_of_lt_of_le hi h

theorem through_iff (t i : I) : addComponent (before t) t i ↔ i ≤ t :=
  le_iff_lt_or_eq.symm

noncomputable def orderedStep (t : I) :
    MeetIso (b.stepInput (before t) t).order (b.cutoffOrder (addComponent (before t) t)) :=
  b.stepIso (before t) t (lt_irrefl t)

theorem before_limit (t : I) (earlier : ∃ s, s < t)
    (limit : ∀ i, i < t → ∃ s, i < s ∧ s < t) (x : b.Node) :
    b.Present (before t) x ↔ ∃ s, s < t ∧ b.Present (before s) x := by
  cases x with
  | inl x =>
    constructor
    · intro _
      rcases earlier with ⟨s, hs⟩
      exact ⟨s, hs, True.intro⟩
    · intro _
      exact True.intro
  | inr x =>
    constructor
    · intro hx
      rcases limit x.1 hx with ⟨s, his, hst⟩
      exact ⟨s, hst, his⟩
    · rintro ⟨s, hst, his⟩
      exact lt_trans his hst

end Ordered

end PartitionPilot.Compression.RecursiveMaps.PrincipalBatch.Family

end

end OAI
