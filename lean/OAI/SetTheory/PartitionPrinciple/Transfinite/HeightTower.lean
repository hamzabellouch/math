import OAI.SetTheory.PartitionPrinciple.Geometry.HeightAttachment

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

structure IntervalHeights {A : Type u} {Column : Type v} {Coord : Type w} (P : MeetOrder A)
    (R : HeightOrder (Column × Coord)) where
  assign : ∀ lo hi, R.lt lo hi → StrictHeight P R
  lower : ∀ lo hi (gap : R.lt lo hi) x, R.lt lo ((assign lo hi gap).value x)
  upper : ∀ lo hi (gap : R.lt lo hi) x, R.lt ((assign lo hi gap).value x) hi
  column : ∀ lo hi (gap : R.lt lo hi) x, ((assign lo hi gap).value x).1 = lo.1

def CountableRange {A : Type u} {B : Type v} (value : A → B) : Prop :=
  ∃ code : A → Nat, ∀ x y, code x = code y → value x = value y

namespace TaskSystem

variable {A G Task Label : Type u} {P : MeetOrder A} (f : TaskSystem P G Task Label)
    {Column : Type v} {Coord : Type w} {R : HeightOrder (Column × Coord)}
    (intervals : IntervalHeights P R)

theorem height_gap (n : Nat) (old : StrictHeight (f.order n) R)
    (i : (f.stages n).Components) :
    R.lt (old.value ((f.stages n).batch.base i)) (old.value ((f.stages n).batch.separator i)) := by
  apply old.strict _ _ ((f.stages n).batch.base_le_separator i)
  intro eq
  apply (f.stages n).batch.separator_not_le_base i
  rw [eq]
  exact (f.order n).refl _

noncomputable def componentHeight (n : Nat) (old : StrictHeight (f.order n) R)
    (i : (f.stages n).Components) : StrictHeight ((f.stages n).batch.order i) R :=
  (intervals.assign (old.value ((f.stages n).batch.base i))
    (old.value ((f.stages n).batch.separator i)) (f.height_gap n old i)).precompose
      (f.templateOriginal n i).toMeetEmbedding

noncomputable def nextHeight (n : Nat) (old : StrictHeight (f.order n) R) :
    StrictHeight (f.order (n + 1)) R :=
  AttachmentHeight.extend (f.stages n).batch old (f.componentHeight intervals n old)
    (fun x => intervals.lower _ _ (f.height_gap n old x.1) ((f.templateOriginal n x.1).toFun x.2.val))
    (fun x => intervals.upper _ _ (f.height_gap n old x.1) ((f.templateOriginal n x.1).toFun x.2.val))

theorem nextHeight_old (n : Nat) (old : StrictHeight (f.order n) R) (x : f.Point n) :
    (f.nextHeight intervals n old).value ((f.step n).toFun x) = old.value x := rfl

theorem nextHeight_column (n : Nat) (old : StrictHeight (f.order n) R)
    (x : (f.stages n).batch.Fresh) :
    ((f.nextHeight intervals n old).value (.inr x)).1 =
      (old.value ((f.stages n).batch.base x.1)).1 :=
  intervals.column _ _ (f.height_gap n old x.1) ((f.templateOriginal n x.1).toFun x.2.val)

noncomputable def heightStages (seed : StrictHeight P R) :
    (n : Nat) → StrictHeight (f.order n) R
  | 0 => seed
  | n + 1 => f.nextHeight intervals n (heightStages seed n)

theorem heightStages_step (seed : StrictHeight P R) (n : Nat) (x : f.Point n) :
    (f.heightStages intervals seed (n + 1)).value ((f.step n).toFun x) =
      (f.heightStages intervals seed n).value x := rfl

theorem heightStages_original (seed : StrictHeight P R) (n : Nat) (x : A) :
    (f.heightStages intervals seed n).value ((f.origin n).toFun x) = seed.value x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [← f.origins_coherent, f.heightStages_step, ih]

theorem heightStages_column (seed : StrictHeight P R) (n : Nat) (x : f.Point n) :
    ∃ a : A, ((f.heightStages intervals seed n).value x).1 = (seed.value a).1 := by
  induction n with
  | zero => exact ⟨x, rfl⟩
  | succ n ih =>
    cases x with
    | inl x => exact ih x
    | inr x =>
      rcases ih ((f.stages n).batch.base x.1) with ⟨a, ha⟩
      exact ⟨a, (f.nextHeight_column intervals n _ x).trans ha⟩

noncomputable def unionHeightValue (seed : StrictHeight P R) : f.Union → Column × Coord
  | .inl a => seed.value a
  | .inr ⟨n, x⟩ => (f.heightStages intervals seed (n + 1)).value (.inr x)

theorem unionHeight_inclusion (seed : StrictHeight P R) (n : Nat) (x : f.Point n) :
    f.unionHeightValue intervals seed (f.inclusion n x) =
      (f.heightStages intervals seed n).value x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases x with
    | inl x => exact ih x
    | inr x => rfl

noncomputable def unionHeight (seed : StrictHeight P R) : StrictHeight f.unionOrder R where
  value := f.unionHeightValue intervals seed
  strict x y lower different := by
    rcases f.pair_cover x y with ⟨n, a, b, rfl, rfl⟩
    rw [f.unionHeight_inclusion, f.unionHeight_inclusion]
    exact (f.heightStages intervals seed n).strict a b
      (((f.inclusionEmbedding n).le_iff a b).mp lower)
      (fun eq => different (congrArg (f.inclusion n) eq))

theorem unionHeight_original (seed : StrictHeight P R) (x : A) :
    (f.unionHeight intervals seed).value (f.originalEmbedding.toFun x) = seed.value x := rfl

theorem unionHeight_bounded (seed : StrictHeight P R) (x : f.Union) :
    R.Weak ((f.unionHeight intervals seed).value x) (seed.value f.top) :=
  (f.unionHeight intervals seed).mono (f.union_top x)

theorem unionHeight_column (seed : StrictHeight P R) (x : f.Union) :
    ∃ a : A, ((f.unionHeight intervals seed).value x).1 = (seed.value a).1 := by
  rcases f.union_cover x with ⟨n, a, rfl⟩
  change ∃ b, (f.unionHeightValue intervals seed (f.inclusion n a)).1 = (seed.value b).1
  rw [f.unionHeight_inclusion]
  exact f.heightStages_column intervals seed n a

theorem unionHeight_countable (seed : StrictHeight P R) (seed_countable : CountableRange seed.value)
    (coordCode : Coord → Nat) (coord_injective : ∀ x y, coordCode x = coordCode y → x = y) :
    CountableRange (f.unionHeight intervals seed).value := by
  classical
  rcases seed_countable with ⟨seedCode, seed_equal⟩
  let source : f.Union → A := fun x => Classical.choose (f.unionHeight_column intervals seed x)
  have column : ∀ x, ((f.unionHeight intervals seed).value x).1 = (seed.value (source x)).1 :=
    fun x => Classical.choose_spec (f.unionHeight_column intervals seed x)
  refine ⟨fun x => natPair (seedCode (source x)) (coordCode ((f.unionHeight intervals seed).value x).2), ?_⟩
  intro x y eq
  have parts := natPair_injective eq
  apply Prod.ext
  · exact (column x).trans ((congrArg Prod.fst (seed_equal _ _ parts.1)).trans (column y).symm)
  · exact coord_injective _ _ parts.2

end TaskSystem
end PartitionPilot.Compression.RecursiveMaps

end

end OAI
