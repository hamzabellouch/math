import OAI.SetTheory.PartitionPrinciple.Definability.GroundRefinementPairClassGraphs

namespace OAI

namespace PartitionPilot.Forcing
open SetRealization
universe u v

abbrev MainTransitionIndex (I : Type v) [Preorder I] := {p : I × I // p.1 ≤ p.2}

def mainTransitionIndexKey {I : Type v} [Preorder I] (key : I → ZFSet.{u})
    (p : MainTransitionIndex I) : ZFSet.{u} := ZFSet.pair (key p.val.2) (key p.val.1)

theorem mainTransitionIndexKey_injective {I : Type v} [Preorder I]
    (key : I → ZFSet.{u}) (injective : Function.Injective key) :
    Function.Injective (mainTransitionIndexKey key) := by
  intro p q equal
  obtain ⟨target, source⟩ := ZFSet.pair_inj.1 equal
  exact Subtype.ext (Prod.ext (injective source) (injective target))

theorem mainTransitionIndex_range {I : Type v} [Small.{u} I] [Preorder I]
    (key : I → ZFSet.{u})
    (order : ∀ i j, i ≤ j ↔ key i = key j ∨ key i ∈ key j) :
    ZFSet.range (mainTransitionIndexKey key) = chronologyPairs (ZFSet.range key) := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨p, rfl⟩ := ZFSet.mem_range.1 hz
    exact (pair_mem_chronologyPairs _ _ _).2
      ⟨ZFSet.mem_range.2 ⟨p.val.2, rfl⟩, ZFSet.mem_range.2 ⟨p.val.1, rfl⟩,
        (order _ _).1 p.property⟩
  · intro hz
    obtain ⟨target, ht, source, hs, rfl, before⟩ := (mem_chronologyPairs _ z).1 hz
    obtain ⟨j, rfl⟩ := ZFSet.mem_range.1 ht
    obtain ⟨i, rfl⟩ := ZFSet.mem_range.1 hs
    exact ZFSet.mem_range.2 ⟨⟨(i, j), (order i j).2 before⟩, rfl⟩

def finiteMainIndexKey {n : Nat} (i : Fin n) : ZFSet.{u} := natSetCode i.val

theorem finiteMainIndexKey_injective (n : Nat) :
    Function.Injective (@finiteMainIndexKey.{u} n) :=
  fun _ _ equal => Fin.ext (natSetCode_injective equal)

theorem finiteMainIndexKey_order {n : Nat} (i j : Fin n) :
    i ≤ j ↔ finiteMainIndexKey i = finiteMainIndexKey j ∨ finiteMainIndexKey i ∈ finiteMainIndexKey j := by
  change i.val ≤ j.val ↔ natSetCode i.val = natSetCode j.val ∨ natSetCode i.val ∈ natSetCode j.val
  rw [natSetCode_injective.eq_iff, natSetCode_mem_iff]
  omega

theorem finiteMainIndexKey_range (n : Nat) :
    ZFSet.range (@finiteMainIndexKey.{u} n) = natSetCode n := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range, mem_natSetCode]
  exact ⟨fun ⟨i, hi⟩ => ⟨i.val, i.isLt, hi.symm⟩,
    fun ⟨i, hi, equal⟩ => ⟨⟨i, hi⟩, equal.symm⟩⟩

theorem finiteMainTransitionIndex_range (n : Nat) :
    ZFSet.range (mainTransitionIndexKey (@finiteMainIndexKey.{u} n)) =
      chronologyPairs (natSetCode n) := by
  exact (mainTransitionIndex_range (@finiteMainIndexKey.{u} n)
    (fun i j => finiteMainIndexKey_order i j)).trans
      (congrArg chronologyPairs (finiteMainIndexKey_range n))

end PartitionPilot.Forcing

namespace PartitionPilot.Forcing
open SetRealization
universe u

@[instance_reducible]
noncomputable def ordinalMainIndexPreorder {T : ZFSet.{u}} (ordinal : ordinalSetProperty T) :
    Preorder (SetMembers T) where
  le i j := SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j
  le_refl _ := Or.inl rfl
  le_trans i j k first second := by
    rcases first with equal | earlier
    · exact equal.symm ▸ second
    · rcases second with equal | later
      · exact Or.inr (equal ▸ earlier)
      · exact Or.inr (ordinal.2 (SetMembers.raw k) (SetMembers.raw_mem k)
          (SetMembers.raw j) later (SetMembers.raw i) earlier)

theorem ordinalMainIndex_le_iff {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    @LE.le _ (ordinalMainIndexPreorder ordinal).toLE i j ↔
      SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j := Iff.rfl

theorem ordinalMainIndex_key_range (T : ZFSet.{u}) :
    ZFSet.range (@SetMembers.raw T) = T := by
  apply ZFSet.ext
  intro z
  rw [ZFSet.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact SetMembers.raw_mem i
  · intro hz
    exact ⟨SetMembers.ofMem z hz, SetMembers.raw_ofMem z hz⟩

theorem ordinalMainTransitionIndex_range {T : ZFSet.{u}} (ordinal : ordinalSetProperty T) :
    letI := ordinalMainIndexPreorder ordinal
    ZFSet.range (mainTransitionIndexKey (@SetMembers.raw T)) = chronologyPairs T := by
  let := ordinalMainIndexPreorder ordinal
  exact (mainTransitionIndex_range (@SetMembers.raw T)
    (fun i j => ordinalMainIndex_le_iff ordinal i j)).trans
      (congrArg chronologyPairs (ordinalMainIndex_key_range T))

theorem ordinalMainIndex_rank_le_iff {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    ZFSet.rank (SetMembers.raw i) ≤ ZFSet.rank (SetMembers.raw j) ↔
      SetMembers.raw i = SetMembers.raw j ∨ SetMembers.raw i ∈ SetMembers.raw j := by
  have hi := ordinalSetProperty_eq_code_rank (SetMembers.raw i)
    (ordinalSetProperty_member ordinal (SetMembers.raw_mem i))
  have hj := ordinalSetProperty_eq_code_rank (SetMembers.raw j)
    (ordinalSetProperty_member ordinal (SetMembers.raw_mem j))
  constructor
  · intro before
    rcases lt_or_eq_of_le before with earlier | equal
    · exact Or.inr (by rw [hi, hj]; exact (mem_ordinalCode_iff _ _).2 earlier)
    · exact Or.inl (hi.trans ((congrArg ordinalCode equal).trans hj.symm))
  · rintro (equal | earlier)
    · exact le_of_eq (congrArg ZFSet.rank equal)
    · exact le_of_lt (ZFSet.rank_lt_of_mem earlier)

theorem ordinalMainIndex_total {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    letI := ordinalMainIndexPreorder ordinal
    i ≤ j ∨ j ≤ i := by
  let := ordinalMainIndexPreorder ordinal
  rcases le_total (ZFSet.rank (SetMembers.raw i)) (ZFSet.rank (SetMembers.raw j)) with first | second
  · exact Or.inl ((ordinalMainIndex_rank_le_iff ordinal i j).1 first)
  · exact Or.inr ((ordinalMainIndex_rank_le_iff ordinal j i).1 second)

theorem ordinalMainIndex_antisymm {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    letI := ordinalMainIndexPreorder ordinal
    i ≤ j → j ≤ i → i = j := by
  let := ordinalMainIndexPreorder ordinal
  intro first second
  apply SetMembers.raw_injective T
  rcases first with equal | earlier
  · exact equal
  · rcases second with equal | later
    · exact equal.symm
    · exact False.elim ((lt_irrefl (ZFSet.rank (SetMembers.raw i)))
        ((ZFSet.rank_lt_of_mem earlier).trans (ZFSet.rank_lt_of_mem later)))

theorem ordinalMainIndex_common_upper {T : ZFSet.{u}} (ordinal : ordinalSetProperty T)
    (i j : SetMembers T) :
    letI := ordinalMainIndexPreorder ordinal
    ∃ k : SetMembers T, i ≤ k ∧ j ≤ k := by
  let := ordinalMainIndexPreorder ordinal
  rcases ordinalMainIndex_total ordinal i j with before | after
  · exact ⟨j, before, le_refl j⟩
  · exact ⟨i, le_refl i, after⟩

def NonzeroLimitOrdinalCode (T : ZFSet.{u}) : Prop :=
  T ≠ ∅ ∧ ∀ b ∈ T, ∃ c ∈ T, b ∈ c

theorem not_nonzeroLimitOrdinalCode_successor (b : ZFSet.{u}) :
    ¬ NonzeroLimitOrdinalCode (insert b b) := by
  intro limit
  obtain ⟨c, member, later⟩ := limit.2 b (ZFSet.mem_insert b b)
  rcases ZFSet.mem_insert_iff.1 member with equal | earlier
  · subst c
    exact (lt_irrefl (ZFSet.rank b)) (ZFSet.rank_lt_of_mem later)
  · exact (lt_irrefl (ZFSet.rank b))
      ((ZFSet.rank_lt_of_mem later).trans (ZFSet.rank_lt_of_mem earlier))

theorem ordinal_successor_or_nonzeroLimit {T : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (nonempty : T ≠ ∅) :
    (∃ b ∈ T, T = insert b b) ∨ NonzeroLimitOrdinalCode T := by
  classical
  by_cases further : ∀ b ∈ T, ∃ c ∈ T, b ∈ c
  · exact Or.inr ⟨nonempty, further⟩
  · push Not at further
    obtain ⟨b, member, maximal⟩ := further
    refine Or.inl ⟨b, member, ?_⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hx
      have comparison := ordinalMainIndex_total ordinal
        (SetMembers.ofMem x hx) (SetMembers.ofMem b member)
      simp only [ordinalMainIndex_le_iff, SetMembers.raw_ofMem] at comparison
      rcases comparison with before | after
      · exact before
      · rcases after with equal | later
        · exact Or.inl equal.symm
        · exact False.elim (maximal x hx later)
    · rintro (equal | earlier)
      · exact equal.symm ▸ member
      · exact ordinal.1 b member x earlier

theorem nonzeroLimitOrdinalCode_iff_not_successor {T : ZFSet.{u}}
    (ordinal : ordinalSetProperty T) (nonempty : T ≠ ∅) :
    NonzeroLimitOrdinalCode T ↔ ¬ ∃ b, T = insert b b := by
  constructor
  · rintro limit ⟨b, rfl⟩
    exact not_nonzeroLimitOrdinalCode_successor b limit
  · intro noSuccessor
    rcases ordinal_successor_or_nonzeroLimit ordinal nonempty with successor | limit
    · obtain ⟨b, _, equal⟩ := successor
      exact False.elim (noSuccessor ⟨b, equal⟩)
    · exact limit

end PartitionPilot.Forcing

end OAI
