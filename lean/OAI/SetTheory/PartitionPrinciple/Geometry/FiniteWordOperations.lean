import OAI.SetTheory.PartitionPrinciple.Definability.DepthSlotCodes
import OAI.SetTheory.PartitionPrinciple.Definability.FiniteWordMapCodes

namespace OAI


namespace PartitionPilot.Forcing
open SetRealization
universe u

def FiniteWordAppendCode (A omega add f g h : ZFSet.{u}) : Prop :=
  ∃ m ∈ omega, ∃ n ∈ omega, ∃ p ∈ omega,
    ZFSet.IsFunc m A f ∧ ZFSet.IsFunc n A g ∧ ZFSet.IsFunc p A h ∧
      ZFSet.pair (ZFSet.pair m n) p ∈ add ∧
      ∀ i ∈ p, ∀ a ∈ A, ZFSet.pair i a ∈ h ↔
        ZFSet.pair i a ∈ f ∨ ∃ j ∈ n,
          ZFSet.pair (ZFSet.pair m j) i ∈ add ∧ ZFSet.pair j a ∈ g

def FiniteWordReverseCode (A omega add f h : ZFSet.{u}) : Prop :=
  ∃ n ∈ omega, ZFSet.IsFunc n A f ∧ ZFSet.IsFunc n A h ∧
    ∀ i ∈ n, ∀ a ∈ A, ZFSet.pair i a ∈ h ↔
      ∃ j ∈ n, ∃ k ∈ n, ZFSet.pair (ZFSet.pair i j) k ∈ add ∧
        n = insert k k ∧ ZFSet.pair j a ∈ f

theorem finiteWordGraph_append_entry {B : Type u} (s : Presentation B)
    (xs ys : List B) (k : Nat) (a : ZFSet.{u}) :
    ZFSet.pair (natSetCode k) a ∈ finiteWordGraph s (xs ++ ys) ↔
      ZFSet.pair (natSetCode k) a ∈ finiteWordGraph s xs ∨
        ∃ j, k = xs.length + j ∧ ZFSet.pair (natSetCode j) a ∈ finiteWordGraph s ys := by
  constructor
  · intro entry
    obtain ⟨hk, value⟩ := (pair_mem_finiteWordGraph s (xs ++ ys) k a).1 entry
    by_cases left : k < xs.length
    · apply Or.inl
      apply (pair_mem_finiteWordGraph s xs k a).2
      refine ⟨left, ?_⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left left] using value
    · have right : xs.length ≤ k := Nat.le_of_not_gt left
      have hj : k - xs.length < ys.length := by simp only [List.length_append] at hk; omega
      refine Or.inr ⟨k - xs.length, by omega, (pair_mem_finiteWordGraph s ys _ a).2 ⟨hj, ?_⟩⟩
      simpa only [List.get_eq_getElem, List.getElem_append_right right] using value
  · rintro (entry | ⟨j, equal, entry⟩)
    · obtain ⟨hk, value⟩ := (pair_mem_finiteWordGraph s xs k a).1 entry
      apply (pair_mem_finiteWordGraph s (xs ++ ys) k a).2
      have bound : k < (xs ++ ys).length := by simp only [List.length_append]; omega
      refine ⟨bound, ?_⟩
      simpa only [List.get_eq_getElem, List.getElem_append_left hk] using value
    · subst k
      obtain ⟨hj, value⟩ := (pair_mem_finiteWordGraph s ys j a).1 entry
      apply (pair_mem_finiteWordGraph s (xs ++ ys) (xs.length + j) a).2
      have bound : xs.length + j < (xs ++ ys).length := by simp only [List.length_append]; omega
      refine ⟨bound, ?_⟩
      simpa only [List.get_eq_getElem,
        List.getElem_append_right (Nat.le_add_right xs.length j), Nat.add_sub_cancel_left] using value

theorem finiteWordGraph_reverse_entry {B : Type u} (s : Presentation B)
    (xs : List B) (i : Nat) (a : ZFSet.{u}) :
    ZFSet.pair (natSetCode i) a ∈ finiteWordGraph s xs.reverse ↔
      ∃ j, i + j + 1 = xs.length ∧ ZFSet.pair (natSetCode j) a ∈ finiteWordGraph s xs := by
  constructor
  · intro entry
    obtain ⟨hi, value⟩ := (pair_mem_finiteWordGraph s xs.reverse i a).1 entry
    have bound : i < xs.length := by simpa only [List.length_reverse] using hi
    have hj : xs.length - 1 - i < xs.length := by omega
    refine ⟨xs.length - 1 - i, by omega, (pair_mem_finiteWordGraph s xs _ a).2 ⟨hj, ?_⟩⟩
    simpa only [List.get_eq_getElem, List.getElem_reverse] using value
  · rintro ⟨j, sum, entry⟩
    obtain ⟨hj, value⟩ := (pair_mem_finiteWordGraph s xs j a).1 entry
    have hi : i < xs.reverse.length := by simp only [List.length_reverse]; omega
    have equal : xs.length - 1 - i = j := by omega
    apply (pair_mem_finiteWordGraph s xs.reverse i a).2
    refine ⟨hi, ?_⟩
    simpa only [List.get_eq_getElem, List.getElem_reverse, equal] using value

theorem finiteWordGraph_append_code {B : Type u} (s : Presentation B) (xs ys : List B) :
    FiniteWordAppendCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s ys) (finiteWordGraph s (xs ++ ys)) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, natSetCode ys.length, natSetCode_mem_omega _,
    natSetCode (xs.length + ys.length), natSetCode_mem_omega _, finiteWordGraph_function s xs,
    finiteWordGraph_function s ys, ?_, (pair_mem_natAddGraph _ _ _).2 rfl, ?_⟩
  · simpa only [List.length_append] using finiteWordGraph_function s (xs ++ ys)
  · intro i hi a _
    obtain ⟨k, _, rfl⟩ := (mem_natSetCode i (xs.length + ys.length)).1 hi
    rw [finiteWordGraph_append_entry]
    apply or_congr Iff.rfl
    constructor
    · rintro ⟨j, equal, entry⟩
      have hj := (ZFSet.pair_mem_prod.1 ((finiteWordGraph_function s ys).1 entry)).1
      exact ⟨natSetCode j, hj, (pair_mem_natAddGraph _ _ _).2 equal, entry⟩
    · rintro ⟨j, hj, sum, entry⟩
      obtain ⟨l, _, rfl⟩ := (mem_natSetCode j ys.length).1 hj
      exact ⟨l, (pair_mem_natAddGraph _ _ _).1 sum, entry⟩

theorem finiteWordGraph_reverse_code {B : Type u} (s : Presentation B) (xs : List B) :
    FiniteWordReverseCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s xs.reverse) := by
  refine ⟨natSetCode xs.length, natSetCode_mem_omega _, finiteWordGraph_function s xs, ?_, ?_⟩
  · simpa only [List.length_reverse] using finiteWordGraph_function s xs.reverse
  · intro i hi a _
    obtain ⟨k, _, rfl⟩ := (mem_natSetCode i xs.length).1 hi
    rw [finiteWordGraph_reverse_entry]
    constructor
    · rintro ⟨j, sum, entry⟩
      have hj := (ZFSet.pair_mem_prod.1 ((finiteWordGraph_function s xs).1 entry)).1
      refine ⟨natSetCode j, hj, natSetCode (k + j), (natSetCode_mem_iff _ _).2 (by omega),
        (pair_mem_natAddGraph _ _ _).2 rfl, ?_, entry⟩
      exact (congrArg natSetCode sum).symm
    · rintro ⟨j, hj, l, hl, sum, successor, entry⟩
      obtain ⟨j, _, rfl⟩ := (mem_natSetCode j xs.length).1 hj
      obtain ⟨l, _, rfl⟩ := (mem_natSetCode l xs.length).1 hl
      have added := (pair_mem_natAddGraph _ _ _).1 sum
      have length : xs.length = l + 1 := natSetCode_injective successor
      exact ⟨j, by omega, entry⟩

theorem FiniteWordAppendCode.unique {A f g h h' : ZFSet.{u}}
    (first : FiniteWordAppendCode A ZFSet.omega natAddGraph f g h)
    (second : FiniteWordAppendCode A ZFSet.omega natAddGraph f g h') : h = h' := by
  obtain ⟨m, hm, n, hn, p, hp, fm, gn, funH, sum, entries⟩ := first
  obtain ⟨m', hm', n', hn', p', hp', fm', gn', funH', sum', entries'⟩ := second
  obtain ⟨m, rfl⟩ := (mem_omega_iff_natSetCode _).1 hm
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode _).1 hn
  obtain ⟨p, rfl⟩ := (mem_omega_iff_natSetCode _).1 hp
  obtain ⟨m', rfl⟩ := (mem_omega_iff_natSetCode _).1 hm'
  obtain ⟨n', rfl⟩ := (mem_omega_iff_natSetCode _).1 hn'
  obtain ⟨p', rfl⟩ := (mem_omega_iff_natSetCode _).1 hp'
  have mEqual := finiteWord_domain_unique fm' fm
  have nEqual := finiteWord_domain_unique gn' gn
  subst m' n'
  have pEqual := ((pair_mem_natAddGraph _ _ _).1 sum').trans ((pair_mem_natAddGraph _ _ _).1 sum).symm
  subst p'
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH.1 hz)
    exact (entries' i hi a ha).2 ((entries i hi a ha).1 hz)
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH'.1 hz)
    exact (entries i hi a ha).2 ((entries' i hi a ha).1 hz)

theorem FiniteWordReverseCode.unique {A f h h' : ZFSet.{u}}
    (first : FiniteWordReverseCode A ZFSet.omega natAddGraph f h)
    (second : FiniteWordReverseCode A ZFSet.omega natAddGraph f h') : h = h' := by
  obtain ⟨n, hn, funF, funH, entries⟩ := first
  obtain ⟨n', hn', funF', funH', entries'⟩ := second
  obtain ⟨n, rfl⟩ := (mem_omega_iff_natSetCode _).1 hn
  obtain ⟨n', rfl⟩ := (mem_omega_iff_natSetCode _).1 hn'
  have same := finiteWord_domain_unique funF' funF
  subst n'
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH.1 hz)
    exact (entries' i hi a ha).2 ((entries i hi a ha).1 hz)
  · intro hz
    obtain ⟨i, hi, a, ha, rfl⟩ := ZFSet.mem_prod.1 (funH'.1 hz)
    exact (entries i hi a ha).2 ((entries' i hi a ha).1 hz)

theorem finiteWordAppendCode_iff {B : Type u} (s : Presentation B) (xs ys : List B) (h : ZFSet.{u}) :
    FiniteWordAppendCode s.carrier ZFSet.omega natAddGraph
      (finiteWordGraph s xs) (finiteWordGraph s ys) h ↔ h = finiteWordGraph s (xs ++ ys) :=
  ⟨fun code => code.unique (finiteWordGraph_append_code s xs ys),
    fun equal => equal.symm ▸ finiteWordGraph_append_code s xs ys⟩

theorem finiteWordReverseCode_iff {B : Type u} (s : Presentation B) (xs : List B) (h : ZFSet.{u}) :
    FiniteWordReverseCode s.carrier ZFSet.omega natAddGraph (finiteWordGraph s xs) h ↔
      h = finiteWordGraph s xs.reverse :=
  ⟨fun code => code.unique (finiteWordGraph_reverse_code s xs),
    fun equal => equal.symm ▸ finiteWordGraph_reverse_code s xs⟩

end PartitionPilot.Forcing

end OAI
