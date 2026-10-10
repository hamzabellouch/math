import OAI.SetTheory.PartitionPrinciple.Transfinite.HeightTower

namespace OAI

section

namespace PartitionPilot.Compression.RecursiveMaps

universe u v w

structure LinearHeightOrder (A : Type u) extends HeightOrder A where
  compare : ∀ x y, lt x y ∨ x = y ∨ lt y x

structure DenseHeightOrder (A : Type u) extends LinearHeightOrder A where
  between : ∀ x y, lt x y → ∃ z, lt x z ∧ lt z y

namespace LinearHeightOrder

variable {A : Type u} (R : LinearHeightOrder A)

theorem asymm {x y : A} (h : R.lt x y) : ¬ R.lt y x :=
  fun h' => R.irrefl x (R.trans h h')

theorem weak_refl (x : A) : R.Weak x x := Or.inl rfl

theorem weak_trans {x y z : A} (h : R.Weak x y) (h' : R.Weak y z) : R.Weak x z := by
  rcases h with rfl | h
  · exact h'
  · exact Or.inr (R.lt_weak h h')

theorem list_max (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak a m ∧ ∀ x ∈ xs, R.Weak x m := by
  induction xs with
  | nil => exact ⟨a, Or.inl rfl, R.weak_refl a, by simp⟩
  | cons x xs ih =>
    rcases ih with ⟨m, hm, ha, hx⟩
    rcases R.compare x m with h | eq | h
    · refine ⟨m, ?_, ha, ?_⟩
      · rcases hm with hm | hm
        · exact Or.inl hm
        · exact Or.inr (List.mem_cons_of_mem x hm)
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inr h
        · exact hx y hy
    · refine ⟨m, ?_, ha, ?_⟩
      · exact Or.inr (List.mem_cons.mpr (Or.inl eq.symm))
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Or.inl eq
        · exact hx y hy
    · refine ⟨x, Or.inr (List.mem_cons_self), R.weak_trans ha (Or.inr h), ?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact R.weak_refl _
      · exact R.weak_trans (hx y hy) (Or.inr h)

def reverse : LinearHeightOrder A where
  lt x y := R.lt y x
  irrefl := R.irrefl
  trans h h' := R.trans h' h
  compare x y := by
    rcases R.compare y x with h | eq | h
    · exact Or.inl h
    · exact Or.inr (Or.inl eq.symm)
    · exact Or.inr (Or.inr h)

theorem list_min (a : A) (xs : List A) :
    ∃ m, (m = a ∨ m ∈ xs) ∧ R.Weak m a ∧ ∀ x ∈ xs, R.Weak m x := by
  rcases R.reverse.list_max a xs with ⟨m, hm, ha, hx⟩
  refine ⟨m, hm, ?_, ?_⟩
  · rcases ha with eq | h
    · exact Or.inl eq.symm
    · exact Or.inr h
  · intro x h
    rcases hx x h with eq | h'
    · exact Or.inl eq.symm
    · exact Or.inr h'

end LinearHeightOrder

namespace DenseHeightOrder

variable {D : Type v} (R : DenseHeightOrder D)

theorem finite_gap (lo hi : D) (lower upper : List D)
    (gap : R.lt lo hi)
    (lower_hi : ∀ x ∈ lower, R.lt x hi)
    (lo_upper : ∀ y ∈ upper, R.lt lo y)
    (separated : ∀ x ∈ lower, ∀ y ∈ upper, R.lt x y) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ x ∈ lower, R.lt x z) ∧ (∀ y ∈ upper, R.lt z y) := by
  rcases R.toLinearHeightOrder.list_max lo lower with ⟨a, ha, hlo, hlow⟩
  rcases R.toLinearHeightOrder.list_min hi upper with ⟨b, hb, hhi, hupp⟩
  have ab : R.lt a b := by
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · exact gap
      · exact lo_upper b hb
    · rcases hb with rfl | hb
      · exact lower_hi a ha
      · exact separated a ha b hb
  rcases R.between a b ab with ⟨z, az, zb⟩
  exact ⟨z, R.weak_lt hlo az, R.lt_weak zb hhi,
    fun x hx => R.weak_lt (hlow x hx) az,
    fun y hy => R.lt_weak zb (hupp y hy)⟩

end DenseHeightOrder

namespace CountableInterpolation

variable {A : Type u} {D : Type v} (S : LinearHeightOrder A)
    (R : DenseHeightOrder D) (enumerate : Nat → A) (lo hi : D)

structure Partial (n : Nat) where
  value : Nat → D
  lower : ∀ i, i < n → R.lt lo (value i)
  upper : ∀ i, i < n → R.lt (value i) hi
  strict : ∀ i j, i < n → j < n → S.lt (enumerate i) (enumerate j) → R.lt (value i) (value j)
  equal : ∀ i j, i < n → j < n → enumerate i = enumerate j → value i = value j

variable {S R enumerate lo hi}

theorem next_exists {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) :
    ∃ z, R.lt lo z ∧ R.lt z hi ∧
      (∀ i, i < n → S.lt (enumerate i) (enumerate n) → R.lt (p.value i) z) ∧
      (∀ i, i < n → S.lt (enumerate n) (enumerate i) → R.lt z (p.value i)) ∧
      (∀ i, i < n → enumerate i = enumerate n → p.value i = z) := by
  classical
  by_cases seen : ∃ i, i < n ∧ enumerate i = enumerate n
  · rcases seen with ⟨j, hj, he⟩
    refine ⟨p.value j, p.lower j hj, p.upper j hj, ?_, ?_, ?_⟩
    · intro i h h'
      exact p.strict i j h hj (he ▸ h')
    · intro i h h'
      exact p.strict j i hj h (he ▸ h')
    · intro i h h'
      exact p.equal i j h hj (h'.trans he.symm)
  · let lowers := ((List.range n).filter (fun i => S.lt (enumerate i) (enumerate n))).map p.value
    let uppers := ((List.range n).filter (fun i => S.lt (enumerate n) (enumerate i))).map p.value
    have lower_spec : ∀ x, x ∈ lowers ↔ ∃ i, i < n ∧ S.lt (enumerate i) (enumerate n) ∧ p.value i = x := by
      intro x
      simp only [lowers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have upper_spec : ∀ x, x ∈ uppers ↔ ∃ i, i < n ∧ S.lt (enumerate n) (enumerate i) ∧ p.value i = x := by
      intro x
      simp only [uppers, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
      constructor
      · rintro ⟨i, ⟨h, h'⟩, eq⟩
        exact ⟨i, h, h', eq⟩
      · rintro ⟨i, h, h', eq⟩
        exact ⟨i, ⟨h, h'⟩, eq⟩
    have lh : ∀ x ∈ lowers, R.lt x hi := by
      intro x hx
      rcases (lower_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.upper i h
    have lu : ∀ x ∈ uppers, R.lt lo x := by
      intro x hx
      rcases (upper_spec x).mp hx with ⟨i, h, _, rfl⟩
      exact p.lower i h
    have sep : ∀ x ∈ lowers, ∀ y ∈ uppers, R.lt x y := by
      intro x hx y hy
      rcases (lower_spec x).mp hx with ⟨i, h, h', rfl⟩
      rcases (upper_spec y).mp hy with ⟨j, k, k', rfl⟩
      exact p.strict i j h k (S.trans h' k')
    rcases R.finite_gap lo hi lowers uppers gap lh lu sep with ⟨z, hz, zh, hl, hu⟩
    refine ⟨z, hz, zh, ?_, ?_, ?_⟩
    · intro i h h'
      exact hl _ ((lower_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h h'
      exact hu _ ((upper_spec _).mpr ⟨i, h, h', rfl⟩)
    · intro i h eq
      exact False.elim (seen ⟨i, h, eq⟩)

noncomputable def nextPoint {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) : D :=
  Classical.choose (next_exists p gap)

theorem nextPoint_spec {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) :
    R.lt lo (nextPoint p gap) ∧ R.lt (nextPoint p gap) hi ∧
      (∀ i, i < n → S.lt (enumerate i) (enumerate n) → R.lt (p.value i) (nextPoint p gap)) ∧
      (∀ i, i < n → S.lt (enumerate n) (enumerate i) → R.lt (nextPoint p gap) (p.value i)) ∧
      (∀ i, i < n → enumerate i = enumerate n → p.value i = nextPoint p gap) :=
  Classical.choose_spec (next_exists p gap)

noncomputable def extend {n : Nat} (p : Partial S R enumerate lo hi n) (gap : R.lt lo hi) :
    Partial S R enumerate lo hi (n + 1) where
  value i := if i < n then p.value i else nextPoint p gap
  lower i _ := by
    split
    · exact p.lower i ‹i < n›
    · exact (nextPoint_spec p gap).1
  upper i _ := by
    split
    · exact p.upper i ‹i < n›
    · exact (nextPoint_spec p gap).2.1
  strict i j h k lt := by
    split <;> split
    · exact p.strict i j ‹i < n› ‹j < n› lt
    · have eq : j = n := by omega
      subst j
      exact (nextPoint_spec p gap).2.2.1 i ‹i < n› lt
    · have eq : i = n := by omega
      subst i
      exact (nextPoint_spec p gap).2.2.2.1 j ‹j < n› lt
    · have ei : i = n := by omega
      have ej : j = n := by omega
      subst i
      subst j
      exact False.elim (S.irrefl _ lt)
  equal i j h k eq := by
    split <;> split
    · exact p.equal i j ‹i < n› ‹j < n› eq
    · have ej : j = n := by omega
      subst j
      exact (nextPoint_spec p gap).2.2.2.2 i ‹i < n› eq
    · have ei : i = n := by omega
      subst i
      exact ((nextPoint_spec p gap).2.2.2.2 j ‹j < n› eq.symm).symm
    · rfl

noncomputable def stages (gap : R.lt lo hi) : (n : Nat) → Partial S R enumerate lo hi n
  | 0 => {
      value := fun _ => lo
      lower := fun _ h => False.elim (Nat.not_lt_zero _ h)
      upper := fun _ h => False.elim (Nat.not_lt_zero _ h)
      strict := fun _ _ h _ _ => False.elim (Nat.not_lt_zero _ h)
      equal := fun _ _ h _ _ => False.elim (Nat.not_lt_zero _ h) }
  | n + 1 => extend (stages gap n) gap

theorem stages_step (gap : R.lt lo hi) (n i : Nat) (h : i < n) :
    (stages (S := S) (enumerate := enumerate) gap (n + 1)).value i =
      (stages (S := S) (enumerate := enumerate) gap n).value i := by
  exact ite_eq_left h

noncomputable def value (gap : R.lt lo hi) (i : Nat) : D :=
  (stages (S := S) (enumerate := enumerate) gap (i + 1)).value i

theorem restriction (gap : R.lt lo hi) (n i : Nat) (h : i < n) :
    (stages (S := S) (enumerate := enumerate) gap n).value i =
      value (S := S) (enumerate := enumerate) gap i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases eq : i = n
    · subst i
      rfl
    · have hn : i < n := by omega
      exact (stages_step (S := S) (enumerate := enumerate) gap n i hn).trans (ih hn)

theorem value_lower (gap : R.lt lo hi) (i : Nat) :
    R.lt lo (value (S := S) (enumerate := enumerate) gap i) :=
  (stages gap (i + 1)).lower i (Nat.lt_succ_self i)

theorem value_upper (gap : R.lt lo hi) (i : Nat) :
    R.lt (value (S := S) (enumerate := enumerate) gap i) hi :=
  (stages gap (i + 1)).upper i (Nat.lt_succ_self i)

theorem value_strict (gap : R.lt lo hi) (i j : Nat) (lt : S.lt (enumerate i) (enumerate j)) :
    R.lt (value (S := S) (enumerate := enumerate) gap i)
      (value (S := S) (enumerate := enumerate) gap j) := by
  have hi : i < i + j + 1 := by omega
  have hj : j < i + j + 1 := by omega
  have h := (stages gap (i + j + 1)).strict i j hi hj lt
  rw [restriction gap _ i hi, restriction gap _ j hj] at h
  exact h

theorem value_equal (gap : R.lt lo hi) (i j : Nat) (eq : enumerate i = enumerate j) :
    value (S := S) (enumerate := enumerate) gap i =
      value (S := S) (enumerate := enumerate) gap j := by
  have hi : i < i + j + 1 := by omega
  have hj : j < i + j + 1 := by omega
  have h := (stages (S := S) gap (i + j + 1)).equal i j hi hj eq
  rw [restriction gap _ i hi, restriction gap _ j hj] at h
  exact h

end CountableInterpolation

theorem countable_range_interpolation {X : Type u} {H : Type v} {D : Type w}
    (S : LinearHeightOrder H) (R : DenseHeightOrder D) (height : X → H)
    (base : X) (countable : CountableRange height) (lo hi : D) (gap : R.lt lo hi) :
    ∃ assign : X → D, (∀ x, R.lt lo (assign x) ∧ R.lt (assign x) hi) ∧
      (∀ x y, S.lt (height x) (height y) → R.lt (assign x) (assign y)) ∧
      (∀ x y, height x = height y → assign x = assign y) := by
  classical
  rcases countable with ⟨code, code_equal⟩
  let enumerate : Nat → H := fun n =>
    if h : ∃ x, code x = n then height (Classical.choose h) else height base
  have cover : ∀ x, enumerate (code x) = height x := by
    intro x
    have h : ∃ y, code y = code x := ⟨x, rfl⟩
    dsimp [enumerate]
    rw [dite_eq_left h]
    exact code_equal _ x (Classical.choose_spec h)
  refine ⟨fun x => CountableInterpolation.value (S := S) (enumerate := enumerate) gap (code x), ?_, ?_, ?_⟩
  · intro x
    exact ⟨CountableInterpolation.value_lower gap _, CountableInterpolation.value_upper gap _⟩
  · intro x y lt
    apply CountableInterpolation.value_strict
    rw [cover, cover]
    exact lt
  · intro x y eq
    apply CountableInterpolation.value_equal
    rw [cover, cover]
    exact eq

end PartitionPilot.Compression.RecursiveMaps

end

end OAI
