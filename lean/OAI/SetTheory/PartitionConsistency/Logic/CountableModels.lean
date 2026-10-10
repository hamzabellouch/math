import Mathlib
import OAI.SetTheory.PartitionConsistency.Logic.Proofs
import OAI.SetTheory.PartitionConsistency.Logic.SetLanguage
import OAI.SetTheory.PartitionConsistency.Forcing.ForcingQuotient

namespace OAI

namespace PartitionConsistency
/-! Countable elementary submodels in arbitrary membership structures. -/

namespace CountableModel
open ForcingQuotient

variable {M : Type*} (E : M → M → Prop)

/-- One local existential witness for each formula and parameter tuple. The
selection is external: it makes no choice function in the object structure. -/
noncomputable def witness [Nonempty M] {n}
    (φ : BasicFormula (n + 1)) (v : Fin n → M) : M := by
  classical
  exact if h : ∃ x, BasicFormula.Realize E (Fin.snoc v x) φ then
    Classical.choose h
  else Classical.choice inferInstance

theorem witness_spec [Nonempty M] {n} (φ : BasicFormula (n + 1))
    (v : Fin n → M) (h : ∃ x, BasicFormula.Realize E (Fin.snoc v x) φ) :
    BasicFormula.Realize E (Fin.snoc v (witness E φ v)) φ := by
  classical
  simp only [witness, dite_eq_left h]
  exact Classical.choose_spec h

/-- Close a set once under all formula witnesses with finitely many parameters. -/
noncomputable def step [Nonempty M] (S : Set M) : Set M :=
  S ∪ Set.range (fun i : Σ n, BasicFormula (n + 1) × (Fin n → S) =>
    witness E i.2.1 (Subtype.val ∘ i.2.2))

theorem subset_step [Nonempty M] (S : Set M) : S ⊆ step E S := Set.subset_union_left

theorem step_countable [Nonempty M] {S : Set M} (hS : S.Countable) :
    (step E S).Countable := by
  have : Countable S := hS.to_subtype
  exact hS.union (Set.countable_range _)

/-- Skolem-hull stages, starting from a given nonempty countable set. -/
noncomputable def stage [Nonempty M] (S : Set M) : ℕ → Set M
  | 0 => S
  | n + 1 => step E (stage S n)

/-- The countable union of the finite stages, not closure under arbitrary
external functions. -/
noncomputable def hull [Nonempty M] (S : Set M) : Set M := ⋃ n, stage E S n

theorem stage_mono [Nonempty M] (S : Set M) : Monotone (stage E S) := by
  apply monotone_nat_of_le_succ
  intro n
  exact subset_step E (stage E S n)

theorem stage_countable [Nonempty M] {S : Set M} (hS : S.Countable) (n : ℕ) :
    (stage E S n).Countable := by
  induction n with
  | zero => exact hS
  | succ n ih => exact step_countable E ih

theorem hull_countable [Nonempty M] {S : Set M} (hS : S.Countable) :
    (hull E S).Countable := Set.countable_iUnion (stage_countable E hS)

theorem subset_hull [Nonempty M] (S : Set M) : S ⊆ hull E S := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, hx⟩

/-- Every finite tuple drawn from the hull lies at one stage. -/
theorem tuple_bounded [Nonempty M] {S : Set M} {n : ℕ}
    (v : Fin n → hull E S) :
    ∃ k, ∀ i, (v i).val ∈ stage E S k := by
  classical
  have h : ∀ i, ∃ k, (v i).val ∈ stage E S k :=
    fun i => Set.mem_iUnion.mp (v i).property
  choose k hk using h
  refine ⟨Finset.univ.sup k, fun i => ?_⟩
  exact stage_mono E S (Finset.le_sup (Finset.mem_univ i)) (hk i)

/-- The hull is closed under the chosen witness for each formula. -/
theorem witness_mem_hull [Nonempty M] {S : Set M} {n : ℕ}
    (φ : BasicFormula (n + 1)) (v : Fin n → hull E S) :
    witness E φ (Subtype.val ∘ v) ∈ hull E S := by
  obtain ⟨k, hk⟩ := tuple_bounded E v
  apply Set.mem_iUnion.mpr
  refine ⟨k + 1, Or.inr ?_⟩
  exact ⟨⟨n, φ, fun i => ⟨(v i).val, hk i⟩⟩, rfl⟩

/-- Tarski–Vaught condition for a subdomain, stated for the formula basis. -/
def HasWitnesses (S : Set M) : Prop :=
  ∀ n (φ : BasicFormula (n + 1)) (v : Fin n → S),
    (∃ x, BasicFormula.Realize E (Fin.snoc (Subtype.val ∘ v) x) φ) →
      ∃ x : S, BasicFormula.Realize E (Fin.snoc (Subtype.val ∘ v) x.val) φ

theorem hull_hasWitnesses [Nonempty M] (S : Set M) : HasWitnesses E (hull E S) := by
  intro n φ v hex
  exact ⟨⟨witness E φ (Subtype.val ∘ v), witness_mem_hull E φ v⟩,
    witness_spec E φ (Subtype.val ∘ v) hex⟩

/-- Formula truth is preserved and reflected in any subdomain satisfying the
Tarski–Vaught condition. Nothing requires external well-foundedness. -/
theorem basic_elementary {S : Set M} (hS : HasWitnesses E S)
    {n} (φ : BasicFormula n) (v : Fin n → S) :
    BasicFormula.Realize (fun x y : S => E x.val y.val) v φ ↔
      BasicFormula.Realize E (Subtype.val ∘ v) φ := by
  induction φ with
  | bot => rfl
  | mem => rfl
  | equal x y => exact Subtype.ext_iff
  | conj φ ψ hφ hψ =>
      exact and_congr (hφ v) (hψ v)
  | neg φ hφ => exact not_congr (hφ v)
  | ex φ hφ =>
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x.val, ?_⟩
        have h := (hφ (Fin.snoc v x)).1 hx
        rwa [Fin.comp_snoc] at h
      · intro hex
        obtain ⟨x, hx⟩ := hS _ φ v hex
        refine ⟨x, (hφ (Fin.snoc v x)).2 ?_⟩
        rwa [Fin.comp_snoc]

/-- Elementarity for the full language used in `ZF` and the target theory. -/
theorem elementary {S : Set M} (hS : HasWitnesses E S)
    {n} (φ : Formula n) (v : Fin n → S) :
    Formula.Realize (fun x y : S => E x.val y.val) v φ ↔
      Formula.Realize E (Subtype.val ∘ v) φ := by
  rw [← Formula.realize_toBasic, ← Formula.realize_toBasic]
  exact basic_elementary E hS φ.toBasic v

/-- Downward Löwenheim–Skolem for this countable membership language, with
parameters: a countable subset of a nonempty structure extends to a nonempty
countable elementary subdomain of that same structure. -/
theorem exists_countable_elementary [Nonempty M] {S : Set M} (hS : S.Countable) :
    ∃ N : Set M, S ⊆ N ∧ N.Nonempty ∧ N.Countable ∧
      ∀ n (φ : Formula n) (v : Fin n → N),
        Formula.Realize (fun x y : N => E x.val y.val) v φ ↔
          Formula.Realize E (Subtype.val ∘ v) φ := by
  let x₀ : M := Classical.choice inferInstance
  let N := hull E (insert x₀ S)
  refine ⟨N, ?_, ?_, hull_countable E (hS.insert x₀), ?_⟩
  · exact Set.Subset.trans (Set.subset_insert _ _) (subset_hull E _)
  · exact ⟨x₀, subset_hull E _ (Set.mem_insert _ _)⟩
  · intro n φ v
    exact elementary E (hull_hasWitnesses E _) φ v

/-- Every nonempty relational model of any theory in the target language has a
nonempty countable submodel. This is only the downward Löwenheim–Skolem step:
it does not prove completeness or construct a model from syntactic consistency. -/
theorem exists_countable_model [Nonempty M] {T : Theory} (hT : Models E T) :
    ∃ N : Set M, N.Nonempty ∧ N.Countable ∧
      Models (fun x y : N => E x.val y.val) T := by
  obtain ⟨N, _, hN, hct, hel⟩ := exists_countable_elementary E Set.countable_empty
  refine ⟨N, hN, hct, ?_⟩
  intro φ hφ
  apply (hel 0 φ Fin.elim0).2
  have hv : (Subtype.val : N → M) ∘ Fin.elim0 = (Fin.elim0 : Fin 0 → M) :=
    Subsingleton.elim _ _
  rw [hv]
  exact hT φ hφ

end CountableModel
end PartitionConsistency

end OAI
