import Mathlib
import OAI.Topology.ArtinGroups.Harmonic.Earlier

namespace OAI

namespace HarmonicArtin
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P I : Type} [PartialOrder P] [Countable I] [Nonempty I]

omit [PartialOrder P] in
lemma directed_cover_sequence (A : I → Set P)
    (hd : ∀ i j, ∃ k, A i ⊆ A k ∧ A j ⊆ A k) :
    ∃ c : ℕ → I, Monotone (fun n => A (c n)) ∧ ∀ i, ∃ n, A i ⊆ A (c n) := by
  obtain ⟨e,he⟩ := exists_surjective_nat I
  let upper : I → I → I := fun i j => (hd i j).choose
  have hu : ∀ i j, A i ⊆ A (upper i j) ∧ A j ⊆ A (upper i j) :=
    fun i j => (hd i j).choose_spec
  let c : ℕ → I := Nat.rec (e 0) (fun n i => upper i (e (n+1)))
  have hc0 : c 0 = e 0 := rfl
  have hcs : ∀ n, c (n+1) = upper (c n) (e (n+1)) := fun _ => rfl
  have hcm : Monotone (fun n => A (c n)) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hcs n]
    exact (hu _ _).1
  refine ⟨c,hcm,?_⟩
  intro i
  obtain ⟨n,rfl⟩ := he i
  refine ⟨n,?_⟩
  cases n with
  | zero => rw [hc0]
  | succ n => rw [hcs n]; exact (hu _ _).2

theorem orderWeights_contractible_of_countable_directed_cover
    (A : I → Set P) (hd : ∀ i j, ∃ k, A i ⊆ A k ∧ A j ⊆ A k)
    (hc : ∀ p, ∃ i, p ∈ A i)
    (hdown : ∀ i {p q}, p ≤ q → q ∈ A i → p ∈ A i)
    (hA : ∀ i, ContractibleSpace (OrderWeights (A i)))
    (k : P → ℕ) (N : ℕ) (hk : ∀ p, k p ≤ N) (hkm : StrictMono k) :
    ContractibleSpace (OrderWeights P) := by
  obtain ⟨c,hcm,hcf⟩ := directed_cover_sequence A hd
  let B : ℕ → Set P := fun n => A (c n)
  have hB : ∀ p, ∃ n, p ∈ B n := by
    intro p
    obtain ⟨i,hi⟩ := hc p
    obtain ⟨n,hn⟩ := hcf i
    exact ⟨n,hn hi⟩
  let f : P →o ℕ := {
    toFun := fun p => Nat.find (hB p)
    monotone' := by
      intro p q hpq
      apply Nat.find_min'
      exact hdown _ hpq (Nat.find_spec (hB q)) }
  have hf : ∀ p n, f p ≤ n ↔ p ∈ B n := by
    intro p n
    constructor
    · intro h
      exact hcm h (Nat.find_spec (hB p))
    · intro h
      exact Nat.find_min' (hB p) h
  apply orderWeights_contractible_of_natural_preimages f k N hk hkm
  intro n
  let e : {p : P // f p ≤ n} ≃o B n := {
    toFun := fun p => ⟨p.val,(hf p.val n).mp p.property⟩
    invFun := fun p => ⟨p.val,(hf p.val n).mpr p.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_rel_iff' := by intros; rfl }
  exact (weightHomeomorph e).contractibleSpace_iff.mpr (hA (c n))

end HarmonicArtin

end OAI
