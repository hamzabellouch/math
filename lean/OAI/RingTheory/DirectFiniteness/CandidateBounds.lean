import OAI.RingTheory.DirectFiniteness.CandidateDependencies

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.FiniteGeometry
variable {Q : Type u_1} {A : Type u_2} {R : Type u_3} {E : Type u_4} [Field Q] [AddCommGroup A] [Module Q A]
  [AddCommGroup E] [Module Q E] [Fintype A] [Fintype Q] [Fintype R] [Fintype E]
namespace Candidate
variable (F : DirectionFrame Q A R E) (T : R → Finset A) (k : ℕ)
variable (j : R × Q) (C : AffineCoset (F.U j))

def TwoCode.equiv : TwoCode F k j C ≃
    ((R × Q) × (Fin 4 → Fin k) × (Fin k → Fin 3) × C.val × (Q × E) × (Q × E) × (Fin k → Q)) where
  toFun c := (c.other,c.idx,c.tag,c.point,c.vec0,c.vec1,c.exc)
  invFun c := ⟨c.1,c.2.1,c.2.2.1,c.2.2.2.1,c.2.2.2.2.1,c.2.2.2.2.2.1,c.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma twoCode_card : Fintype.card (TwoCode F k j C) =
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k := by
  rw [Fintype.card_congr (TwoCode.equiv F k j C)]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe]
  ring

omit [Fintype E] in
lemma oneCode_card_le (M : ℕ) (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card (OneCode F T k j C) ≤ Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k := by
  change Fintype.card (Σ r : R, (Fin 2 → Fin k) × (Fin k → Bool) ×
    ↥(C.val ∩ T r) × ↥(C.val ∩ T r) × (Fin k → Q)) ≤ _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe]
  calc
    _ ≤ ∑ _r : R, k^2 * (2^k * (M * (M * Fintype.card Q^k))) := by
      apply Finset.sum_le_sum
      intro r _
      gcongr <;> exact hM r
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul]; ring

lemma two_rooted_card_le (hk : k ≤ 5) :
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=2} ≤
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k := by
  rw [← twoCode_card F k j C]
  apply card_le_of_unique_cover (fun c z => CoveredTwo F T k j C c.val z)
  · intro c; exact two_label_codec F T k j C c.val hk c.property
  · intro c d z hc hd
    exact Subtype.ext (CoveredTwo.unique F T k j C hc hd)

lemma one_rooted_card_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=1} ≤
    Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k := by
  apply le_trans (b := Fintype.card (OneCode F T k j C))
  · apply card_le_of_unique_cover (fun c z => CoveredOne F T k j C c.val z)
    · intro c; exact (one_label_codec F T k j C c.val hk3 hk5 c.property).2
    · intro c d z hc hd; exact Subtype.ext (CoveredOne.unique F T k j C hc hd)
  · exact oneCode_card_le F T k j C M hM

lemma local_card_le_rooted (g : ℕ) :
    Fintype.card {c : Candidate F T k // c.labels.card=g ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    Fintype.card {c : Rooted F T k j C // c.cycle.labels.card=g} := by
  apply card_le_of_unique_cover (fun c d => d.val.cycle = c.val)
  · intro c
    obtain ⟨i,hi,hC⟩ := (c.val.mem_deps_iff_rooted F T j C).mp c.property.2
    exact ⟨⟨⟨c.val,i,hi,hC⟩,c.property.1⟩,rfl⟩
  · intro c c' d hc hc'
    exact Subtype.ext (hc.symm.trans hc')

lemma local_one_card_le (hk3 : 3 ≤ k) (hk5 : k ≤ 5) (M : ℕ)
    (hM : ∀ r, (C.val ∩ T r).card ≤ M) :
    Fintype.card {c : Candidate F T k // c.labels.card=1 ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    Fintype.card R*k^2*2^k*M^2*Fintype.card Q^k :=
  (local_card_le_rooted F T k j C 1).trans (one_rooted_card_le F T k j C hk3 hk5 M hM)

lemma local_two_card_le (hk5 : k ≤ 5) :
    Fintype.card {c : Candidate F T k // c.labels.card=2 ∧ (⟨j,C⟩ : SlabVariable F) ∈ c.deps F T} ≤
    (Fintype.card R*Fintype.card Q)*k^4*3^k*C.val.card*(Fintype.card Q*Fintype.card E)^2*Fintype.card Q^k :=
  (local_card_le_rooted F T k j C 2).trans (two_rooted_card_le F T k j C hk5)

end Candidate
end KaplanskyCounterexample.FiniteGeometry
end

end OAI
