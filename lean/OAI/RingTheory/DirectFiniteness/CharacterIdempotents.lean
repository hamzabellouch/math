import OAI.RingTheory.DirectFiniteness.MultiHNN

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterIdempotents
variable {K : Type u_1} {A : Type u_2} {G : Type u_3} [Field K] [Group A] [Fintype A] [Group G]

def projector (χ : A →* Kˣ) : MonoidAlgebra K A :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹)

lemma sum_character_eq_zero (χ : A →* Kˣ) (hχ : χ ≠ 1) :
    ∑ a : A, (χ a : K) = 0 := by
  have hn : ∃ b : A, (χ b : K) ≠ 1 := by
    by_contra! h
    apply hχ
    ext b
    exact h b
  obtain ⟨b, hb⟩ := hn
  have hh : (χ b : K) * ∑ a : A, (χ a : K) = ∑ a : A, (χ a : K) := by
    rw [Finset.mul_sum]
    simp only [← Units.val_mul, ← map_mul]
    exact Equiv.sum_comp (Equiv.mulLeft b) (fun a => (χ a : K))
  by_contra hs
  exact hb ((mul_eq_right₀ hs).mp hh)

lemma projector_mul_single (χ : A →* Kˣ) (b : A) :
    projector χ * MonoidAlgebra.single b 1 = (χ b : K) • projector χ := by
  unfold projector
  rw [smul_mul_assoc, Finset.sum_mul, smul_smul]
  rw [mul_comm (χ b : K), ← smul_smul]
  congr 1
  rw [Finset.smul_sum]
  calc
    (∑ a : A, MonoidAlgebra.single a ((χ a : K)⁻¹) * MonoidAlgebra.single b 1) =
        ∑ a : A, (χ b : K) • MonoidAlgebra.single (a * b) ((χ (a * b) : K)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a _
      simp [MonoidAlgebra.single_mul_single, mul_comm]
    _ = _ := Equiv.sum_comp (Equiv.mulRight b)
      (fun a : A => (χ b : K) • MonoidAlgebra.single a ((χ a : K)⁻¹))

lemma projector_mul (χ ψ : A →* Kˣ) :
    projector χ * projector ψ =
      ((Fintype.card A : K)⁻¹ * ∑ b : A, ((χ b : K) * (ψ b : K)⁻¹)) •
        projector χ := by
  conv_lhs => rhs; unfold projector
  rw [mul_smul_comm, Finset.mul_sum]
  have hh (b : A) : projector χ * MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      ((χ b : K) * (ψ b : K)⁻¹) • projector χ := by
    rw [show MonoidAlgebra.single b ((ψ b : K)⁻¹) =
      (ψ b : K)⁻¹ • MonoidAlgebra.single b 1 by simp]
    rw [mul_smul_comm, projector_mul_single, smul_smul, mul_comm]
  simp_rw [hh]
  rw [← Finset.sum_smul, smul_smul]

lemma projector_idempotent (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    IsIdempotentElem (projector χ) := by
  change projector χ * projector χ = projector χ
  rw [projector_mul]
  simp [hcard]

lemma projector_orthogonal (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    projector χ * projector ψ = 0 := by
  rw [projector_mul]
  have hn : χ * ψ⁻¹ ≠ 1 := by
    intro h
    apply hne
    apply MonoidHom.ext
    intro a
    have hh := congrArg (fun f : A →* Kˣ => f a) h
    exact mul_inv_eq_one.mp hh
  have h := sum_character_eq_zero (χ * ψ⁻¹) hn
  simpa using congrArg (fun c : K => ((Fintype.card A : K)⁻¹ * c) • projector χ) h

lemma projector_one_coeff (χ : A →* Kˣ) :
    (projector χ).coeff 1 = (Fintype.card A : K)⁻¹ := by
  simp [projector, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.single_apply]

lemma projector_ne_zero (χ : A →* Kˣ) (hcard : (Fintype.card A : K) ≠ 0) :
    projector χ ≠ 0 := by
  intro h
  have := congrArg (fun p : MonoidAlgebra K A => p.coeff 1) h
  rw [projector_one_coeff] at this
  exact (inv_ne_zero hcard) this

/-- Transport the character projector along an actual subgroup embedding. -/
def pushed (f : A →* G) (χ : A →* Kˣ) : MonoidAlgebra K G :=
  MonoidAlgebra.mapDomainAlgHom K K f (projector χ)

lemma pushed_eq_sum (f : A →* G) (χ : A →* Kˣ) :
    pushed f χ = (Fintype.card A : K)⁻¹ •
      ∑ a : A, MonoidAlgebra.single (f a) ((χ a : K)⁻¹) := by
  simp [pushed, projector, map_sum]

lemma pushed_idempotent (f : A →* G) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) :
    pushed f χ * pushed f χ = pushed f χ := by
  unfold pushed
  rw [← map_mul, projector_idempotent χ hc]

lemma pushed_orthogonal (f : A →* G) (χ ψ : A →* Kˣ) (hne : χ ≠ ψ) :
    pushed f χ * pushed f ψ = 0 := by
  unfold pushed
  rw [← map_mul, projector_orthogonal χ ψ hne, map_zero]

lemma pushed_ne_zero (f : A →* G) (hf : Function.Injective f) (χ : A →* Kˣ)
    (hc : (Fintype.card A : K) ≠ 0) : pushed f χ ≠ 0 := by
  intro h
  exact projector_ne_zero χ hc ((MonoidAlgebra.mapDomain_injective hf) (h.trans (MonoidAlgebra.mapDomain_zero f).symm))

lemma pushed_mul_single (f : A →* G) (χ : A →* Kˣ) (b : A) :
    pushed f χ * MonoidAlgebra.single (f b) 1 = (χ b : K) • pushed f χ := by
  have h := congrArg (MonoidAlgebra.mapDomainAlgHom K K f) (projector_mul_single χ b)
  rw [map_mul, map_smul] at h
  simpa only [pushed, MonoidAlgebra.mapDomainAlgHom_apply, MonoidAlgebra.mapDomain_single] using h

lemma pushed_central (f : A →* G) (χ : A →* Kˣ)
    (hf : ∀ a g, Commute (f a) g) (x : MonoidAlgebra K G) :
    Commute (pushed f χ) x := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    change pushed f χ * MonoidAlgebra.single g 1 = _
    rw [pushed_eq_sum, smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single, mul_one, one_mul,
      (hf a g).eq]
  | add x y hx hy => exact hx.add_right hy
  | smul r x hx => exact hx.smul_right r

lemma lift_pushed (f : A →* G) (χ : A →* Kˣ) (ρ : G →* K)
    (hρ : ∀ a, ρ (f a) = (χ a : K)) (hc : (Fintype.card A : K) ≠ 0) :
    MonoidAlgebra.lift K K G ρ (pushed f χ) = 1 := by
  rw [pushed_eq_sum]
  simp [map_sum, MonoidAlgebra.lift_single, hρ, hc]

end KaplanskyCounterexample.CharacterIdempotents

end

end OAI
