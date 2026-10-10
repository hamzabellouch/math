import OAI.RingTheory.DirectFiniteness.SlabKeys

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical
open Module
namespace KaplanskyCounterexample.FiniteGeometry

variable {Q : Type u_1} {P : Type u_2} [Field Q] [AddCommGroup P] [Module Q P]

def NoEigenvector (J : P →ₗ[Q] P) : Prop :=
  ∀ x : P, x ≠ 0 → ∀ c : Q, J x ≠ c • x

lemma independent_pair_of_noEigenvector (J : P →ₗ[Q] P) (hJ : NoEigenvector J)
    (x : P) (hx : x ≠ 0) : LinearIndependent Q ![J x, x] := by
  rw [linearIndependent_fin2]
  exact ⟨hx, fun c h => hJ x hx c h.symm⟩

theorem existsUnique_slab_functional [FiniteDimensional Q P]
    (hd : finrank Q P = 2) (J : P →ₗ[Q] P) (hJ : NoEigenvector J)
    (x : P) (hx : x ≠ 0) (c : Q) :
    ∃! γ : P →ₗ[Q] Q, γ x = 1 ∧ γ (J x) = c := by
  let B : Basis (Fin 2) Q P := basisOfLinearIndependentOfCardEqFinrank
    (independent_pair_of_noEigenvector J hJ x hx) (by simp [hd])
  have hB (i : Fin 2) : B i = ![J x, x] i := by
    simp [B]
  let γ : P →ₗ[Q] Q := B.constr Q ![c, 1]
  have hγ (i : Fin 2) : γ (B i) = ![c, 1] i := by simp [γ]
  have hγx : γ x = 1 := by simpa [hB] using hγ 1
  have hγJx : γ (J x) = c := by simpa [hB] using hγ 0
  refine ⟨γ, ⟨hγx, hγJx⟩, ?_⟩
  intro δ hδ
  apply B.ext
  intro i
  fin_cases i <;> simp_all

def slabLine (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) : Set (P × Q) :=
  {p | γ p.1 = 1 ∧ p.2 = γ (J p.1)}

lemma slabLine_off_axis (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q)
    {p : P × Q} (hp : p ∈ slabLine J γ) : p.1 ≠ 0 := by
  intro h
  have h' := hp.1
  rw [h, map_zero] at h'
  exact zero_ne_one h'

lemma slabLine_functional_ne_zero (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q)
    {p : P × Q} (hp : p ∈ slabLine J γ) : γ ≠ 0 := by
  intro h
  have h' := hp.1
  rw [h] at h'
  exact zero_ne_one h'

/-- The axis and the displayed lifted lines partition the slab. -/
theorem slab_partition [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (hJ : NoEigenvector J) (p : P × Q) :
    p.1 = 0 ∨ ∃! γ : {γ : P →ₗ[Q] Q // γ ≠ 0}, p ∈ slabLine J γ.val := by
  by_cases hx : p.1 = 0
  · exact Or.inl hx
  · right
    obtain ⟨γ, hγ, hu⟩ := existsUnique_slab_functional hd J hJ p.1 hx p.2
    have hp : p ∈ slabLine J γ := ⟨hγ.1, hγ.2.symm⟩
    refine ⟨⟨γ, slabLine_functional_ne_zero J γ hp⟩, hp, ?_⟩
    intro δ hδ
    apply Subtype.ext
    exact hu δ.val ⟨hδ.1, hδ.2.symm⟩

/-- The displayed set is a full affine line, not merely an arbitrary part
of the partition; its direction has nonzero projection to the plane. -/
theorem slabLine_is_line [FiniteDimensional Q P] (hd : finrank Q P = 2)
    (J : P →ₗ[Q] P) (γ : P →ₗ[Q] Q) (hγ : γ ≠ 0) :
    ∃ u v : P × Q, v.1 ≠ 0 ∧
      slabLine J γ = Set.range (fun t : Q => u + t • v) := by
  have hex : ∃ x : P, γ x ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hγ (LinearMap.ext hn)
  obtain ⟨x, hx⟩ := hex
  let x₀ := (γ x)⁻¹ • x
  have hx₀ : γ x₀ = 1 := by simp [x₀, hx]
  have hsurj : Function.Surjective γ := by
    intro c
    exact ⟨c • x₀, by simp [hx₀]⟩
  have hker : finrank Q γ.ker = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker γ
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_self, hd] at h
    omega
  have hkn : γ.ker ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hker
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkn
  let y' : γ.ker := ⟨y, hy⟩
  have hy' : y' ≠ 0 := by
    intro h
    exact hy0 (congrArg Subtype.val h)
  have hgen : ∀ z : γ.ker, ∃ t : Q, t • y' = z :=
    (finrank_eq_one_iff_of_nonzero' y' hy').mp hker
  have hγy : γ y = 0 := hy
  refine ⟨(x₀, γ (J x₀)), (y, γ (J y)), hy0, ?_⟩
  ext p
  constructor
  · intro hp
    have hz : p.1 - x₀ ∈ γ.ker := by
      change γ (p.1 - x₀) = 0
      rw [map_sub, hp.1, hx₀, sub_self]
    obtain ⟨t, ht⟩ := hgen ⟨p.1 - x₀, hz⟩
    have hty : t • y = p.1 - x₀ := congrArg Subtype.val ht
    have hxp : x₀ + t • y = p.1 := eq_sub_iff_add_eq.mp hty |>.symm ▸ add_comm _ _
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact hxp
    · change γ (J x₀) + t * γ (J y) = p.2
      rw [hp.2, ← hxp]
      simp
  · rintro ⟨t, rfl⟩
    constructor
    · change γ (x₀ + t • y) = 1
      simp [hx₀, hγy]
    · change γ (J x₀) + t * γ (J y) = γ (J (x₀ + t • y))
      simp

variable {F : Type u_3} [Field F] [Algebra Q F]

/-- A quadratic extension supplies the operator without eigenvectors. -/
theorem exists_noEigenvector_of_quadratic (hd : finrank Q F = 2) :
    ∃ J : F →ₗ[Q] F, NoEigenvector J := by
  have hn : ¬ Function.Surjective (algebraMap Q F) := by
    intro hs
    have h := Module.finrank_of_bijective_algebraMap ⟨(algebraMap Q F).injective, hs⟩
    omega
  have hn' : ∃ η : F, ∀ c : Q, algebraMap Q F c ≠ η := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  obtain ⟨η, hη⟩ := hn'
  refine ⟨LinearMap.mulLeft Q η, ?_⟩
  intro x hx c h
  apply hη c
  apply mul_right_cancel₀ hx
  simpa [Algebra.smul_def] using h.symm

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
