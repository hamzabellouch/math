import Mathlib

namespace OAI

namespace HarmonicArtin.CoefficientArrays

variable {K I E : Type*} [Field K] [Fintype I]
  {V : I → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

def IsSubrepresentation (d : ∀ i j : I, E → (V i →ₗ[K] V j))
    (U : ∀ i, Submodule K (V i)) : Prop :=
  ∀ i j e, ∀ x ∈ U i, d i j e x ∈ U j

def socle (d : ∀ i j : I, E → (V i →ₗ[K] V j)) (i : I) : Submodule K (V i) :=
  ⨅ j : I, ⨅ e : E, LinearMap.ker (d i j e)

omit [Fintype I] in
@[simp] theorem mem_socle (d : ∀ i j : I, E → (V i →ₗ[K] V j)) (i : I) (x : V i) :
    x ∈ socle d i ↔ ∀ j e, d i j e x = 0 := by
  simp [socle]

theorem exists_nonzero_socle
    (degree : I → ℤ) (d : ∀ i j : I, E → (V i →ₗ[K] V j))
    (hd : ∀ i j e, degree j ≤ degree i → d i j e = 0)
    (U : ∀ i, Submodule K (V i)) (hU : IsSubrepresentation d U)
    (hne : ∃ i, U i ≠ ⊥) :
    ∃ i, ∃ x : V i, x ∈ U i ∧ x ≠ 0 ∧ x ∈ socle d i := by
  classical
  let support : Finset I := Finset.univ.filter (fun i => U i ≠ ⊥)
  have hs : support.Nonempty := by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, by simp [support, hi]⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image support degree hs
  have hUi : U i ≠ ⊥ := (Finset.mem_filter.mp hi).2
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUi
  refine ⟨i, x, hx, hx0, (mem_socle d i x).mpr ?_⟩
  intro j e
  by_cases hj : U j = ⊥
  · have hxj := hU i j e x hx
    simpa [hj] using hxj
  · have hjmem : j ∈ support := by simp [support, hj]
    have hdeg : degree j ≤ degree i := hmax j hjmem
    rw [hd i j e hdeg]
    rfl

theorem subrepresentation_eq_bot_of_socle_eq_bot
    (degree : I → ℤ) (d : ∀ i j : I, E → (V i →ₗ[K] V j))
    (hd : ∀ i j e, degree j ≤ degree i → d i j e = 0)
    (active : Set I) (hsoc : ∀ i ∈ active, socle d i = ⊥)
    (U : ∀ i, Submodule K (V i)) (hU : IsSubrepresentation d U)
    (hsupp : ∀ i, i ∉ active → U i = ⊥) : ∀ i, U i = ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨i, x, hxU, hx0, hxsoc⟩ := exists_nonzero_socle degree d hd U hU h
  have hi : i ∈ active := by
    by_contra hi
    have : x = 0 := by simpa [hsupp i hi] using hxU
    exact hx0 this
  have : x = 0 := by simpa [hsoc i hi] using hxsoc
  exact hx0 this

section Morphisms

variable {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]

omit [Fintype I] in

theorem range_isSubrepresentation
    (dV : ∀ i j : I, E → (V i →ₗ[K] V j))
    (dW : ∀ i j : I, E → (W i →ₗ[K] W j))
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ i j e, (f j).comp (dV i j e) = (dW i j e).comp (f i)) :
    IsSubrepresentation dW (fun i => LinearMap.range (f i)) := by
  rintro i j e _ ⟨x, rfl⟩
  refine ⟨dV i j e x, ?_⟩
  exact LinearMap.congr_fun (hf i j e) x

theorem map_eq_zero_of_socle_eq_bot
    (degree : I → ℤ)
    (dV : ∀ i j : I, E → (V i →ₗ[K] V j))
    (dW : ∀ i j : I, E → (W i →ₗ[K] W j))
    (hd : ∀ i j e, degree j ≤ degree i → dW i j e = 0)
    (f : ∀ i, V i →ₗ[K] W i)
    (hf : ∀ i j e, (f j).comp (dV i j e) = (dW i j e).comp (f i))
    (active : Set I) (hsoc : ∀ i ∈ active, socle dW i = ⊥)
    (hsupp : ∀ i, i ∉ active → f i = 0) : ∀ i, f i = 0 := by
  have hz := subrepresentation_eq_bot_of_socle_eq_bot degree dW hd active hsoc
    (fun i => LinearMap.range (f i)) (range_isSubrepresentation dV dW f hf)
    (fun i hi => by simp [hsupp i hi])
  intro i
  exact LinearMap.range_eq_bot.mp (hz i)

end Morphisms
end HarmonicArtin.CoefficientArrays

end OAI
