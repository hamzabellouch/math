import OAI.RingTheory.DirectFiniteness.PrescribedSearch

namespace OAI

universe u_1 u_2 u_3 u_4

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.IncidenceDirections
variable {K : Type u_1} [Field K]

def directionMap : Option K → K →ₗ[K] (Fin 2 → K)
  | none =>
    { toFun := fun c => ![0, c]
      map_add' := by intros; ext i; fin_cases i <;> simp
      map_smul' := by intros; ext i; fin_cases i <;> simp }
  | some a =>
    { toFun := fun c => ![c, a * c]
      map_add' := by intros; ext i; fin_cases i <;> simp [mul_add]
      map_smul' := by intros; ext i; fin_cases i <;> simp; ring }

lemma directionMap_injective (d : Option K) : Function.Injective (directionMap d) := by
  cases d with
  | none => intro x y h; simpa [directionMap] using congrFun h 1
  | some a => intro x y h; simpa [directionMap] using congrFun h 0

lemma directionMap_independent {d e : Option K} (hne : d ≠ e) (c b : K)
    (h : directionMap d c + directionMap e b = 0) : c = 0 ∧ b = 0 := by
  have h₀ := congrFun h 0
  have h₁ := congrFun h 1
  cases d <;> cases e <;> simp_all [directionMap]
  rename_i d e
  have hde : d - e ≠ 0 := sub_ne_zero.mpr hne
  have hc : (d - e) * c = 0 := by linear_combination h.2 - e * h.1
  have hz := (mul_eq_zero.mp hc).resolve_left hde
  exact ⟨hz, by simpa [hz] using h.1⟩

lemma directionMap_covers (a : Fin 2 → K) (ha : a ≠ 0) :
    ∃ d : Option K, ∃ c : K, c ≠ 0 ∧ directionMap d c = a := by
  by_cases h₀ : a 0 = 0
  · have h₁ : a 1 ≠ 0 := by
      intro h₁
      apply ha
      ext i
      fin_cases i <;> assumption
    refine ⟨none, a 1, h₁, ?_⟩
    ext i
    fin_cases i <;> simp [directionMap, h₀]
  · refine ⟨some (a 1 / a 0), a 0, h₀, ?_⟩
    ext i
    fin_cases i <;> simp [directionMap, h₀]

/-- Every nonzero vector lies on exactly one of these parametrized lines. -/
def nonzeroEquiv : (Option K × {c : K // c ≠ 0}) ≃ {a : Fin 2 → K // a ≠ 0} :=
  Equiv.ofBijective
    (fun p => ⟨directionMap p.1 p.2.val, fun h =>
      p.2.property ((directionMap_injective p.1) (h.trans (map_zero _).symm))⟩) (by
      constructor
      · rintro ⟨d, c, hc⟩ ⟨e, b, hb⟩ h
        have heq : directionMap d c = directionMap e b := congrArg Subtype.val h
        have hde : d = e := by
          by_contra hne
          apply hc
          exact (directionMap_independent hne c (-b) (by simpa [sub_eq_add_neg] using sub_eq_zero.mpr heq)).1
        subst e
        exact Prod.ext rfl (Subtype.ext (directionMap_injective d heq))
      · rintro ⟨a, ha⟩
        obtain ⟨d, c, hc, hca⟩ := directionMap_covers a ha
        exact ⟨(d, ⟨c, hc⟩), Subtype.ext hca⟩)

@[simp] lemma nonzeroEquiv_apply (d : Option K) (c : {c : K // c ≠ 0}) :
    (nonzeroEquiv (d, c)).val = directionMap d c := rfl

/-- The local subgroup decomposition, before applying a group-ring map. -/
lemma sum_directions [Fintype K] {M : Type u_2} [AddCommGroup M]
    (f : (Fin 2 → K) → M) :
    ∑ a : Fin 2 → K, f a = f 0 + ∑ d : Option K, (∑ c : K, f (directionMap d c) - f 0) := by
  rw [Fintype.sum_eq_add_sum_subtype_ne f 0]
  congr 1
  rw [← Equiv.sum_comp nonzeroEquiv (fun a => f a.val), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  rw [Fintype.sum_eq_add_sum_subtype_ne (fun c : K => f (directionMap d c)) 0]
  simp

variable {V : Type u_3} {F : Type u_4} [Fintype F] (Inc : F → Finset V) (ℓ : ℕ) [Fact ℓ.Prime]

/-- At a point, assign the incident lines bijectively to all slopes. -/
def incidenceEquiv (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) : {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ) :=
  Fintype.equivOfCardEq (by simpa using hdeg v)

def incidenceMap (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f : {f : F // v ∈ Inc f}) : ZMod ℓ →+ (Fin 2 → ZMod ℓ) :=
  (directionMap (incidenceEquiv Inc ℓ hdeg v f)).toAddMonoidHom

lemma incidenceMap_injective (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f : {f : F // v ∈ Inc f}) : Function.Injective (incidenceMap Inc ℓ hdeg v f) :=
  directionMap_injective _

lemma incidenceMap_independent (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (f g : {f : F // v ∈ Inc f}) (hne : f ≠ g) (a b : ZMod ℓ)
    (h : incidenceMap Inc ℓ hdeg v f a + incidenceMap Inc ℓ hdeg v g b = 0) :
    a = 0 ∧ b = 0 :=
  directionMap_independent ((incidenceEquiv Inc ℓ hdeg v).injective.ne hne) a b h

lemma incidenceMap_covers (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f} = ℓ + 1)
    (v : V) (a : Fin 2 → ZMod ℓ) (ha : a ≠ 0) :
    ∃ (f : F) (hf : v ∈ Inc f) (c : ZMod ℓ), c ≠ 0 ∧ incidenceMap Inc ℓ hdeg v ⟨f, hf⟩ c = a := by
  obtain ⟨d, c, hc, hca⟩ := directionMap_covers a ha
  obtain ⟨f, hf⟩ := (incidenceEquiv Inc ℓ hdeg v).surjective d
  exact ⟨f.val, f.property, c, hc, by simpa [incidenceMap, hf] using hca⟩

end KaplanskyCounterexample.IncidenceDirections
end

end OAI
