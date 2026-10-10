import OAI.RingTheory.DirectFiniteness.ChosenCriterion

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open IncidenceDirections
variable (ℓ : ℕ) [Fact ℓ.Prime]

lemma every_direction (S : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ))
    (hS : Module.finrank (ZMod ℓ) S=1) :
    ∃ d : Option (ZMod ℓ), LinearMap.range (directionMap d)=S := by
  have hne : S ≠ ⊥ := by
    intro he
    rw [he, finrank_bot] at hS
    omega
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨d,c,hc,hcx⟩ := directionMap_covers x hx0
  refine ⟨d,Submodule.eq_of_le_of_finrank_eq ?_ ?_⟩
  · have h1 : directionMap d 1 ∈ S := by
      have hh := S.smul_mem c⁻¹ hx
      rw [← hcx,← map_smul] at hh
      simpa [hc] using hh
    rintro y ⟨k,rfl⟩
    have hh := S.smul_mem k h1
    rw [← map_smul] at hh
    simpa using hh
  · rw [direction_range_finrank,hS]

lemma mem_directionSet (d : Option (ZMod ℓ)) (x : Fin 2 → ZMod ℓ) :
    x ∈ directionSet ℓ d ↔ x ∈ LinearMap.range (directionMap d) := by
  simp only [directionSet,Finset.mem_image,Finset.mem_univ,true_and,LinearMap.mem_range]

lemma every_direction_unique (S : Submodule (ZMod ℓ) (Fin 2 → ZMod ℓ))
    (hS : Module.finrank (ZMod ℓ) S=1) :
    ∃! d : Option (ZMod ℓ), LinearMap.range (directionMap d)=S := by
  obtain ⟨d,hd⟩ := every_direction ℓ S hS
  refine ⟨d,hd,?_⟩
  intro e he
  apply directionSet_injective ℓ
  ext x
  rw [mem_directionSet,mem_directionSet,he,hd]

lemma orderedAssignment_strictMono {V F : Type} [Fintype F] [LinearOrder F]
    (Inc : F → Finset V) (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f}=ℓ+1) (v : V) :
    letI := directionOrder ℓ
    StrictMono (orderedAssignment ℓ Inc hdeg v) := by
  let := directionOrder ℓ
  exact (Fintype.orderIsoFinOfCardEq (Option (ZMod ℓ)) (by simp)).strictMono.comp
    (Fintype.orderIsoFinOfCardEq {f : F // v ∈ Inc f} (hdeg v)).symm.strictMono

end KaplanskyCounterexample.Prescription
end

end OAI
