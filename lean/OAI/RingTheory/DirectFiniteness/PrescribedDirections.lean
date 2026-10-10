import OAI.RingTheory.DirectFiniteness.AssignedDevelopment

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
open IncidenceDirections
variable (ℓ : ℕ) [Fact ℓ.Prime]

local instance directionModulusNeZero : NeZero ℓ := inferInstance

/-- A direction is ordered by its full underlying point set. Slopes are just
coordinates for all of the one-dimensional subspaces, including the vertical one. -/
def directionSet (d : Option (ZMod ℓ)) : Finset (Fin 2 → ZMod ℓ) :=
  Finset.univ.image (directionMap d)

lemma directionSet_injective : Function.Injective (directionSet ℓ) := by
  intro d e he
  by_contra hne
  have hm : directionMap d 1 ∈ directionSet ℓ e := he ▸ Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp hm
  have hh := directionMap_independent hne 1 (-c) (by simp [hc])
  exact one_ne_zero hh.1

local instance directionResidueOrder : LinearOrder (ZMod ℓ) := residueOrder ℓ

@[instance_reducible] def directionOrder : LinearOrder (Option (ZMod ℓ)) :=
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  letI : LinearOrder (Finset (Fin 2 → ZMod ℓ)) := subsetOrder _
  LinearOrder.lift' (directionSet ℓ) (directionSet_injective ℓ)

lemma direction_first (d : Option (ZMod ℓ)) (x : Fin 2 → ZMod ℓ)
    (hx : x ∈ directionSet ℓ d) (hne : x ≠ 0) :
    toLex (directionMap d 1) ≤ toLex x := by
  obtain ⟨c,_,rfl⟩ := Finset.mem_image.mp hx
  have hc : c ≠ 0 := by intro hc; apply hne; simp [hc]
  by_cases hc1 : c=1
  · subst c; exact le_refl _
  have hc0 : c.val ≠ 0 := by simpa using hc
  have hc1' : c.val ≠ 1 := by
    intro he
    apply hc1
    apply ZMod.val_injective ℓ
    simpa only [ZMod.val_one] using he
  have hl : (1:ZMod ℓ) < c := by
    change (1:ZMod ℓ).val < c.val
    rw [ZMod.val_one]
    omega
  apply le_of_lt
  cases d with
  | none =>
    refine ⟨1,?_,?_⟩
    · intro j hj
      have hj0 : j=0 := by omega
      subst j
      rfl
    · exact hl
  | some d =>
    refine ⟨0,?_,?_⟩
    · intro j hj; have : ¬ j < 0 := Fin.not_lt_zero j; exact (this hj).elim
    · exact hl

lemma direction_first_nonzero (d : Option (ZMod ℓ)) : directionMap d (1:ZMod ℓ) ≠ 0 := by
  intro hz
  exact one_ne_zero (directionMap_injective d (hz.trans (map_zero _).symm))

lemma direction_range_finrank (d : Option (ZMod ℓ)) :
    Module.finrank (ZMod ℓ) (LinearMap.range (directionMap d))=1 := by
  rw [LinearMap.finrank_range_of_inj (directionMap_injective d),Module.finrank_self]

def orderedAssignment {V F : Type} [Fintype F] [LinearOrder F] (Inc : F → Finset V)
    (hdeg : ∀ v, Fintype.card {f : F // v ∈ Inc f}=ℓ+1)
    (v : V) : {f : F // v ∈ Inc f} ≃ Option (ZMod ℓ) :=
  letI := directionOrder ℓ
  ((Fintype.orderIsoFinOfCardEq {f : F // v ∈ Inc f} (hdeg v)).toEquiv.symm.trans
    (Fintype.orderIsoFinOfCardEq (Option (ZMod ℓ)) (by simp)).toEquiv)

end KaplanskyCounterexample.Prescription
end

end OAI
