import OAI.RingTheory.DirectFiniteness.CoordinateCharacters

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription
variable (ℓ : ℕ) [Fact ℓ.Prime]
variable {V m : Type} [Fintype V] [Fintype m] [LinearOrder V] [LinearOrder m]

local instance slotModulusNeZero : NeZero ℓ := inferInstance

local instance slotIndexWellFounded : WellFoundedLT (Fin 2) := inferInstance

@[instance_reducible] def slotPairOrder : LinearOrder (m × (Fin 2 → ZMod ℓ)) :=
  letI : LinearOrder (ZMod ℓ) := residueOrder ℓ
  letI : LinearOrder (Fin 2 → ZMod ℓ) := vectorOrder
  LinearOrder.lift' (toLex : (m × (Fin 2 → ZMod ℓ)) → Lex (m × (Fin 2 → ZMod ℓ)))
    (fun _ _ he => he)

def slotAssignment (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) :
    V ↪ m × (Fin 2 → ZMod ℓ) :=
  letI := slotPairOrder (m := m) ℓ
  let e := Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl
  let r := (Fintype.orderIsoFinOfCardEq V rfl).symm
  { toFun := fun v => e ⟨(r v).val, by
      have hc : Fintype.card (m × (Fin 2 → ZMod ℓ))=Fintype.card m * ℓ^2 := by simp
      rw [hc]
      exact (r v).isLt.trans_le hsize⟩
    inj' := by
      intro v w he
      apply r.injective
      apply Fin.ext
      have hh := e.injective he
      exact congrArg (fun z => z.val) hh }

/-- The assigned pair has exactly the point's rank in the finite order, so the
image consists of the first t pairs, with none skipped or repeated. -/
lemma slotAssignment_rank (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) :
    letI := slotPairOrder (m := m) ℓ
    ((Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl).symm
      (slotAssignment ℓ hsize v)).val =
      ((Fintype.orderIsoFinOfCardEq V rfl).symm v).val := by
  let := slotPairOrder (m := m) ℓ
  exact congrArg Fin.val (OrderIso.symm_apply_apply _ _)

lemma slotAssignment_first_pairs (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2)
    (p : m × (Fin 2 → ZMod ℓ)) :
    letI := slotPairOrder (m := m) ℓ
    p ∈ Set.range (slotAssignment ℓ hsize) ↔
      ((Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl).symm p).val < Fintype.card V := by
  let := slotPairOrder (m := m) ℓ
  let e := Fintype.orderIsoFinOfCardEq (m × (Fin 2 → ZMod ℓ)) rfl
  let r := Fintype.orderIsoFinOfCardEq V rfl
  constructor
  · rintro ⟨v,rfl⟩
    rw [slotAssignment_rank]
    exact (r.symm v).isLt
  · intro hp
    refine ⟨r ⟨(e.symm p).val,hp⟩,?_⟩
    apply e.symm.injective
    apply Fin.ext
    rw [slotAssignment_rank]
    exact congrArg Fin.val (r.symm_apply_apply _)

def assignedSlot (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) : m :=
  (slotAssignment ℓ hsize v).1

def assignedForm (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2) (v : V) :
    CoordinateCharacters.Plane ℓ →* CoordinateCharacters.Cyclic ℓ :=
  CoordinateCharacters.form ℓ (slotAssignment ℓ hsize v).2

lemma assignedForm_distinct (hsize : Fintype.card V ≤ Fintype.card m * ℓ^2)
    (v w : V) (hvw : v ≠ w) (hs : assignedSlot ℓ hsize v=assignedSlot ℓ hsize w) :
    assignedForm ℓ hsize v ≠ assignedForm ℓ hsize w := by
  intro he
  exact hvw ((slotAssignment ℓ hsize).injective
    (Prod.ext hs (CoordinateCharacters.form_injective ℓ he)))

end KaplanskyCounterexample.Prescription
end

end OAI
