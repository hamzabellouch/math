import OAI.RingTheory.DirectFiniteness.PrescribedSubfield

namespace OAI

noncomputable section
open scoped Classical
namespace KaplanskyCounterexample.Prescription

abbrev Input := {h : ℕ // 2 ≤ h}

def fieldDegree (h : Input) : ℕ := h.val*(prime h.val-1)
lemma fieldDegree_pos (h : Input) : 0 < fieldDegree h := by
  have := prime_ge h.val h.property
  exact Nat.mul_pos (by omega) (by omega)

abbrev K (h : Input) := CoefficientField (fieldDegree h) (fieldDegree_pos h)
instance K_field (input : Input) : Field (K input) := inferInstance

instance K_char (h : Input) : CharP (K h) 2 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 2) (K h)).injective 2

abbrev Q (h : Input) := rootSubfield (K h) h.val

instance K_order (h : Input) : LinearOrder (K h) := coefficientFieldOrder _ _

lemma K_card (h : Input) : Fintype.card (K h)=2^(fieldDegree h) :=
  coefficientField_card _ _
lemma Q_card (h : Input) : Fintype.card (Q h)=Qcard h.val := by
  apply rootSubfield_card (K h) h.val (by omega)
  rw [coefficientField_finrank]
  exact dvd_mul_right _ _

/-- The enumeration of the prescribed root subfield is in inherited coefficient order. -/
def enumeration (h : Input) : Fin (Qcard h.val) ≃ Q h :=
  (Fintype.orderIsoFinOfCardEq (Q h) (Q_card h)).toEquiv

lemma primitive_exists (h : Input) : ∃ ζ : K h, IsPrimitiveRoot ζ (prime h.val) := by
  let : Fact (prime h.val).Prime := ⟨prime_prime h.val⟩
  have hc : (2:ℕ).Coprime (prime h.val) := Nat.coprime_two_left.mpr (prime_odd h.val h.property)
  have hf := (Nat.ModEq.pow_card_sub_one_eq_one (prime_prime h.val) hc).pow h.val
  have hd : prime h.val ∣ Fintype.card (K h)ˣ := by
    rw [Fintype.card_units,K_card]
    simpa only [fieldDegree,← pow_mul,one_pow,Nat.mul_comm] using hf.symm.dvd'
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card (G := (K h)ˣ) (prime h.val) hd
  refine ⟨u,IsPrimitiveRoot.iff_orderOf.mpr ?_⟩
  simpa only [orderOf_units] using hu

/-- The first element of multiplicative order ell in the literal coefficient order. -/
def zeta (h : Input) : K h := first (fun ζ => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)
lemma zeta_primitive (h : Input) : IsPrimitiveRoot (zeta h) (prime h.val) := by
  unfold zeta
  exact first_spec (fun ζ : K h => IsPrimitiveRoot ζ (prime h.val)) (primitive_exists h)
lemma zeta_first (h : Input) (ζ : K h) (hζ : IsPrimitiveRoot ζ (prime h.val)) :
    zeta h ≤ ζ := by
  unfold zeta
  exact first_le _ _ ζ hζ

end KaplanskyCounterexample.Prescription
end

end OAI
