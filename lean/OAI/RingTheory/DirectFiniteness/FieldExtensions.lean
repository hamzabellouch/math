import OAI.RingTheory.DirectFiniteness.FrameExistence

namespace OAI

noncomputable section
open Module
namespace KaplanskyCounterexample.FiniteGeometry

/-- Finite characteristic-two fields have finite extensions of every positive degree. -/
theorem exists_finite_extension (Q : Type) [Field Q] [Fintype Q] [CharP Q 2]
    (b : ℕ) (hb : 0 < b) :
    ∃ (F : Type) (_ : Field F) (_ : Algebra Q F) (_ : Fintype F),
      finrank Q F = b := by
  let : Algebra (ZMod 2) Q := ZMod.algebra Q 2
  let h := finrank (ZMod 2) Q
  have hh : 0 < h := Module.finrank_pos
  let F := GaloisField 2 (h * b)
  have hFb : finrank (ZMod 2) F = h * b :=
    GaloisField.finrank 2 (Nat.ne_of_gt (Nat.mul_pos hh hb))
  obtain ⟨f⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (K := Q) (L := F)
    (by rw [hFb]; exact dvd_mul_right h b)
  algebraize [f.toRingHom]
  let : Fintype F := Fintype.ofFinite F
  refine ⟨F, inferInstance, inferInstance, inferInstance, ?_⟩
  have ht := Module.finrank_mul_finrank (ZMod 2) Q F
  rw [hFb] at ht
  exact Nat.eq_of_mul_eq_mul_left hh ht

end KaplanskyCounterexample.FiniteGeometry
end

end OAI
