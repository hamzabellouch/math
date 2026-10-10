import OAI.Topology.CoarseAssembly.Definitions
import OAI.Topology.CoarseAssembly.FredholmModule

namespace OAI

/-!
# The odd Fredholm-module group

The group is formed from actual analytic cycles, modulo degeneracy, unitary
equivalence, orthogonal direct sum and norm homotopy. Pullback of star
representations descends to this quotient. This gives the analytic domain
needed for the subsequent geometric construction; no assembly or nonzero
class is postulated here.
-/

noncomputable section

namespace CoarseAssembly.Analytic

universe u

variable (A : Type u) [NonUnitalCStarAlgebra A]

variable {A}

theorem relation_zero {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) :
    (QuotientAddGroup.mk z : OddK A) = 0 :=
  (QuotientAddGroup.eq_zero_iff z).2 (AddSubgroup.subset_closure hz)

theorem degenerate_zero (c : OddCycle A) (hc : c.Degenerate) : cycleClass A c = 0 :=
  relation_zero (.degenerate c hc)

theorem unitary_eq (c d : OddCycle A) (h : c.UnitaryEquivalent d) :
    cycleClass A c = cycleClass A d := by
  have hz := relation_zero (.unitary c d h)
  exact sub_eq_zero.mp (by simpa only [cycleClass, OddK, QuotientAddGroup.mk_sub] using hz)

theorem directSum_eq (c d e : OddCycle A) (h : c.IsDirectSum d e) :
    cycleClass A e = cycleClass A c + cycleClass A d := by
  have hz := relation_zero (.directSum c d e h)
  exact sub_eq_zero.mp (by simpa only [cycleClass, OddK, QuotientAddGroup.mk_sub, QuotientAddGroup.mk_add] using hz)

theorem homotopy_eq (h : OddHomotopy A) :
    cycleClass A (h.eval start) = cycleClass A (h.eval finish) := by
  have hz := relation_zero (.homotopy h)
  exact sub_eq_zero.mp (by simpa only [cycleClass, OddK, QuotientAddGroup.mk_sub] using hz)

variable {B C : Type u} [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C]

theorem precompFree_relation (φ : B →⋆ₙₐ[ℂ] A)
    {z : FreeAbelianGroup (OddCycle A)} (hz : CycleRelation A z) :
    precompFree φ z = 0 := by
  cases hz with
  | degenerate c h =>
    simpa [precompFree] using degenerate_zero (c.precomp φ) (h.precomp φ)
  | unitary c d h =>
    simpa [precompFree] using sub_eq_zero.mpr
      (unitary_eq (c.precomp φ) (d.precomp φ) (h.precomp φ))
  | directSum c d e h =>
    simpa [precompFree] using sub_eq_zero.mpr
      (directSum_eq (c.precomp φ) (d.precomp φ) (e.precomp φ) (h.precomp φ))
  | homotopy h =>
    simpa [precompFree] using sub_eq_zero.mpr (homotopy_eq (h.precomp φ))

@[simp] theorem precomp_cycleClass (φ : B →⋆ₙₐ[ℂ] A) (c : OddCycle A) :
    precomp φ (cycleClass A c) = cycleClass B (c.precomp φ) := by
  exact FreeAbelianGroup.lift_apply_of _ _

theorem hom_ext {D : Type*} [AddCommGroup D] (f g : OddK A →+ D)
    (h : ∀ c, f (cycleClass A c) = g (cycleClass A c)) : f = g := by
  apply QuotientAddGroup.addMonoidHom_ext
  exact FreeAbelianGroup.lift_ext _ _ h

@[simp] theorem precomp_id : precomp (NonUnitalStarAlgHom.id ℂ A) = AddMonoidHom.id (OddK A) := by
  apply hom_ext
  intro c
  simp

theorem precomp_comp (φ : B →⋆ₙₐ[ℂ] A) (ψ : C →⋆ₙₐ[ℂ] B) :
    precomp (φ.comp ψ) = (precomp ψ).comp (precomp φ) := by
  apply hom_ext
  intro c
  simp

end CoarseAssembly.Analytic

end

end OAI
