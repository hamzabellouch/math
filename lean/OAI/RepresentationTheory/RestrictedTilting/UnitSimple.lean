import OAI.RepresentationTheory.RestrictedTilting.UnitAnnihilator

namespace OAI

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace FiberFunctorProof
universe v u w
noncomputable section

 

theorem simple_unit_of_scalar_endomorphisms
    (k : Type w) [Field k] (C : Type u) [Category.{v} C] [Abelian C]
    [MonoidalCategory C] [SymmetricCategory C] [MonoidalPreadditive C]
    [RigidCategory C] [Linear k C] [MonoidalLinear k C]
    (h : Function.Bijective (algebraMap k (End (𝟙_ C)))) : Simple (𝟙_ C) := by
  have hunit : (𝟙 (𝟙_ C)) ≠ (0 : End (𝟙_ C)) := by
    intro hz
    exact one_ne_zero (h.1 (by simpa using hz))
  refine ⟨fun {U} i _ => ?_⟩
  constructor
  · intro hi hz
    let := hi
    apply hunit
    have he := IsIso.inv_hom_id i
    simpa [hz] using he.symm
  · intro hi
    obtain ⟨r, hr⟩ := subunit_retraction i
    let e : End (𝟙_ C) := r ≫ i
    have he : e * e = e := by
      change (r ≫ i) ≫ r ≫ i = r ≫ i
      simp only [Category.assoc, ← Category.assoc i, hr, Category.id_comp]
    obtain ⟨a, ha⟩ := h.2 e
    have haa : a * a = a := h.1 (by simpa only [map_mul, ha] using he)
    have ha01 : a = 0 ∨ a = 1 := by
      have : a * (a - 1) = 0 := by rw [mul_sub, haa, mul_one, sub_self]
      rcases mul_eq_zero.mp this with hz | ho
      · exact Or.inl hz
      · exact Or.inr (sub_eq_zero.mp ho)
    have hei : e = 𝟙 (𝟙_ C) := by
      rcases ha01 with hz | ho
      · have he0 : e = 0 := by simpa [hz] using ha.symm
        exfalso
        apply hi
        calc
          i = i ≫ e := by dsimp [e]; rw [← Category.assoc, hr, Category.id_comp]
          _ = 0 := by rw [he0, comp_zero]
      · simpa [ho] using ha.symm
    exact ⟨⟨r, hr, hei⟩⟩
end
end FiberFunctorProof

end OAI
