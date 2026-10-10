import OAI.RingTheory.DirectFiniteness.MatrixBlock

namespace OAI

universe u_1 u_2 u_3

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.ProductAlgebras
variable {K : Type u_1} {G : Type u_2} {H : Type u_3} [Field K] [Group G] [Group H]

def leftMap : MonoidAlgebra K G →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inl G H)
def rightMap : MonoidAlgebra K H →ₐ[K] MonoidAlgebra K (G × H) :=
  MonoidAlgebra.mapDomainAlgHom K K (MonoidHom.inr G H)

lemma left_right_commute (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) :
    Commute (leftMap x) (rightMap y) := by
  induction x using MonoidAlgebra.induction_on with
  | of g =>
    induction y using MonoidAlgebra.induction_on with
    | of h =>
      change _ * _ = _ * _
      simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single]
    | add y z hy hz => simpa only [map_add] using hy.add_right hz
    | smul c y hy => simpa only [map_smul] using hy.smul_right c
  | add x z hx hz => simpa only [map_add] using hx.add_left hz
  | smul c x hx => simpa only [map_smul] using hx.smul_left c

lemma product_coeff (x : MonoidAlgebra K G) (y : MonoidAlgebra K H) (g : G) (h : H) :
    (leftMap x * rightMap y).coeff (g,h) = x.coeff g * y.coeff h := by
  induction x using MonoidAlgebra.induction_on with
  | of a =>
    induction y using MonoidAlgebra.induction_on with
    | of b =>
      by_cases hag : a = g <;> by_cases hbh : b = h <;>
        simp [leftMap, rightMap, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_single,
          hag, hbh, Prod.ext_iff]
    | add y z hy hz =>
      simp only [map_add, mul_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hz]
    | smul c y hy =>
      simp only [map_smul, mul_smul_comm, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul, hy]
      ring
  | add x z hx hz =>
    simp only [map_add, add_mul, MonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hz]
  | smul c x hx =>
    simp only [map_smul, smul_mul_assoc, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, hx]
    ring

lemma product_ne_zero {x : MonoidAlgebra K G} {y : MonoidAlgebra K H}
    (hx : x ≠ 0) (hy : y ≠ 0) : leftMap x * rightMap y ≠ 0 := by
  obtain ⟨g,hg⟩ : ∃ g, x.coeff g ≠ 0 := by
    by_contra! h
    apply hx
    ext g
    exact h g
  obtain ⟨h,hh⟩ : ∃ h, y.coeff h ≠ 0 := by
    by_contra! h
    apply hy
    ext a
    exact h a
  intro he
  have he' := congrArg (fun z : MonoidAlgebra K (G × H) => z.coeff (g,h)) he
  rw [product_coeff] at he'
  exact mul_ne_zero hg hh he'

end KaplanskyCounterexample.ProductAlgebras
end

end OAI
