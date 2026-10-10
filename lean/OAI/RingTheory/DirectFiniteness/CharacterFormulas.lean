import OAI.RingTheory.DirectFiniteness.PackingFormulas

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open CharacterIdempotents AlgebraicPacking
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} {m : Type u_5} {K : Type u_6} [CommGroup A] [Group N] [CommGroup C]
variable [Field K] [Fintype A] [Fintype C] [Fintype V] [Fintype m]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C) (ξ : C →* Kˣ)

def aMatrix (X : Matrix m V K) (slot : V → m) : Matrix m m (MonoidAlgebra K (L ι hi v₀ α)) :=
  aMat (Rectangular.U X (P ι hi v₀ α))
    (Jpack slot (uInv ι hi v₀ α) (fun v => e ι hi v₀ α ξ * P ι hi v₀ α v))
    (Matrix.diagonal (fun _ => e ι hi v₀ α ξ))

def bMatrix (X : Matrix m V K) (slot : V → m) : Matrix m m (MonoidAlgebra K (L ι hi v₀ α)) :=
  bMat (Cpack slot (u ι hi v₀ α) (fun v => e ι hi v₀ α ξ * P ι hi v₀ α v))
    (Rectangular.T X (P ι hi v₀ α)) (Matrix.diagonal (fun _ => e ι hi v₀ α ξ))

theorem matrix_products {F : Type u_7} [Fintype F]
    (X : Matrix m V K) (Inc : F → Finset V)
    (lineSum : F → MonoidAlgebra K (L ι hi v₀ α))
    (hdec : ∀ v, P (K := K) ι hi v₀ α v =
      1 + ∑ f : {f : F // v ∈ Inc f}, (lineSum f.val - 1))
    (hglobal : X * X.transpose = 1)
    (hlocal : ∀ f i j, ∑ v ∈ Inc f, X i v * X j v = 0)
    (hlt : Fintype.card m < Fintype.card V)
    (hA : (Fintype.card A : K) ≠ 0) (hC : (Fintype.card C : K) ≠ 0)
    (slot : V → m) (hξ : Function.Injective ξ)
    (hα : ∀ v w, v ≠ w → slot v = slot w → α v ≠ α w) :
    aMatrix ι hi v₀ α ξ X slot * bMatrix ι hi v₀ α ξ X slot=1 ∧
    bMatrix ι hi v₀ α ξ X slot * aMatrix ι hi v₀ α ξ X slot≠1 := by
  have hp (v : V) : P (K := K) ι hi v₀ α v * P ι hi v₀ α v = P ι hi v₀ α v :=
    pushed_idempotent _ _ hA
  obtain ⟨hUP,hPT,hUT⟩ := Rectangular.identities X (P ι hi v₀ α) lineSum Inc hp hdec hglobal hlocal
  apply prescribed_packing_products (Rectangular.U X (P ι hi v₀ α))
    (Rectangular.T X (P ι hi v₀ α)) (P ι hi v₀ α) (Q ι hi v₀ α ξ)
    (u ι hi v₀ α) (uInv ι hi v₀ α) slot (e ι hi v₀ α ξ)
    (pushed_idempotent _ _ hC) (e_central ι hi v₀ α ξ) hp hUP hPT hUT
    (uInv_mul_u ι hi v₀ α) (conjugate_projection ι hi v₀ α ξ)
    _ (defect_ne_zero ι hi v₀ α ξ X hlt hA hC)
  intro v w hvw hslot
  apply pushed_orthogonal
  intro heq
  apply hα v w hvw hslot
  apply MonoidHom.ext
  intro a
  apply hξ
  have heq' := congrArg (fun χ : A →* Kˣ => χ a) heq
  exact inv_injective heq'

end KaplanskyCounterexample.CharacterTwist
end

end OAI
