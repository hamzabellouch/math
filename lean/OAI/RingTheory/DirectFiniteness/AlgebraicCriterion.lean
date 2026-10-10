import OAI.RingTheory.DirectFiniteness.Rectangular

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

noncomputable section
open scoped Classical BigOperators
namespace KaplanskyCounterexample.CharacterTwist
open CharacterIdempotents AlgebraicPacking
variable {A : Type u_1} {N : Type u_2} {C : Type u_3} {V : Type u_4} {m : Type u_5} {K : Type u_6} [CommGroup A] [Group N] [CommGroup C]
variable [Field K] [Fintype A] [Fintype C] [Fintype V] [Fintype m]
variable (ι : V → A →* N) (hi : ∀ v, Function.Injective (ι v)) (v₀ : V)
variable (α : V → A →* C) (ξ : C →* Kˣ)

lemma map_pushed {G : Type u_7} {H : Type u_8} [Group G] [Group H]
    (f : G →* H) (g : A →* G) (χ : A →* Kˣ) :
    MonoidAlgebra.mapDomainAlgHom K K f (pushed g χ) = pushed (f.comp g) χ := by
  unfold pushed
  rw [MonoidAlgebra.mapDomainAlgHom_comp]
  rfl

lemma defect_ne_zero (X : Matrix m V K) (hlt : Fintype.card m < Fintype.card V)
    (hA : (Fintype.card A : K) ≠ 0) (hC : (Fintype.card C : K) ≠ 0) :
    Matrix.diagonal (fun _ : V => e ι hi v₀ α ξ) *
      (Rectangular.T X (P ι hi v₀ α) * Rectangular.U X (P ι hi v₀ α) -
        Matrix.diagonal (P ι hi v₀ α)) ≠ 0 := by
  let pH (v : V) : MonoidAlgebra K (N × C) :=
    pushed ((MonoidHom.inl N C).comp (ι v)) 1
  let eH : MonoidAlgebra K (N × C) := pushed (MonoidHom.inr N C) ξ
  let f := MonoidAlgebra.mapDomainAlgHom K K (emb ι hi v₀ α)
  have hf : Function.Injective f := MonoidAlgebra.mapDomain_injective (emb_injective ι hi v₀ α)
  have hp (v : V) : f (pH v) = P ι hi v₀ α v := map_pushed _ _ _
  have he : f eH = e ι hi v₀ α ξ := map_pushed _ _ _
  let ρ : (N × C) →* K := (Units.coeHom K).comp (ξ.comp (MonoidHom.snd N C))
  let ε := MonoidAlgebra.lift K K (N × C) ρ
  have hεp (v : V) : ε (pH v) = 1 := by
    apply lift_pushed _ _ ρ _ hA
    intro a
    simp [ρ]
  have hεe : ε eH = 1 := by
    apply lift_pushed _ _ ρ _ hC
    intro c
    rfl
  intro hz
  apply transpose_mul_ne_one X hlt
  ext v w
  have hzvw := congrFun (congrFun hz v) w
  rw [Matrix.diagonal_mul] at hzvw
  change e ι hi v₀ α ξ * ((∑ i : m, (X i v • P ι hi v₀ α v) *
    (X i w • P ι hi v₀ α w)) - (if v = w then P ι hi v₀ α v else 0)) = 0 at hzvw
  have hpre : eH * ((∑ i : m, (X i v • pH v) * (X i w • pH w)) -
      (if v = w then pH v else 0)) = 0 := by
    apply hf
    simp only [map_mul, map_sub, map_sum, map_smul, hp, he, map_zero]
    simpa only [apply_ite, map_zero, hp] using hzvw
  have hs := congrArg ε hpre
  simp only [map_mul, map_sub, map_sum, map_smul, hεp, hεe, one_mul,
    smul_eq_mul, mul_one, map_zero, apply_ite] at hs
  apply sub_eq_zero.mp
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, apply_ite] using hs

theorem square_witnesses {F : Type u_9} [Fintype F]
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
    ∃ a b : Matrix m m (MonoidAlgebra K (L ι hi v₀ α)), a * b = 1 ∧ b * a ≠ 1 := by
  have hp (v : V) : P (K := K) ι hi v₀ α v * P ι hi v₀ α v = P ι hi v₀ α v :=
    pushed_idempotent _ _ hA
  obtain ⟨hUP,hPT,hUT⟩ := Rectangular.identities X (P ι hi v₀ α) lineSum Inc hp hdec hglobal hlocal
  apply square_of_projections (Rectangular.U X (P ι hi v₀ α))
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
