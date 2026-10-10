import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Balance.BalanceGluing

namespace OAI

/-! Balance Lift. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma coordinateProjection_letterLift {n d D : ℕ} (f : Fin d → Fin D)
    (P : (Fin n → Fin d) → Prop) (Q : (Fin n → Fin D) → Prop)
    (h : ∀ w, Q (f ∘ w) ↔ P w) (x : WordSpace n d) :
    coordinateProjection Q (letterLift f x) = letterLift f (coordinateProjection P x) := by
  classical
  conv_lhs => rw [← (Pi.basisFun ℂ (Fin n → Fin d)).sum_repr x]
  conv_rhs => rw [← (Pi.basisFun ℂ (Fin n → Fin d)).sum_repr x]
  simp only [map_sum,map_smul,Pi.basisFun_apply,letterLift_single,
    coordinateProjection_single,h]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases hp : P w <;> simp [hp,letterLift_single]

lemma letterLift_nonzero_word {n d D : ℕ} (f : Fin d → Fin D) (hf : Function.Injective f)
    (x : WordSpace n d) (w : Fin n → Fin D) (hw : letterLift f x w ≠ 0) :
    ∃ a : Fin n → Fin d, f ∘ a = w ∧ x a ≠ 0 := by
  classical
  have hm := letterLift_mem_alphabet (Set.range f) f (fun a => ⟨a,rfl⟩) x
  have hr : ∀ i, ∃ a, f a = w i := by
    intro i
    by_contra hi
    exact hw (hm w ⟨i,hi⟩)
  choose a ha using hr
  have he : f ∘ a = w := funext ha
  refine ⟨a,he,?_⟩
  rw [←he,letterLift_eval f hf] at hw
  exact hw

namespace Balance

lemma output_pairLetterMap {d D : ℕ} (f : Fin d → Fin D)
    (hf : ∀ a, (f a).val = a.val) (a : Fin (d*d)) :
    output (pairLetterMap f f a) = output a := by
  simp only [output,pairLetterMap,Equiv.symm_apply_apply,hf]

lemma cyclicSquareMap_lift_mem {n d D : ℕ} (f : Fin d → Fin D)
    (v : WordSpace n d) (x : WordSpace n (d*d))
    (hx : x ∈ (cyclicSquareMap v).range) :
    letterLift (pairLetterMap f f) x ∈ (cyclicSquareMap (letterLift f v)).range := by
  obtain ⟨z,rfl⟩ := hx
  let F := cyclicMap (letterLift f) v
  refine ⟨TensorProduct.map F.toLinearMap F.toLinearMap z,?_⟩
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul x y =>
    change wordTensor _ _ _ (letterLift f x.val ⊗ₜ[ℂ] letterLift f y.val) =
      letterLift (pairLetterMap f f) (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val))
    exact (letterLift_wordTensor f f x.val y.val).symm

def Piece.lift {n d D : ℕ} {G Y : Type*} [Group G] [AddCommGroup Y] [Module ℂ Y]
    {v : WordSpace n d} {c : Fin n → ℕ} {σ : ℕ → ℤ}
    {φ : G →* fiberGroup c} {τ : Representation ℂ G Y}
    (f : Fin d → Fin D) (hf : ∀ a, (f a).val = a.val)
    (A : Fin (D*D) → Prop) (label : Fin (D*D) → ℕ)
    (P : Piece v c (A ∘ pairLetterMap f f) (label ∘ pairLetterMap f f) σ φ τ) :
    Piece (letterLift f v) c A label σ φ τ := by
  have hfi : Function.Injective f := by
    intro a b he
    apply Fin.ext
    simpa only [hf] using congrArg Fin.val he
  let J := pairLetterMap f f
  have hJi : Function.Injective J := pairLetterMap_injective f f hfi hfi
  let T : Representation.IntertwiningMap
      ((wordRep n (d*d)).comp ((fiberGroup c).subtype.comp φ))
      ((wordRep n (D*D)).comp ((fiberGroup c).subtype.comp φ)) :=
    ⟨(letterLift J).toLinearMap, fun g => (letterLift J).isIntertwining' (φ g).val⟩
  refine {
    surj := P.surj
    raw := (letterLift J).toLinearMap.comp P.raw
    raw_mem := fun y => cyclicSquareMap_lift_mem f v _ (P.raw_mem y)
    raw_sums := ?_
    projected := T.comp P.projected
    injective := (letterLift_injective J hJi).comp P.injective
    projection_eq := ?_ }
  · intro y w hw k
    obtain ⟨a,rfl,ha⟩ := letterLift_nonzero_word J hJi (P.raw y) w hw
    have he := P.raw_sums y a ha k
    simpa only [J, Function.comp_apply,output_pairLetterMap f hf] using he
  · intro y
    change coordinateProjection (componentWords c A label) (letterLift J (P.raw y)) =
      letterLift J (P.projected y)
    rw [coordinateProjection_letterLift J (componentWords c (A ∘ J) (label ∘ J))
      (componentWords c A label) (fun _ => Iff.rfl),P.projection_eq]

end Balance
end Saxl
end
end

end OAI
