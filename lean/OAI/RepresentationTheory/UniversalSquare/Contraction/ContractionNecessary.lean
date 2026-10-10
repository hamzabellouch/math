import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Capacity.NumericBands

namespace OAI

/-! Contraction Necessary. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

lemma polytabloid_action {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : Equiv.Perm (Fin n)) :
    polytabloid (g.symm.trans t) = wordRep n (μ.colLen 0) g (polytabloid t) := by
  rw [polytabloid_move t (g.symm.trans t)]
  have he : tableauMove t (g.symm.trans t) = g := by
    ext i
    simp [tableauMove]
  rw [he]

lemma spechtTensor_linear_ext {n : ℕ} {α β : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) {Z : Type*} [AddCommGroup Z] [Module ℂ Z]
    (R : WordSpace n (α.colLen 0 * β.colLen 0) →ₗ[ℂ] Z)
    (h : ∀ (a' : Tableau n α) (b' : Tableau n β),
      R (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) = 0)
    (z : Specht a ⊗[ℂ] Specht b) : R (spechtTensorMap a b z) = 0 := by
  have aux (x : WordSpace n (α.colLen 0)) (hx : x ∈ spechtSub a)
      (y : WordSpace n (β.colLen 0)) (hy : y ∈ spechtSub b) :
      R (wordTensor _ _ _ (x ⊗ₜ[ℂ] y)) = 0 := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g,rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k,rfl⟩ := hy
        dsimp only
        rw [←polytabloid_action,←polytabloid_action]
        exact h _ _
      | zero => simp
      | add y w hy hw ihy ihw => simp only [TensorProduct.tmul_add,map_add,ihy,ihw,add_zero]
      | smul c y hy ih => simp only [TensorProduct.tmul_smul,map_smul,ih,smul_zero]
    | zero => simp
    | add x w hx hw ihx ihw => simp only [TensorProduct.add_tmul,map_add,ihx,ihw,add_zero]
    | smul c x hx ih => simp only [TensorProduct.smul_tmul,TensorProduct.tmul_smul,map_smul,ih,smul_zero]
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy,add_zero]
  | tmul x y =>
    unfold spechtTensorMap
    change R (wordTensor _ _ _ (x.val ⊗ₜ[ℂ] y.val)) = 0
    exact aux x.val x.property y.val y.property

theorem kronecker_contraction_necessary {n : ℕ} {α β μ : YoungDiagram}
    (a : Tableau n α) (b : Tableau n β) (t : Tableau n μ)
    (h : 0 < kronecker a b t) :
    ∃ (a' : Tableau n α) (b' : Tableau n β) (s : Tableau n μ)
      (L : Fin (μ.colLen 0) → Fin (α.colLen 0 * β.colLen 0) → ℂ),
      dotProduct (wordMap L (polytabloid s))
        (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0 := by
  classical
  obtain ⟨F,hF⟩ := (kronecker_pos_iff a b t).mp h
  let := specht_irreducible t
  have hFi : Function.Injective F := (Representation.IsIrreducible.injective_or_eq_zero (W := Specht a ⊗[ℂ] Specht b) F).resolve_right hF
  let E := (spechtTensorMap a b).comp F
  have hEi : Function.Injective E := (spechtTensorMap_injective a b).comp hFi
  obtain ⟨R,hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id (spechtRep t))
  have he : ∃ (a' : Tableau n α) (b' : Tableau n β),
      R (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')) ≠ 0 := by
    by_contra hn
    push Not at hn
    let p : Specht t := ⟨polytabloid t,mem_cyclic _ _⟩
    have hz := spechtTensor_linear_ext a b R.toLinearMap hn (F p)
    have hi := congrArg (fun H : Representation.IntertwiningMap (spechtRep t) (spechtRep t) => H p) hR
    change R (spechtTensorMap a b (F p)) = p at hi
    change R (spechtTensorMap a b (F p)) = 0 at hz
    have hp : p = 0 := hi.symm.trans hz
    exact polytabloid_ne_zero t (congrArg Subtype.val hp)
  obtain ⟨a',b',hab⟩ := he
  let y := wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b')
  have hv : (R y).val ≠ 0 := fun hz => hab (Subtype.ext hz)
  obtain ⟨g,hg⟩ := specht_detect t (R y).property hv
  rw [wordPair_move] at hg
  let H := (spechtInclusion t).comp R
  obtain ⟨L,hL⟩ := wordMap_detects_intertwiner H y _ hg
  rw [wordMap_pair_transpose,dotProduct_comm,←polytabloid_action] at hL
  exact ⟨a',b',g.trans t,fun a b => L b a,hL⟩

end Saxl
end
end

end OAI
