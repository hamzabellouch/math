import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.RowCertificates

namespace OAI

/-! Young Converse. -/

section

noncomputable section
namespace Saxl
open scoped BigOperators

lemma rowPrefix_eq_count {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : ℕ) :
    rowPrefix μ k = (Finset.univ.filter (fun i => (t i).val.1 < k)).card := by
  classical
  rw [← rowTruncate_card]
  change (μ.cells.filter (fun c => c.1 < k)).card = _
  conv_lhs => rw [← tableau_image t]
  rw [Finset.filter_image, Finset.card_image_iff.mpr]
  intro i hi j hj h
  exact t.injective (Subtype.val_injective h)

lemma rowPrefix_eq_sum_indicator {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) (k : ℕ) :
    (rowPrefix μ k : ℤ) = ∑ i, if (t i).val.1 < k then (1 : ℤ) else 0 := by
  classical
  simp only [rowPrefix_eq_count t k, Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

theorem dominates_of_mixed {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν) (g : Equiv.Perm (Fin n))
    (hi : Function.Injective (fun i => ((u (g i)).val.1, (t i).val.2))) :
    Dominates μ ν := by
  classical
  intro k
  let f : Fin n → ℕ × ℕ := fun i => ((u (g i)).val.1, (t i).val.2)
  let w : ℕ × ℕ → ℤ := fun c => (if c.1 < k then 1 else 0) -
    (if μ.colLen c.2 < k then 1 else 0)
  have h := finset_signed_sum_le (Finset.univ.image f) μ.cells w
    (fun c hc => by
      have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
      dsimp only [w]
      split_ifs <;> omega)
    (fun c hc => by
      have hh : μ.colLen c.2 ≤ c.1 :=
        le_of_not_gt (fun h => hc (YoungDiagram.mem_iff_lt_colLen.mpr h))
      dsimp only [w]
      split_ifs <;> omega)
  rw [Finset.sum_image (fun _ _ _ _ h => hi h), ← tableau_sum t w] at h
  simp only [w, Finset.sum_sub_distrib] at h
  rw [Equiv.sum_comp g (fun i => if (u i).val.1 < k then (1 : ℤ) else 0),
    ← rowPrefix_eq_sum_indicator u k, ← rowPrefix_eq_sum_indicator t k] at h
  have hh : (rowPrefix ν k : ℤ) ≤ rowPrefix μ k := by omega
  exact_mod_cast hh

theorem dominates_of_tabloid_hom {n : ℕ} {μ ν : YoungDiagram}
    (t : Tableau n μ) (u : Tableau n ν)
    (f : Representation.IntertwiningMap (spechtRep t) (tabloidSub u).toRepresentation)
    (hf : f ≠ 0) : Dominates μ ν := by
  let := specht_irreducible t
  have hi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
  have hz : columnAlt t (f p).val ≠ 0 := by
    intro hz
    have he := columnOperator_intertwining t f p
    have hy : columnOperator t (tabloidSub u).toRepresentation (f p) = 0 := by
      apply Subtype.ext
      exact (columnOperator_subtype t (tabloidSub u) (f p)).trans hz
    rw [hy] at he
    have ht : columnOperator t (spechtRep t) p = 0 := hi (he.trans (map_zero f).symm)
    exact columnAlt_polytabloid_ne_zero t
      ((columnOperator_subtype t (spechtSub t) p).symm.trans (congrArg Subtype.val ht))
  obtain ⟨g,hg⟩ := mixed_injective_of_columnAlt_ne_zero t u (f p).property hz
  exact dominates_of_mixed t u g hg

theorem tabloid_supportLE {n : ℕ} {θ : YoungDiagram} (u : Tableau n θ)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Equiv.Perm (Fin n)) V)
    (h : ∀ (μ : YoungDiagram) (t : Tableau n μ), Dominates μ θ →
      ∃ f : Representation.IntertwiningMap (spechtRep t) σ, f ≠ 0) :
    SupportLE (tabloidSub u).toRepresentation σ := by
  apply intertwining_separates_of_simple_support
  intro S hS
  let := hS
  let : AddCommGroup S.toSubmodule := Module.addCommMonoidToAddCommGroup ℂ
  obtain ⟨p, ⟨e⟩⟩ := irreducible_equiv_specht S.toRepresentation
  let t := partitionTableau p
  let i : Representation.IntertwiningMap (spechtRep t) (tabloidSub u).toRepresentation :=
    (subrepInclusion S).comp e.symm.toIntertwiningMap
  have hi : i ≠ 0 := by
    intro he
    have hz := congrArg (fun F : Representation.IntertwiningMap (spechtRep t)
      (tabloidSub u).toRepresentation => F ⟨polytabloid t, mem_cyclic _ _⟩) he
    have h0 : e.symm ⟨polytabloid t, mem_cyclic _ _⟩ = 0 := Subtype.ext hz
    have h1 := e.symm.injective (h0.trans e.symm.toLinearEquiv.map_zero.symm)
    exact polytabloid_ne_zero t (congrArg Subtype.val h1)
  obtain ⟨f,hf⟩ := h _ t (dominates_of_tabloid_hom t u i hi)
  refine ⟨f.comp e.toIntertwiningMap, ?_⟩
  intro he
  apply hf
  ext y
  obtain ⟨z,rfl⟩ := e.surjective y
  exact congrArg (fun F : Representation.IntertwiningMap S.toRepresentation σ => F z) he

end Saxl
end
end

end OAI
