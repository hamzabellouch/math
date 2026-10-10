import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.GeneralDetection
import OAI.RepresentationTheory.UniversalSquare.Contraction.PolynomialDetection

namespace OAI

/-! Dual Polytabloid. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl
open scoped MonoidAlgebra

theorem intertwining_extend_injective {G X Y Z : Type*}
    [Group G] [Finite G] [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    {ρ : Representation ℂ G X} {σ : Representation ℂ G Y}
    {τ : Representation ℂ G Z}
    (F : Representation.IntertwiningMap ρ σ) (hF : Function.Injective F)
    (f : Representation.IntertwiningMap ρ τ) :
    ∃ h : Representation.IntertwiningMap σ τ, h.comp F = f := by
  let EF := Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
  let EH := Representation.IntertwiningMap.equivLinearMapAsModule σ τ
  let Ef := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ
  obtain ⟨h, hh⟩ := IsSemisimpleModule.extension_property (EF F) hF (Ef f)
  refine ⟨EH.symm h, ?_⟩
  ext z
  exact LinearMap.congr_fun hh z

lemma cyclic_zero_mem_iff {G X : Type*} [Group G] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ G X) (x : X) : x ∈ cyclic ρ 0 ↔ x = 0 := by
  change x ∈ Submodule.span ℂ (Set.range fun g : G => ρ g 0) ↔ _
  simp

theorem dual_polytabloid_necessary {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation) (hf : f ≠ 0) :
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin (μ.colLen 0) → Fin d → ℂ),
      dotProduct (wordMap L (wordRep n (μ.colLen 0) g (polytabloid t))) u ≠ 0 := by
  let := specht_irreducible t
  have hfi := (Representation.IsIrreducible.injective_or_eq_zero f).resolve_right hf
  let E := (subrepInclusion (cyclic (wordRep n d) u)).comp f
  have hEi : Function.Injective E := Subtype.val_injective.comp hfi
  obtain ⟨R, hR⟩ := intertwining_extend_injective E hEi
    (Representation.IntertwiningMap.id (spechtRep t))
  have hRu : R u ≠ 0 := by
    intro h0
    let p : Specht t := ⟨polytabloid t, mem_cyclic _ _⟩
    have hm := intertwiner_cyclic_mem R u (E p) (f p).property
    rw [h0, cyclic_zero_mem_iff] at hm
    have hi := congrArg (fun H : Representation.IntertwiningMap (spechtRep t)
      (spechtRep t) => H p) hR
    change R (E p) = p at hi
    exact polytabloid_ne_zero t (congrArg Subtype.val (hi.symm.trans hm))
  have hv : (R u).val ≠ 0 := by
    intro hz
    exact hRu (Subtype.ext hz)
  obtain ⟨g, hg⟩ := specht_detect t (R u).property hv
  let F := (subrepInclusion (spechtSub t)).comp R
  have hp : dotProduct (F u)
      (wordRep n (μ.colLen 0) g⁻¹ (polytabloid t)) ≠ 0 := by
    rw [wordPair_move] at hg
    exact hg
  obtain ⟨L,hL⟩ := wordMap_detects_intertwiner F u _ hp
  refine ⟨g⁻¹, fun b a => L a b, ?_⟩
  rw [wordMap_pair_transpose, dotProduct_comm] at hL
  exact hL

theorem specht_to_cyclic_of_vector_pair {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (x : Specht t) (L : Fin (μ.colLen 0) → Fin d → ℂ)
    (u : WordSpace n d)
    (h : dotProduct (wordMap L x.val) u ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, F ≠ 0 := by
  let pr := subrepProject (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
  let F : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) :=
    pr.comp ((wordMap (fun b a => L a b)).comp (subrepInclusion _))
  apply specht_map_back_of_nonzero _ t F
  intro hz
  have hp := subrepProject_pair (spechtSub t)
    (fun _ hx => cyclic_star _ (polytabloid_real t) hx)
    (wordMap (fun b a => L a b) u) x
  have he : pr (wordMap (fun b a => L a b) u) = 0 :=
    congrArg (fun H : Representation.IntertwiningMap
      (cyclic (wordRep n d) u).toRepresentation (spechtRep t) =>
      H ⟨u, mem_cyclic _ _⟩) hz
  rw [he] at hp
  change dotProduct (0 : WordSpace n (μ.colLen 0)) x.val =
    dotProduct (wordMap (fun b a => L a b) u) x.val at hp
  rw [zero_dotProduct] at hp
  rw [wordMap_pair_transpose, dotProduct_comm] at h
  exact h hp.symm

theorem dual_polytabloid_iff {n d : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (u : WordSpace n d) :
    (∃ f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n d) u).toRepresentation, f ≠ 0) ↔
    ∃ (g : Equiv.Perm (Fin n)) (L : Fin (μ.colLen 0) → Fin d → ℂ),
      dotProduct (wordMap L (wordRep n (μ.colLen 0) g (polytabloid t))) u ≠ 0 := by
  constructor
  · rintro ⟨f, hf⟩
    exact dual_polytabloid_necessary t u f hf
  · rintro ⟨g, L, h⟩
    exact specht_to_cyclic_of_vector_pair t
      ⟨wordRep n (μ.colLen 0) g (polytabloid t),
        (spechtSub t).apply_mem_toSubmodule g (mem_cyclic _ _)⟩ L u h

end Saxl
end
end

end OAI
