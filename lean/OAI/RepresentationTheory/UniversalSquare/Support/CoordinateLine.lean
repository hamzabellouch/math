import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Contraction.SquareDetection

namespace OAI

/-! Coordinate Line. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

def coordinateRestriction {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) : Module.Dual ℂ (Specht t) :=
  { toFun := fun x => x.val a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

def projectedCoordinate {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) : Specht t :=
  (spechtSelfDual t).symm (coordinateRestriction t a)

lemma projectedCoordinate_pair {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0)) (x : Specht t) :
    dotProduct (projectedCoordinate t a).val x.val = x.val a := by
  exact congrArg (fun f : Module.Dual ℂ (Specht t) => f x)
    ((spechtSelfDual t).apply_symm_apply (coordinateRestriction t a))

lemma projectedCoordinate_nonzero {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ) :
    projectedCoordinate t (rowWord s) ≠ 0 := by
  intro hz
  have h := projectedCoordinate_pair t (rowWord s)
    ⟨polytabloid s, polytabloid_mem_all t s⟩
  rw [hz] at h
  have h0 : (0 : ℂ) = 1 := by
    simpa only [ZeroMemClass.coe_zero, zero_dotProduct, polytabloid_rowWord] using h
  exact zero_ne_one h0

lemma coordinateRestriction_nonzero {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ) :
    coordinateRestriction t (rowWord s) ≠ 0 := by
  intro hz
  apply projectedCoordinate_nonzero t s
  simp only [projectedCoordinate, hz, map_zero]

lemma coordinateRestriction_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    (spechtRep t).dual g.val (coordinateRestriction t (rowWord s)) =
      coordinateRestriction t (rowWord s) := by
  ext x
  change x.val (rowWord s ∘ ((g.val)⁻¹ : Equiv.Perm (Fin n))) = x.val (rowWord s)
  apply congrArg x.val
  funext i
  apply Fin.ext
  exact g⁻¹.property i

lemma projectedCoordinate_fixed {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (g : columnGroup (transposeTableau s)) :
    spechtRep t g.val (projectedCoordinate t (rowWord s)) =
      projectedCoordinate t (rowWord s) := by
  have h := LinearMap.congr_fun ((spechtSelfDual t).symm.isIntertwining' g.val)
    (coordinateRestriction t (rowWord s))
  simp only [LinearMap.comp_apply] at h
  rw [coordinateRestriction_fixed] at h
  exact h.symm

theorem signEquiv_coordinate_line {n : ℕ} {μ : YoungDiagram} (t s : Tableau n μ)
    (φ : (spechtRep t).Equiv (signTwist (spechtRep (transposeTableau t)))) :
    ∃ c : ℂ, c ≠ 0 ∧ (φ (projectedCoordinate t (rowWord s))).val =
      c • polytabloid (transposeTableau s) := by
  let y : Specht (transposeTableau s) :=
    ⟨(φ (projectedCoordinate t (rowWord s))).val,
      by change _ ∈ (spechtSub (transposeTableau s)).toSubmodule
         rw [← spechtSub_tableau_independent (transposeTableau t) (transposeTableau s)]
         exact (φ (projectedCoordinate t (rowWord s))).property⟩
  have ha (g : columnGroup (transposeTableau s)) :
      spechtRep (transposeTableau s) g.val y = signC g.val • y := by
    have he := LinearMap.congr_fun (φ.isIntertwining' g.val)
      (projectedCoordinate t (rowWord s))
    change φ (spechtRep t g.val (projectedCoordinate t (rowWord s))) =
      signC g.val • spechtRep (transposeTableau t) g.val
        (φ (projectedCoordinate t (rowWord s))) at he
    rw [projectedCoordinate_fixed] at he
    have hh := congrArg (fun x => signC g.val • x.val) he
    change signC g.val • (φ (projectedCoordinate t (rowWord s))).val =
      signC g.val • (signC g.val • wordRep _ _ g.val
        (φ (projectedCoordinate t (rowWord s))).val) at hh
    apply Subtype.ext
    change wordRep _ _ g.val (φ (projectedCoordinate t (rowWord s))).val =
      signC g.val • (φ (projectedCoordinate t (rowWord s))).val
    simpa only [Submodule.coe_smul_of_tower, smul_smul, signC_mul_self, one_smul]
      using hh.symm
  obtain ⟨c,hc⟩ := alternating_specht_line (transposeTableau s) y ha
  refine ⟨c, ?_, hc⟩
  intro hz
  rw [hz, zero_smul] at hc
  apply projectedCoordinate_nonzero t s
  apply φ.injective
  exact (Subtype.ext hc).trans (map_zero φ).symm

lemma exists_tableau_of_row_content {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin (μ.colLen 0))
    (ha : ∀ j, (Finset.univ.filter (fun i => a i = j)).card = μ.rowLen j.val) :
    ∃ s : Tableau n μ, rowWord s = a := by
  obtain ⟨g,hg⟩ := perm_of_equal_content a (rowWord t)
    (fun j => (ha j).trans (rowWord_content t j).symm)
  exact ⟨g.trans t, hg⟩

theorem coordinateRestriction_ne_zero_of_content {n : ℕ} {μ : YoungDiagram}
    (t : Tableau n μ) (a : Fin n → Fin (μ.colLen 0))
    (ha : ∀ j, (Finset.univ.filter (fun i => a i = j)).card = μ.rowLen j.val) :
    coordinateRestriction t a ≠ 0 := by
  obtain ⟨s, rfl⟩ := exists_tableau_of_row_content t a ha
  exact coordinateRestriction_nonzero t s

end Saxl
end
end

end OAI
