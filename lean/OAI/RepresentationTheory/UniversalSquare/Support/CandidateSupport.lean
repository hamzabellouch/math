import Mathlib
import OAI.RepresentationTheory.Saxl.Main
import OAI.RepresentationTheory.UniversalSquare.Support.TransposeSupport
import OAI.RepresentationTheory.UniversalSquare.Support.CandidateCut

namespace OAI

/-! Candidate Support. -/

section

noncomputable section
open scoped TensorProduct
namespace Saxl

theorem kronecker_pos_of_tensor_cyclic_support {n : ℕ} {α β μ : YoungDiagram}
    (a a' : Tableau n α) (b b' : Tableau n β) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep n (α.colLen 0 * β.colLen 0))
        (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b'))).toRepresentation)
    (hf : f ≠ 0) : 0 < kronecker a b t := by
  let S := cyclic (wordRep n (α.colLen 0 * β.colLen 0))
    (wordTensor _ _ _ (polytabloid a' ⊗ₜ[ℂ] polytabloid b'))
  let F := @intertwiningLiftSubrep (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  have hF : Function.Injective F := @intertwiningLiftSubrep_injective (Equiv.Perm (Fin n))
    (Specht a ⊗[ℂ] Specht b) (WordSpace n (α.colLen 0 * β.colLen 0))
    _ _ _ _ _ ((spechtRep a).tprod (spechtRep b))
    (wordRep n (α.colLen 0 * β.colLen 0))
    (spechtTensorMap a b) (spechtTensorMap_injective a b)
    S (polytabloidTensor_cyclic_le_range a a' b b')
  apply (kronecker_pos_iff a b t).mpr
  refine ⟨F.comp f, ?_⟩
  intro hz
  apply hf
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have he := congrArg (fun H => H x) hz
  change F (f x) = 0 at he
  change F (f x) = F 0
  simpa only [map_zero] using he

lemma pairWord_mem_alphabetLeft_gen {n a b : ℕ} (A : Fin a → Prop)
    (x : WordSpace n a) (y : WordSpace n b) (hx : x ∈ alphabetSub n a A) :
    wordTensor n a b (x ⊗ₜ[ℂ] y) ∈
      alphabetSub n (a*b) (fun c => A (finProdFinEquiv.symm c).1) := by
  apply (alphabetSub_iff _ _).mpr
  intro w hw i
  rw [wordTensor_tmul] at hw
  exact (alphabetSub_iff A x).mp hx (splitLeft w) (mul_ne_zero_iff.mp hw).1 i

end Saxl
namespace UniversalTensorSquare
open Saxl

theorem kronecker_pos_of_rowColumn_support {n : ℕ} {α μ : YoungDiagram}
    (hα : α.transpose = α) (a a' : Tableau n α) (t : Tableau n μ)
    (f : Representation.IntertwiningMap (spechtRep t) (rowColumnCyclic a').toRepresentation)
    (hf : f ≠ 0) : 0 < kronecker a a t := by
  have hp := kronecker_pos_of_tensor_cyclic_support
    (transposeTableau a) (transposeTableau a') a a' t f hf
  obtain ⟨g,hg⟩ := (kronecker_pos_iff _ _ _).mp hp
  let E := spechtShapeEquiv hα (transposeTableau a) a
  let F := E.toIntertwiningMap.tensor (Representation.IntertwiningMap.id (spechtRep a))
  have hF : Function.Injective F :=
    (TensorProduct.congr E.toLinearEquiv (LinearEquiv.refl ℂ (Specht a))).injective
  apply (kronecker_pos_iff _ _ _).mpr
  refine ⟨F.comp g, ?_⟩
  intro hz
  apply hg
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  apply hF
  have he := congrArg (fun H => H x) hz
  change F (g x) = 0 at he
  change F (g x) = F 0
  simpa only [map_zero] using he

lemma candidateHighLetter_injective (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidateHighLetter M b δ hM) := by
  intro a c hac
  have ha := a.isLt
  have hc := c.isLt
  simp only [staircase_colLen, Nat.sub_zero] at ha hc
  have he := congrArg Fin.val hac
  dsimp [candidateHighLetter] at he
  apply Fin.ext
  split_ifs at he <;> omega

lemma candidateHighMap_injective {n : ℕ} (M b δ : ℕ) (hM : 4 ≤ M) :
    Function.Injective (candidateHighMap (n := n) M b δ hM) := by
  apply pairWordMap_injective
  · apply letterLift_injective
    exact (Fin.cast_injective _).comp (candidateHighLetter_injective M b δ hM)
  · exact letterLift_injective _ (candidateHighLetter_injective M b δ hM)

lemma candidateHighLetter_marked (M b δ : ℕ) (hM : 4 ≤ M)
    (a : Fin ((staircase (M-2)).colLen 0)) :
    candidateMark M b (candidateHighLetter M b δ hM a).val := by
  have ha := a.isLt
  simp only [staircase_colLen, Nat.sub_zero] at ha
  dsimp [candidateMark, candidateHighLetter]
  split_ifs <;> omega

lemma candidateHighWord_alphabet (M b δ : ℕ) (hM : 4 ≤ M) :
    candidateHighWord M b δ hM ∈ alphabetSub _ _
      (fun a => candidateMark M b ((finProdFinEquiv.symm a).1).val) := by
  unfold candidateHighWord candidateHighMap staircaseWord
  rw [pairWordMap_tensor]
  apply pairWord_mem_alphabetLeft_gen (fun a => candidateMark M b a.val)
  apply letterLift_mem_alphabet
  intro a
  exact candidateHighLetter_marked M b δ hM a

lemma candidateBandRow_alphabet {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateBandRow hM t ∈ alphabetSub _ _ (fun a => ¬ candidateMark M b a.val) := by
  apply altWord_mem_alphabet
  intro j
  have hn := candidateCutPositions_high t ((candidateCutPositions t).symm (Sum.inr j))
  simp only [Equiv.apply_symm_apply, Sum.isLeft_inr, Bool.false_eq_true, false_iff] at hn
  have hr := candidateRotateRow_mark M b δ hM (candidateBandTableau t j)
  have hh : ¬candidateMark M b (candidateRotateRow M b δ hM (candidateBandTableau t j)).val.2 :=
    fun hh => hn (hr.mp hh)
  simpa [rightWord, rowWord, transposeTableau, candidateRotateRowPositions, candidateBandTableau]
    using hh

lemma candidateBandWord_alphabet {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    candidateBandWord hM t ∈ alphabetSub _ _
      (fun a => ¬candidateMark M b ((finProdFinEquiv.symm a).1).val) := by
  exact pairWord_mem_alphabetLeft_gen (fun a => ¬candidateMark M b a.val) _ _
    (candidateBandRow_alphabet hM t)

lemma candidateBandWord_ne_zero {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) : candidateBandWord hM t ≠ 0 := by
  intro hz
  apply candidate_projected_ne_zero hM t
  rw [candidate_cut_factor hM t, hz]
  ext w
  change _ * 0 = 0
  exact mul_zero _

theorem candidateHighWord_support (M b δ : ℕ) (hM : 4 ≤ M)
    (μ : YoungDiagram) (t : Tableau (staircase (M-2)).card μ) :
    ∃ F : Representation.IntertwiningMap (spechtRep t)
      (cyclic (wordRep _ _) (candidateHighWord M b δ hM)).toRepresentation, F ≠ 0 := by
  obtain ⟨f,hf⟩ := full_cyclic_support (M-2) (by omega) μ t
  exact cyclic_support_map (candidateHighMap M b δ hM)
    (candidateHighMap_injective M b δ hM) (staircaseWord (M-2)) f hf

theorem candidate_triangle_quotient {n M b δ : ℕ} (hM : 4 ≤ M)
    (t : Tableau n (candidate M b δ)) :
    ∃ F : Representation.IntertwiningMap (rowColumnCyclic t).toRepresentation
      (cyclic (wordRep _ _)
        (positionProduct (candidateCutPositions t) (candidateHighWord M b δ hM)
          (candidateBandWord hM t))).toRepresentation, Function.Surjective F := by
  rw [← candidate_cut_factor hM t]
  exact ⟨cyclicMap (sameMarkProjection _ _ _ (candidateMark M b)) (rowColumnWord t),
    cyclicMap_surjective _ _⟩

theorem candidate_cut_strip_support {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ))
    (ν μ : YoungDiagram) (hν : ν.card = (staircase (M-2)).card)
    (t : Tableau n μ) (bs : List ℕ) (hs : SizedStripChain bs ν μ)
    (hband : ∀ (η : YoungDiagram) (r : Tableau (candidateBandSize a) η),
      η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation, F ≠ 0) :
    ∃ F : Representation.IntertwiningMap (spechtRep t) (rowColumnCyclic a).toRepresentation,
      F ≠ 0 := by
  obtain ⟨f,hf⟩ := candidateHighWord_support M b δ hM ν (canonicalTableau ν hν)
  have H := strip_product_support hs (canonicalTableau ν hν) t (candidateCutPositions a)
    (candidateHighWord M b δ hM) (candidateBandWord hM a)
    (fun α => candidateMark M b ((finProdFinEquiv.symm α).1).val)
    (candidateHighWord_alphabet M b δ hM) (candidateBandWord_alphabet hM a) f hf hband
  rw [← candidate_cut_factor hM a] at H
  obtain ⟨F,hF⟩ := H
  exact cyclic_projection_support (sameMarkProjection _ _ _ (candidateMark M b))
    (rowColumnWord a) F hF

theorem candidate_kronecker_pos_of_strip_band {n M b δ : ℕ} (hM : 4 ≤ M)
    (a : Tableau n (candidate M b δ))
    (ν μ : YoungDiagram) (hν : ν.card = (staircase (M-2)).card)
    (t : Tableau n μ) (bs : List ℕ) (hs : SizedStripChain bs ν μ)
    (hband : ∀ (η : YoungDiagram) (r : Tableau (candidateBandSize a) η),
      η.colLen 0 ≤ bs.length →
      ∃ F : Representation.IntertwiningMap (spechtRep r)
        (cyclic (wordRep _ _) (candidateBandWord hM a)).toRepresentation, F ≠ 0) :
    0 < kronecker a a t := by
  obtain ⟨F,hF⟩ := candidate_cut_strip_support hM a ν μ hν t bs hs hband
  exact kronecker_pos_of_rowColumn_support (candidate_transpose M b δ) a a t F hF

end UniversalTensorSquare
end
end

end OAI
